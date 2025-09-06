"""
Gestionnaire de cours simple (Python + Tkinter)
Fichier: main.py
Fonctionnalités :
- Ajouter / éditer / supprimer des cours (matière, description, professeur, date d'échéance)
- Ajouter des ressources (fichiers Word, PDF, images...) liées à un cours
- Ouvrir une ressource avec l'application par défaut du système
- Recherche / filtrage par nom de cours
- Sauvegarde automatique dans une base SQLite locale (courses.db)
- Import / export JSON pour partage

Améliorations :
- Copie des fichiers ajoutés dans la base SQLite (champ BLOB) compressés avec gzip
- Migration automatique du schéma (ajout des colonnes si l'ancienne table existait)
- Lors de l'ouverture d'une ressource, extraction depuis la base dans un fichier temporaire puis ouverture
- Vérification automatique des mises à jour à chaque lancement (URL configurable)

Usage : si vous possedez cette version veuillez la compiler avec pyinstaller :
    pyinstaller --onefile --windowed main.py
Dépendances : Python 3 (builtin: tkinter, sqlite3, gzip). Optionnel : tkcalendar pour un sélecteur de date plus pratique
    pip install tkcalendar

Auteur : Généré par l'assistant (modifié pour stocker les fichiers compressés dans la DB)
"""

import os
import sys
import json
import sqlite3
import datetime
import platform
import subprocess
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import gzip
import tempfile
import threading
import urllib.request
import urllib.error
import webbrowser
import hashlib
import shutil
import zipfile
import time

# Version locale de l'application
CURRENT_VERSION = '2.0'
# URL fournie (vérifiée à chaque lancement)
UPDATE_URL = 'https://raw.githubusercontent.com/lolo34dr/OrganiseTesCours/refs/heads/main/version.json'
AUTO_APPLY_UPDATE = False

USE_TKCALENDAR = False
try:
    from tkcalendar import DateEntry
    USE_TKCALENDAR = True
except Exception:
    DateEntry = None

DB_FILE = 'courses.db'

def init_db():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute('''
        CREATE TABLE IF NOT EXISTS courses (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            teacher TEXT,
            description TEXT,
            due_date TEXT,
            done INTEGER DEFAULT 0
        )
    ''')
    c.execute('''
        CREATE TABLE IF NOT EXISTS resources (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            course_id INTEGER,
            path TEXT,
            note TEXT
        )
    ''')
    conn.commit()
    migrate_resources_table(conn)
    return conn

def migrate_resources_table(conn):
    c = conn.cursor()
    info = c.execute("PRAGMA table_info(resources)").fetchall()
    cols = [row[1] for row in info]
    changed = False
    if 'filename' not in cols:
        try:
            c.execute("ALTER TABLE resources ADD COLUMN filename TEXT")
            changed = True
        except Exception:
            pass
    if 'data' not in cols:
        try:
            c.execute("ALTER TABLE resources ADD COLUMN data BLOB")
            changed = True
        except Exception:
            pass
    if changed:
        conn.commit()

    try:
        rows = c.execute("SELECT id, path FROM resources WHERE data IS NULL").fetchall()
        for rid, path in rows:
            if path and os.path.exists(path) and os.path.isfile(path):
                try:
                    with open(path, 'rb') as f:
                        raw = f.read()
                    comp = gzip.compress(raw)
                    filename = os.path.basename(path)
                    c.execute("UPDATE resources SET filename=?, data=? WHERE id=?", (filename, sqlite3.Binary(comp), rid))
                except Exception:
                    pass
        conn.commit()
    except Exception:
        pass

def open_file_with_default(path):
    if not os.path.exists(path):
        raise FileNotFoundError(path)
    system = platform.system()
    if system == 'Windows':
        os.startfile(path)
    elif system == 'Darwin':
        subprocess.run(['open', path])
    else:
        subprocess.run(['xdg-open', path])

# --- update check helpers ---

def _sha256_of_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(8192), b''):
            h.update(chunk)
    return h.hexdigest()


def _download_to_temp(url, timeout=30):
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'OrganiseTesCours-Updater/1.0'})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            # déterminer extension si possible
            ct = resp.headers.get('Content-Type', '').lower()
            data = resp.read()
            # nom temporaire
            suffix = ''
            if url.lower().endswith('.zip'):
                suffix = '.zip'
            elif url.lower().endswith('.exe'):
                suffix = '.exe'
            elif url.lower().endswith('.py'):
                suffix = '.py'
            # write temp
            tmpf = tempfile.NamedTemporaryFile(delete=False, suffix=suffix)
            tmpf.write(data)
            tmpf.flush()
            tmpf.close()
            return tmpf.name
    except Exception as e:
        return None
    
def _apply_update_file(downloaded_path, expected_sha256=None, restart=True):
    """
    downloaded_path: chemin du fichier téléchargé (peut être .py, .zip, .exe).
    expected_sha256: hex string ou None.
    restart: si True, redémarre l'application après remplacement.
    Retourne True si appliqué avec succès.
    """
    try:
        if expected_sha256:
            got = _sha256_of_file(downloaded_path)
            if got.lower() != expected_sha256.lower():
                # checksum mismatch
                return False, f"SHA256 mismatch (got {got})"

        # déterminer cible : si script non compilé -> remplacer le fichier courant (sys.argv[0])
        running_exec = os.path.abspath(sys.argv[0])  # script courant (main.py)
        running_binary = os.path.abspath(sys.executable)  # interpréteur ou exe compilé

        # CASE 1 : ZIP -> extraire les fichiers à la racine du projet (écrase les fichiers existants after backup)
        if zipfile.is_zipfile(downloaded_path):
            # sauvegarde : create backup dir with timestamp
            backup_dir = os.path.join(os.path.dirname(running_exec), f'backup_{int(time.time())}')
            os.makedirs(backup_dir, exist_ok=True)
            # copy current files that will be overwritten: we will extract zip and overwrite files; backup all files in zip if exist
            with zipfile.ZipFile(downloaded_path, 'r') as z:
                for member in z.namelist():
                    target = os.path.join(os.path.dirname(running_exec), member)
                    if os.path.exists(target):
                        # make sure subdirs exist in backup
                        destbackup = os.path.join(backup_dir, member)
                        os.makedirs(os.path.dirname(destbackup), exist_ok=True)
                        shutil.copy2(target, destbackup)
                # extract all (overwrite)
                z.extractall(os.path.dirname(running_exec))
            # done
            applied = True

        else:
            # single file (py or exe)
            # if the downloaded file is an exe and current process is an exe (pyinstaller), replace executable
            downloaded_name = os.path.basename(downloaded_path)
            if downloaded_name.lower().endswith('.exe') and os.path.basename(running_binary).lower().endswith('.exe') and running_binary != sys.executable:
                # try to replace the running executable
                target_bin = running_binary
                backup_bin = target_bin + f'.bak_{int(time.time())}'
                try:
                    shutil.copy2(target_bin, backup_bin)
                except Exception:
                    pass
                try:
                    # On Windows, replacing running exe may fail; try move after process exits.
                    # We'll write the new exe next to current and schedule replacement on restart.
                    shutil.copy2(downloaded_path, target_bin)
                    applied = True
                except Exception as e:
                    # fallback: write next to it and notify manual replace
                    alt = target_bin + '.new'
                    shutil.copy2(downloaded_path, alt)
                    return False, f"Impossible d'écraser l'exécutable en cours. Nouveau fichier écrit : {alt}"
            else:
                # assume replace script file (main.py)
                target_script = running_exec
                backup_script = target_script + f'.bak_{int(time.time())}'
                try:
                    shutil.copy2(target_script, backup_script)
                except Exception:
                    pass
                try:
                    shutil.copy2(downloaded_path, target_script)
                    applied = True
                except Exception as e:
                    return False, f"Erreur écriture fichier : {e}"

        # nettoyage du temp
        try:
            os.remove(downloaded_path)
        except Exception:
            pass

        if applied and restart:
            try:
                # redémarrage : relancer python avec mêmes arguments
                python = sys.executable
                os.execv(python, [python] + sys.argv)
            except Exception:
                # si execv échoue, on renvoie True quand même (mise à jour appliquée)
                return True, "Mise à jour appliquée (redémarrage automatique échoué). Relance manuelle requise."
        return True, "Mise à jour appliquée"
    except Exception as e:
        return False, str(e)
    
def _notify_update_on_ui(root, remote_info):
    """
    Améliorée : propose 'Ouvrir la page', 'Mettre à jour maintenant' ou 'Plus tard'.
    Si AUTO_APPLY_UPDATE=True -> télécharge et applique automatiquement.
    """
    # normalisation
    if remote_info is None:
        return
    if isinstance(remote_info, (int, float, str)):
        remote_info = {'version': str(remote_info)}
    if not isinstance(remote_info, dict):
        return
    if 'version' not in remote_info:
        for k in ('ver','v','release'):
            if k in remote_info:
                remote_info['version'] = remote_info[k]
                break
    if 'version' not in remote_info:
        return

    remote_ver = str(remote_info.get('version'))
    if not remote_ver:
        return
    try:
        cmp = _compare_versions(CURRENT_VERSION, remote_ver)
    except Exception:
        cmp = -1
    if cmp >= 0:
        return

    changelog = remote_info.get('changelog') or remote_info.get('notes') or ''
    download = remote_info.get('download_url') or remote_info.get('url') or remote_info.get('html_url')
    expected_sha = remote_info.get('sha256')

    msg = f"Nouvelle version disponible : {remote_ver}\\nVotre version : {CURRENT_VERSION}\\n\\n"
    if changelog:
        msg += f"Changelog :\\n{changelog}\\n\\n"
    msg += "Que voulez-vous faire ?"

    def ask_user():
        try:
            # Si AUTO_APPLY_UPDATE activé -> lancer update direct en thread
            if AUTO_APPLY_UPDATE and download:
                if messagebox.askyesno('Mise à jour automatique', f"Version {remote_ver} disponible. Appliquer maintenant ? (AUTO_APPLY_UPDATE activé)"):
                    # lancer update dans un thread
                    def worker_update():
                        tmp = _download_to_temp(download)
                        if not tmp:
                            root.after(100, lambda: messagebox.showerror('Erreur', 'Téléchargement de la mise à jour échoué')) 
                            return
                        ok, info = _apply_update_file(tmp, expected_sha256=expected_sha, restart=True)
                        if not ok:
                            root.after(100, lambda: messagebox.showerror('Erreur mise à jour', info))
                    threading.Thread(target=worker_update, daemon=True).start()
                return

            # sinon proposer choix
            choice = messagebox.askquestion('Mise à jour disponible', msg, icon='info')
            # messagebox.askquestion renvoie 'yes'/'no'. On veut proposer 3 choix ->
            # on fait une nouvelle fenêtre custom si on veut 3 boutons. Simpler: yes -> Update now, no -> Open page
            if choice == 'yes':
                if not download:
                    messagebox.showinfo('Info', 'Aucun lien de téléchargement fourni. Ouverture de la page si disponible.')
                    if remote_info.get('html_url'):
                        webbrowser.open(remote_info.get('html_url'))
                    return
                # start background update
                def worker_update2():
                    tmp = _download_to_temp(download)
                    if not tmp:
                        root.after(100, lambda: messagebox.showerror('Erreur', 'Téléchargement de la mise à jour échoué'))
                        return
                    ok, info = _apply_update_file(tmp, expected_sha256=expected_sha, restart=True)
                    if not ok:
                        root.after(100, lambda: messagebox.showerror('Erreur mise à jour', info))
                threading.Thread(target=worker_update2, daemon=True).start()
            else:
                # 'no' -> ouvrir page de téléchargement si disponible
                if download:
                    try:
                        webbrowser.open(download)
                    except Exception:
                        messagebox.showinfo('Info', f'Ouvrez manuellement : {download}')
                else:
                    messagebox.showinfo('Info', 'Aucun lien de téléchargement fourni.')
        except Exception:
            pass

    root.after(100, ask_user)

def _compare_versions(a, b):
    """Compare semantic-like versions 'a' and 'b'.
    Retourne : -1 si a<b, 0 si égal, 1 si a>b
    """
    try:
        pa = [int(x) for x in str(a).split('.') if x.isdigit()]
        pb = [int(x) for x in str(b).split('.') if x.isdigit()]
    except Exception:
        # fallback simple
        if str(a) == str(b):
            return 0
        return -1
    # comparer longueur
    n = max(len(pa), len(pb))
    pa += [0] * (n - len(pa))
    pb += [0] * (n - len(pb))
    for i in range(n):
        if pa[i] < pb[i]:
            return -1
        elif pa[i] > pb[i]:
            return 1
    return 0


def _fetch_update_info(url, timeout=6):
    """
    Récupère le JSON depuis `url`.
    Si le JSON est un objet -> retourne le dict.
    Si le JSON est une valeur simple (ex: "1.1" ou 1.1) -> retourne {'version': '1.1'}.
    Retourne None en cas d'erreur réseau / parse.
    """
    req = urllib.request.Request(url, headers={'User-Agent': 'OrganiseTesCours-Updater/1.0'})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read()
            # essayer de décoder en utf-8, puis loader JSON
            try:
                parsed = json.loads(raw.decode('utf-8'))
            except Exception:
                return None

            # Si le JSON est un dict, renvoyer tel quel
            if isinstance(parsed, dict):
                return parsed
            # Si c'est une valeur simple (float/int/str), normaliser en dict contenant 'version'
            if isinstance(parsed, (int, float, str)):
                return {'version': str(parsed)}
            # Si c'est une liste ou autre, on ignore (mais on peut essayer la première valeur)
            if isinstance(parsed, list) and len(parsed) > 0:
                first = parsed[0]
                if isinstance(first, dict):
                    return first
                if isinstance(first, (int, float, str)):
                    return {'version': str(first)}
            return None
    except Exception:
        # network / timeout / parsing -> on ignore silencieusement (retour None)
        return None


def start_update_check(root):
    # lancer la vérification dans un thread séparé pour ne pas bloquer l'UI
    def worker():
        info = _fetch_update_info(UPDATE_URL)
        if info:
            # notifier sur l'UI thread
            _notify_update_on_ui(root, info)
    t = threading.Thread(target=worker, daemon=True)
    t.start()


class CourseManagerApp(tk.Tk):
    def __init__(self, conn):
        super().__init__()
        self.conn = conn
        self.title('OrganiseTesCours | Version beta test')
        self.geometry('1100x650')
        self.minsize(800, 480)
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        self.create_widgets()
        self.load_courses()
        self.bind('<Configure>', self.on_root_resize)

        # démarrer la vérification de mise à jour à chaque lancement
        try:
            start_update_check(self)
        except Exception:
            # si la vérification échoue, on l'ignore (pas critique)
            pass

    # ... le reste de la classe est identique à la version précédente (fonctions CRUD, import/export, etc.)
    # pour des raisons de lisibilité dans le canevas, le code complet suit ci-dessous.

    def create_widgets(self):
        top_frame = ttk.Frame(self)
        top_frame.grid(row=0, column=0, sticky='ew', padx=8, pady=6)
        top_frame.columnconfigure(1, weight=1)

        ttk.Label(top_frame, text='Recherche :').grid(row=0, column=0, sticky='w')
        self.search_var = tk.StringVar()
        search_entry = ttk.Entry(top_frame, textvariable=self.search_var)
        search_entry.grid(row=0, column=1, sticky='ew', padx=6)
        search_entry.bind('<KeyRelease>', lambda e: self.load_courses())

        btns = ttk.Frame(top_frame)
        btns.grid(row=0, column=2, sticky='e')
        ttk.Button(btns, text='Ajouter un cours', command=self.add_course_dialog).pack(side='left', padx=6)
        ttk.Button(btns, text='Importer (JSON)', command=self.import_json).pack(side='left', padx=6)
        ttk.Button(btns, text='Exporter (JSON)', command=self.export_json).pack(side='left', padx=6)

        paned = ttk.Panedwindow(self, orient='horizontal')
        paned.grid(row=1, column=0, sticky='nsew', padx=8, pady=6)
        self.rowconfigure(1, weight=1)

        left_frame = ttk.Frame(paned)
        left_frame.columnconfigure(0, weight=1)
        left_frame.rowconfigure(0, weight=1)
        paned.add(left_frame, weight=1)

        self.tree = ttk.Treeview(left_frame, columns=('teacher', 'due', 'done'), show='tree headings', selectmode='browse')
        self.tree.heading('#0', text='Nom')
        self.tree.heading('teacher', text='Professeur')
        self.tree.heading('due', text='Échéance')
        self.tree.heading('done', text='Fait')
        self.tree.column('#0', anchor='w')
        self.tree.column('teacher', anchor='w')
        self.tree.column('due', width=120, anchor='center')
        self.tree.column('done', width=60, anchor='center')
        self.tree.grid(row=0, column=0, sticky='nsew')
        self.tree.bind('<<TreeviewSelect>>', lambda e: self.on_course_select())

        vsb = ttk.Scrollbar(left_frame, orient='vertical', command=self.tree.yview)
        vsb.grid(row=0, column=1, sticky='ns')
        self.tree.configure(yscrollcommand=vsb.set)

        right_frame = ttk.Frame(paned)
        right_frame.columnconfigure(0, weight=1)
        right_frame.rowconfigure(1, weight=1)
        paned.add(right_frame, weight=3)

        details = ttk.LabelFrame(right_frame, text='Détails du cours')
        details.grid(row=0, column=0, sticky='ew', padx=6, pady=6)
        details.columnconfigure(1, weight=1)
        details.rowconfigure(2, weight=1)

        self.name_var = tk.StringVar()
        self.teacher_var = tk.StringVar()
        self.description_text = tk.Text(details, height=6)

        ttk.Label(details, text='Nom :').grid(row=0, column=0, sticky='w', padx=4, pady=2)
        ttk.Entry(details, textvariable=self.name_var).grid(row=0, column=1, sticky='ew', padx=4, pady=2)
        ttk.Label(details, text='Professeur :').grid(row=1, column=0, sticky='w', padx=4, pady=2)
        ttk.Entry(details, textvariable=self.teacher_var).grid(row=1, column=1, sticky='ew', padx=4, pady=2)

        ttk.Label(details, text='Description :').grid(row=2, column=0, sticky='nw', padx=4, pady=2)
        self.description_text.grid(row=2, column=1, sticky='nsew', padx=4, pady=2)

        ttk.Label(details, text='Échéance (YYYY-MM-DD) :').grid(row=3, column=0, sticky='w', padx=4, pady=2)
        if USE_TKCALENDAR:
            self.due_widget = DateEntry(details, date_pattern='yyyy-mm-dd')
        else:
            self.due_var = tk.StringVar()
            self.due_widget = ttk.Entry(details, textvariable=self.due_var)
        self.due_widget.grid(row=3, column=1, sticky='w', padx=4, pady=2)

        btn_frame = ttk.Frame(details)
        btn_frame.grid(row=4, column=0, columnspan=2, sticky='e', pady=6)
        ttk.Button(btn_frame, text='Enregistrer', command=self.save_current_course).pack(side='left', padx=4)
        ttk.Button(btn_frame, text='Supprimer', command=self.delete_current_course).pack(side='left', padx=4)
        ttk.Button(btn_frame, text='Marquer comme fait', command=self.toggle_done).pack(side='left', padx=4)

        res_frame = ttk.LabelFrame(right_frame, text='Ressources liées')
        res_frame.grid(row=1, column=0, sticky='nsew', padx=6, pady=6)
        res_frame.columnconfigure(0, weight=1)
        res_frame.rowconfigure(0, weight=1)

        self.res_tree = ttk.Treeview(res_frame, columns=('path','note'), show='headings', selectmode='browse')
        self.res_tree.heading('path', text='Fichier')
        self.res_tree.heading('note', text='Note')
        self.res_tree.column('path', anchor='w')
        self.res_tree.column('note', anchor='w')
        self.res_tree.grid(row=0, column=0, sticky='nsew')

        res_vsb = ttk.Scrollbar(res_frame, orient='vertical', command=self.res_tree.yview)
        res_vsb.grid(row=0, column=1, sticky='ns')
        self.res_tree.configure(yscrollcommand=res_vsb.set)

        rbtn_frame = ttk.Frame(res_frame)
        rbtn_frame.grid(row=2, column=0, sticky='ew', pady=6)
        ttk.Button(rbtn_frame, text='Ajouter fichier', command=self.add_resource).pack(side='left', padx=4)
        ttk.Button(rbtn_frame, text='Ouvrir', command=self.open_selected_resource).pack(side='left', padx=4)
        ttk.Button(rbtn_frame, text='Supprimer ressource', command=self.delete_selected_resource).pack(side='left', padx=4)

        self.status_var = tk.StringVar()
        status = ttk.Label(self, textvariable=self.status_var, relief='sunken', anchor='w')
        status.grid(row=2, column=0, sticky='ew')

    def load_courses(self):
        q = self.search_var.get().strip()
        c = self.conn.cursor()
        if q:
            c.execute("SELECT id, name, teacher, due_date, done FROM courses WHERE name LIKE ? OR teacher LIKE ? ORDER BY due_date IS NULL, due_date", (f'%{q}%', f'%{q}%'))
        else:
            c.execute("SELECT id, name, teacher, due_date, done FROM courses ORDER BY due_date IS NULL, due_date")
        rows = c.fetchall()
        for item in self.tree.get_children():
            self.tree.delete(item)
        for r in rows:
            _id, name, teacher, due, done = r
            due_display = due if due else ''
            done_display = '✅' if done else ''
            self.tree.insert('', 'end', iid=str(_id), text=name, values=(teacher, due_display, done_display))
        self.status_var.set(f'{len(rows)} cours chargés')
        self.after(50, self.adjust_columns)

    def on_course_select(self):
        sel = self.tree.selection()
        if not sel:
            return
        course_id = int(sel[0])
        c = self.conn.cursor()
        c.execute('SELECT name, teacher, description, due_date, done FROM courses WHERE id=?', (course_id,))
        row = c.fetchone()
        if not row:
            return
        name, teacher, desc, due, done = row
        self.current_course_id = course_id
        self.name_var.set(name)
        self.teacher_var.set(teacher or '')
        self.description_text.delete('1.0', 'end')
        self.description_text.insert('1.0', desc or '')
        if USE_TKCALENDAR:
            if due:
                try:
                    dt = datetime.datetime.strptime(due, '%Y-%m-%d').date()
                    self.due_widget.set_date(dt)
                except Exception:
                    pass
            else:
                self.due_widget.set_date(datetime.date.today())
        else:
            self.due_var.set(due or '')
        self.load_resources(course_id)

    def load_resources(self, course_id):
        c = self.conn.cursor()
        c.execute('SELECT id, COALESCE(filename, path) AS fname, note FROM resources WHERE course_id=?', (course_id,))
        rows = c.fetchall()
        for item in self.res_tree.get_children():
            self.res_tree.delete(item)
        for r in rows:
            _id, fname, note = r
            display_fname = fname if fname else ''
            if len(display_fname) > 120:
                display_fname = '...' + display_fname[-117:]
            self.res_tree.insert('', 'end', iid=str(_id), values=(display_fname, note or ''))
        self.status_var.set(f'{len(rows)} ressources chargées')
        self.after(50, self.adjust_columns)

    def add_course_dialog(self):
        dialog = tk.Toplevel(self)
        dialog.title('Ajouter un cours')
        dialog.geometry('400x300')

        name_var = tk.StringVar()
        teacher_var = tk.StringVar()
        ttk.Label(dialog, text='Nom :').pack(anchor='w', padx=8, pady=4)
        ttk.Entry(dialog, textvariable=name_var).pack(fill='x', padx=8)
        ttk.Label(dialog, text='Professeur :').pack(anchor='w', padx=8, pady=4)
        ttk.Entry(dialog, textvariable=teacher_var).pack(fill='x', padx=8)
        ttk.Label(dialog, text='Description :').pack(anchor='w', padx=8, pady=4)
        desc = tk.Text(dialog, height=6)
        desc.pack(fill='both', expand=True, padx=8)

        def create_course():
            name = name_var.get().strip()
            teacher = teacher_var.get().strip()
            description = desc.get('1.0', 'end').strip()
            if not name:
                messagebox.showwarning('Erreur', 'Le nom du cours est requis')
                return
            c = self.conn.cursor()
            c.execute('INSERT INTO courses (name, teacher, description) VALUES (?,?,?)', (name, teacher, description))
            self.conn.commit()
            dialog.destroy()
            self.load_courses()
            self.status_var.set('Cours ajouté')

        ttk.Button(dialog, text='Créer', command=create_course).pack(pady=8)

    def save_current_course(self):
        if not hasattr(self, 'current_course_id'):
            messagebox.showinfo('Info', 'Aucun cours sélectionné')
            return
        name = self.name_var.get().strip()
        teacher = self.teacher_var.get().strip()
        description = self.description_text.get('1.0', 'end').strip()
        if USE_TKCALENDAR:
            due = self.due_widget.get_date().strftime('%Y-%m-%d')
        else:
            due = self.due_var.get().strip()
            if due == '':
                due = None
            else:
                try:
                    datetime.datetime.strptime(due, '%Y-%m-%d')
                except Exception:
                    messagebox.showerror('Erreur', 'Format de date invalide (attendu YYYY-MM-DD)')
                    return
        c = self.conn.cursor()
        c.execute('UPDATE courses SET name=?, teacher=?, description=?, due_date=? WHERE id=?', (name, teacher, description, due, self.current_course_id))
        self.conn.commit()
        self.load_courses()
        self.status_var.set('Cours enregistré')

    def delete_current_course(self):
        if not hasattr(self, 'current_course_id'):
            messagebox.showinfo('Info', 'Aucun cours sélectionné')
            return
        if not messagebox.askyesno('Confirmer', 'Supprimer ce cours et toutes ses ressources ?'):
            return
        c = self.conn.cursor()
        c.execute('DELETE FROM courses WHERE id=?', (self.current_course_id,))
        c.execute('DELETE FROM resources WHERE course_id=?', (self.current_course_id,))
        self.conn.commit()
        delattr(self, 'current_course_id')
        self.load_courses()
        self.description_text.delete('1.0', 'end')
        self.name_var.set('')
        self.teacher_var.set('')
        if not USE_TKCALENDAR:
            self.due_var.set('')
        self.status_var.set('Cours supprimé')

    def toggle_done(self):
        if not hasattr(self, 'current_course_id'):
            messagebox.showinfo('Info', 'Aucun cours sélectionné')
            return
        c = self.conn.cursor()
        c.execute('SELECT done FROM courses WHERE id=?', (self.current_course_id,))
        done = c.fetchone()[0]
        new = 0 if done else 1
        c.execute('UPDATE courses SET done=? WHERE id=?', (new, self.current_course_id))
        self.conn.commit()
        self.load_courses()
        self.status_var.set('Statut modifié')

    def add_resource(self):
        if not hasattr(self, 'current_course_id'):
            messagebox.showinfo('Info', "Sélectionnez d'un cours avant d'ajouter une ressource")
            return
        paths = filedialog.askopenfilenames(title='Sélectionner des fichiers')
        if not paths:
            return
        note = simple_input(self, 'Note (optionnelle) pour ces fichiers :')
        c = self.conn.cursor()
        added = 0
        for p in paths:
            try:
                with open(p, 'rb') as f:
                    raw = f.read()
                comp = gzip.compress(raw)
                filename = os.path.basename(p)
                c.execute('INSERT INTO resources (course_id, path, filename, data, note) VALUES (?,?,?,?,?)', (
                    self.current_course_id, os.path.abspath(p), filename, sqlite3.Binary(comp), note
                ))
                added += 1
            except Exception:
                try:
                    filename = os.path.basename(p)
                    c.execute('INSERT INTO resources (course_id, path, filename, note) VALUES (?,?,?,?)', (
                        self.current_course_id, os.path.abspath(p), filename, note
                    ))
                    added += 1
                except Exception:
                    pass
        self.conn.commit()
        self.load_resources(self.current_course_id)
        self.status_var.set(f'{added} fichier(s) ajoutés (copiés et compressés dans la DB)')

    def open_selected_resource(self):
        sel = self.res_tree.selection()
        if not sel:
            messagebox.showinfo('Info', 'Aucune ressource sélectionnée')
            return
        res_id = int(sel[0])
        c = self.conn.cursor()
        c.execute('SELECT path, filename, data FROM resources WHERE id=?', (res_id,))
        row = c.fetchone()
        if not row:
            messagebox.showerror('Erreur', 'Ressource introuvable')
            return
        orig_path, filename, data = row
        if data:
            try:
                raw = gzip.decompress(data)
            except Exception:
                raw = None
            if raw is not None:
                suffix = ''
                if filename and '.' in filename:
                    suffix = os.path.splitext(filename)[1]
                tmp = tempfile.NamedTemporaryFile(delete=False, suffix=suffix)
                try:
                    tmp.write(raw)
                    tmp.flush()
                    tmp.close()
                    open_file_with_default(tmp.name)
                    self.status_var.set('Fichier extrait et ouvert depuis la DB')
                    return
                except Exception as e:
                    try:
                        os.unlink(tmp.name)
                    except Exception:
                        pass
                    messagebox.showerror('Erreur', f"Impossible d'ouvrir le fichier extrait : {e}")
                    return
        if orig_path and os.path.exists(orig_path):
            try:
                open_file_with_default(orig_path)
                self.status_var.set('Fichier ouvert depuis le chemin d\'origine')
                return
            except Exception as e:
                messagebox.showerror('Erreur', f"Impossible d'ouvrir le fichier : {e}")
                return
        messagebox.showerror('Erreur', 'Aucune donnée disponible pour cette ressource')

    def delete_selected_resource(self):
        sel = self.res_tree.selection()
        if not sel:
            messagebox.showinfo('Info', 'Aucune ressource sélectionnée')
            return
        res_id = int(sel[0])
        if not messagebox.askyesno('Confirmer', 'Supprimer cette ressource ?'):
            return
        c = self.conn.cursor()
        c.execute('DELETE FROM resources WHERE id=?', (res_id,))
        self.conn.commit()
        self.load_resources(self.current_course_id)
        self.status_var.set('Ressource supprimée')

    def export_json(self):
        path = filedialog.asksaveasfilename(defaultextension='.json', filetypes=[('JSON files', '*.json')], title='Exporter en JSON')
        if not path:
            return
        c = self.conn.cursor()
        c.execute('SELECT id, name, teacher, description, due_date, done FROM courses')
        courses = []
        for r in c.fetchall():
            cid, name, teacher, desc, due, done = r
            c2 = self.conn.cursor()
            c2.execute('SELECT path, note, filename FROM resources WHERE course_id=?', (cid,))
            res = [{'path':row[0], 'note':row[1], 'filename':row[2]} for row in c2.fetchall()]
            courses.append({'id':cid,'name':name,'teacher':teacher,'description':desc,'due_date':due,'done':done,'resources':res})
        with open(path, 'w', encoding='utf-8') as f:
            json.dump({'exported_at': datetime.datetime.utcnow().isoformat(), 'courses': courses}, f, ensure_ascii=False, indent=2)
        self.status_var.set('Export terminé')
        messagebox.showinfo('Export', 'Export JSON effectué (les blobs binaires ne sont pas inclus)')

    def import_json(self):
        path = filedialog.askopenfilename(title='Importer JSON', filetypes=[('JSON files','*.json')])
        if not path:
            return
        with open(path, 'r', encoding='utf-8') as f:
            data = json.load(f)
        inserted = 0
        for cobj in data.get('courses', []):
            name = cobj.get('name') or 'Sans nom'
            teacher = cobj.get('teacher')
            desc = cobj.get('description')
            due = cobj.get('due_date')
            done = cobj.get('done') or 0
            c = self.conn.cursor()
            c.execute('INSERT INTO courses (name, teacher, description, due_date, done) VALUES (?,?,?,?,?)', (name, teacher, desc, due, done))
            cid = c.lastrowid
            for r in cobj.get('resources', []):
                pathr = r.get('path')
                note = r.get('note')
                filename = r.get('filename')
                data_blob = None
                if pathr and os.path.exists(pathr):
                    try:
                        with open(pathr, 'rb') as f2:
                            data_blob = gzip.compress(f2.read())
                    except Exception:
                        data_blob = None
                if data_blob:
                    c.execute('INSERT INTO resources (course_id, path, filename, data, note) VALUES (?,?,?,?,?)', (cid, pathr, filename, sqlite3.Binary(data_blob), note))
                else:
                    c.execute('INSERT INTO resources (course_id, path, filename, note) VALUES (?,?,?,?)', (cid, pathr, filename, note))
            inserted += 1
        self.conn.commit()
        self.load_courses()
        messagebox.showinfo('Import', f'Import terminé : {inserted} cours ajoutés')

    def adjust_columns(self):
        try:
            total = self.tree.winfo_width()
            if total <= 0:
                return
            name_w = int(total * 0.5)
            rest = max(total - name_w, 180)
            teacher_w = int(rest * 0.45)
            due_w = int(rest * 0.35)
            done_w = max(60, rest - teacher_w - due_w)
            self.tree.column('#0', width=name_w)
            self.tree.column('teacher', width=max(100, teacher_w))
            self.tree.column('due', width=max(100, due_w))
            self.tree.column('done', width=done_w)

            rtotal = self.res_tree.winfo_width()
            if rtotal > 0:
                self.res_tree.column('path', width=int(rtotal * 0.72))
                self.res_tree.column('note', width=int(rtotal * 0.28))
        except Exception:
            pass

    def on_root_resize(self, event):
        self.after(50, self.adjust_columns)

def simple_input(root, prompt):
    dlg = tk.Toplevel(root)
    dlg.title('Entrée')
    dlg.geometry('400x120')
    ttk.Label(dlg, text=prompt).pack(anchor='w', padx=8, pady=6)
    var = tk.StringVar()
    ttk.Entry(dlg, textvariable=var).pack(fill='x', padx=8)
    res = {'value': None}
    def ok():
        res['value'] = var.get()
        dlg.destroy()
    ttk.Button(dlg, text='OK', command=ok).pack(pady=8)
    dlg.transient(root)
    dlg.grab_set()
    root.wait_window(dlg)
    return res['value']

if __name__ == '__main__':
    conn = init_db()
    app = CourseManagerApp(conn)
    app.mainloop()
