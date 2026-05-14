import os
import tkinter as tk
from tkinter import filedialog, messagebox, StringVar, BooleanVar
import math
import random
import time
import json
import ctypes
import fnmatch
import hashlib
import re
from datetime import datetime, timedelta

# --- GLOBAL SETTINGS ---
ENABLE_KEK = False            
ENABLE_EDITOR = True         
ENABLE_SAFE_MODE_UI = True   
ENABLE_ADVANCED_MASKS = True 
ENABLE_LOGGING = True
ENABLE_DRY_RUN_UI = True
ENABLE_HASH_DEDUPLICATION = True
ENABLE_REGEX_SUPPORT = True

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILENAME = os.path.join(SCRIPT_DIR, "file_organizer_config.json")

DEFAULT_FILE_TYPES = {
    'Изображения': ['.jpg', '.jpeg', '.png', '.gif', '.bmp', '.ico', '.webp', '.avif', '.tiff', '.tif', '.svg', '.heic', '.jfif', '.psd', '.xpm', '.tga', '.rgb', '.rgba', '.hdr'],
    'Документы': ['.pdf', '.doc', '.docx', '.txt', '.rtf', '.odt', '.xls', '.xlsx', '.ods', '.ppt', '.pptx', '.pps', '.ppsx', '.csv', '.xml', '.json', '.md', '.rst', '.tex', '.log', '.ini', '.cfg', '.conf', '.config', '.env', '.properties', '.yaml', '.yml', '.toml', '.bib', '.epub', '.mobi', '.fb2', '.djvu'],
    'Архивы': ['.zip', '.rar', '.7z', '.tar', '.gz', '.bz2', '.xz', '.tgz', '.cab', '.msi', '.msix', '.msixbundle', '.appx', '.appxbundle', '.pkg', '.deb', '.rpm', '.iso', '.img', '.dmg', '.pak'],
    'Видео': ['.mp4', '.avi', '.mkv', '.mov', '.wmv', '.flv', '.webm', '.m4v', '.mpeg', '.mpg', '.3gp', '.ts', '.m2ts', '.ogv'],
    'Музыка': ['.mp3', '.wav', '.flac', '.aac', '.ogg', '.m4a', '.opus', '.wma', '.mid', '.midi', '.ape'],
    'Программы': ['.exe', '.msi', '.app', '.deb', '.rpm', '.dmg', '.pkg', '.jar', '.apk', '.ipa', '.msix', '.appx', '.bin', '.sh', '.bat', '.cmd', '.ps1', '.vbs', '.scr', '.com', '.msu', '.crdownload', '.partial', '.download'],
    'Скрипты': ['.py', '.js', '.html', '.htm', '.css', '.php', '.rb', '.pl', '.lua', '.go', '.rs', '.swift', '.kt', '.java', '.c', '.cpp', '.h', '.hpp', '.cs', '.fs', '.dart', '.groovy', '.sh', '.bash', '.zsh', '.fish', '.ps1', '.psm1', '.psd1', '.vbs', '.ahk', '.au3', '.sql', '.sqlite', '.r', '.jl', '.scm', '.clj', '.coffee', '.ts', '.tsx', '.jsx', '.vue', '.sass', '.scss', '.less', '.styl', '.pug', '.ejs', '.handlebars', '.hbs', '.template', '.tmpl', '.tpl', '.j2', '.yaml', '.yml', '.toml', '.ini', '.conf', '.config', '.dockerfile', '.makefile', '.cmake', '.gradle', '.xml', '.json', '.jsonc', '.ipynb', '.md', '.rst'],
    'Шрифты': ['.ttf', '.otf', '.woff', '.woff2', '.eot', '.fnt', '.fon'],
    'Системные': ['.dll', '.sys', '.drv', '.ocx', '.vxd', '.lib', '.obj', '.pdb', '.exp', '.ilk', '.ncb', '.sdf', '.suo', '.user', '.reg', '.pol', '.msc', '.inf', '.cat', '.cpl', '.dat', '.db', '.db3', '.db-journal', '.ldb', '.mdf', '.ndf', '.bak', '.old', '.tmp', '.temp', '.lock', '.log'],
    'Книги': ['.epub', '.mobi', '.fb2', '.azw', '.azw3', '.lit', '.lrf', '.pdf', '.djvu', '.cbr', '.cbz', '.cbt', '.cb7'],
    'Ярлыки': ['.lnk', '.url']
}

COLORS = {
    'primary': '#0f766e', 'on_primary': '#ffffff', 'surface': '#ffffff',
    'on_surface': '#0f172a', 'surface_variant': '#f1f5f9', 'outline': '#94a3b8',
    'outline_variant': '#e2e8f0', 'background': '#f8fafc', 'error': '#b91c1c',
    'success': '#15803d', 'file_blue': '#3b82f6', 'file_green': '#10b981',
    'file_purple': '#8b5cf6', 'file_yellow': '#f59e0b', 'file_pink': '#ec4899'
}

FONTS = {
    'title': ('Segoe UI', 16, 'bold'), 'subtitle': ('Segoe UI', 10, 'bold'),
    'body': ('Segoe UI', 10), 'caption': ('Segoe UI', 9)
}

# --- GLOBAL STATE ---
root = None
entry_p_widget = None
cfg_p_var = None
safe_mode_var = None
dry_run_var = None
errmsg_var = None
moved_msg_var = None
safe_paths = []

# Animation state
anim_canvas = None
anim_files = {}
anim_organizing_all = False
anim_mouse_x, anim_mouse_y = -100, -100
anim_last_update = 0

# --- HELPERS ---

def parse_size(s):
    if not s: return 0
    s = str(s).upper().strip()
    units = {"KB": 1024, "MB": 1024**2, "GB": 1024**3}
    for u, v in units.items():
        if s.endswith(u): return float(s[:-2].strip()) * v
    return float(s)

def parse_date(s):
    if not s: return 0
    s = str(s).lower().strip()
    if s.endswith('d'): return time.time() - float(s[:-1]) * 86400
    return 0 

def get_file_hash(filepath):
    h = hashlib.sha256()
    try:
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(4096), b""): h.update(chunk)
        return h.hexdigest()
    except Exception: return None

def log_action(msg):
    if not ENABLE_LOGGING: return
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    log_path = os.path.join(SCRIPT_DIR, "file_organizer.log")
    with open(log_path, "a", encoding="utf-8") as f: f.write(f"[{ts}] {msg}\n")

# --- UI COMPONENT FUNCTIONS ---

def create_round_rect(canvas, x1, y1, x2, y2, r, **kwargs):
    p = [x1+r, y1, x1+r, y1, x2-r, y1, x2-r, y1, x2, y1, x2, y1+r, x2, y1+r, x2, y2-r, x2, y2-r, x2, y2, x2-r, y2, x2-r, y2, x1+r, y2, x1+r, y2, x1, y2, x1, y2-r, x1, y2-r, x1, y1+r, x1, y1+r, x1, y1]
    return canvas.create_polygon(p, **kwargs, smooth=True)

def create_modern_button(parent, text, command=None, width=180, height=40, primary=True, is_scary=False, disabled=False):
    btn = tk.Canvas(parent, width=width, height=height, bg=parent['bg'], highlightthickness=0)
    btn.command = command; btn.is_disabled = disabled
    color = COLORS['error'] if is_scary else (COLORS['primary'] if primary else COLORS['surface_variant'])
    hover_color = '#991b1b' if is_scary else ('#0d5e58' if primary else COLORS['outline_variant'])
    text_color = COLORS['on_primary'] if (primary or is_scary) else COLORS['on_surface']
    
    rect = create_round_rect(btn, 0, 0, width, height, 20, fill=color if not disabled else COLORS['outline'], outline="")
    label = btn.create_text(width/2, height/2, text=text, fill=text_color if not disabled else COLORS['on_surface'], font=FONTS['body'])
    
    def on_enter(e):
        if not btn.is_disabled: btn.itemconfig(rect, fill=hover_color)
    def on_leave(e):
        if not btn.is_disabled: btn.itemconfig(rect, fill=color)
    def on_click(e):
        if not btn.is_disabled and btn.command: btn.command()
    
    btn.bind("<Enter>", on_enter); btn.bind("<Leave>", on_leave); btn.bind("<Button-1>", on_click)
    
    def set_disabled(is_disabled, new_text=None):
        btn.is_disabled = is_disabled
        if new_text: btn.itemconfig(label, text=new_text)
        btn.itemconfig(rect, fill=color if not is_disabled else COLORS['outline'])
    
    btn.set_disabled = set_disabled
    return btn

def show_modern_dialog(parent, title, text, is_scary=False, lock_time=0):
    dlg = tk.Toplevel(parent); dlg.title(title); dlg.geometry("550x350")
    dlg.configure(bg=COLORS['background']); dlg.transient(parent); dlg.grab_set()
    
    def on_close():
        if lock_time > 0: pass # Block close if locked
        else: dlg.destroy()
    dlg.protocol("WM_DELETE_WINDOW", on_close)
    
    c = tk.Frame(dlg, bg=COLORS['background'], padx=25, pady=25); c.pack(fill='both', expand=True)
    tk.Label(c, text=title.upper(), font=FONTS['title'], bg=COLORS['background'], fg=COLORS['error'] if is_scary else COLORS['primary']).pack(anchor='w', pady=(0, 10))
    
    tx_f = tk.Frame(c, bg=COLORS['background']); tx_f.pack(fill='both', expand=True, pady=(0, 20))
    txt = tk.Text(tx_f, font=FONTS['body'], bg=COLORS['background'], fg=COLORS['on_surface'], relief='flat', highlightthickness=0, wrap='word', height=10)
    sb = tk.Scrollbar(tx_f, orient="vertical", command=txt.yview); txt.configure(yscrollcommand=sb.set)
    txt.pack(side='left', fill='both', expand=True)
    if len(text) > 200: sb.pack(side='right', fill='y')
    txt.insert('1.0', text); txt.configure(state='disabled')

    btn = create_modern_button(c, "ПОНЯТНО", dlg.destroy, width=140, height=40, is_scary=is_scary, disabled=(lock_time > 0))
    btn.pack(side='bottom')
    
    def countdown(t):
        if t > 0: btn.set_disabled(True, f"ЖДИТЕ ({t}с)"); dlg.after(1000, lambda: countdown(t-1))
        else: btn.set_disabled(False, "Я ПОНИМАЮ РИСК")
    
    if lock_time > 0: countdown(lock_time)

# --- CONFIG EDITOR ---

def show_config_editor(parent, data, on_save):
    editor_window = tk.Toplevel(parent); editor_window.title("Редактор правил"); editor_window.geometry("550x700")
    editor_window.configure(bg=COLORS['background']); editor_window.data = data.copy(); editor_window.transient(parent); editor_window.grab_set()
    
    main_container = tk.Frame(editor_window, bg=COLORS['background'], padx=20, pady=20); main_container.pack(fill='both', expand=True)
    tk.Label(main_container, text="НАСТРОЙКА ПРАВИЛ СОРТИРОВКИ", font=FONTS['title'], bg=COLORS['background'], fg=COLORS['primary']).pack(anchor='w', pady=(0, 15))
    
    scroll_frame = tk.Frame(main_container, bg=COLORS['surface_variant']); scroll_frame.pack(fill='both', expand=True)
    canvas = tk.Canvas(scroll_frame, bg=COLORS['surface_variant'], highlightthickness=0)
    scrollbar = tk.Scrollbar(scroll_frame, orient="vertical", command=canvas.yview)
    inner_frame = tk.Frame(canvas, bg=COLORS['surface_variant'])
    inner_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
    canvas.create_window((0, 0), window=inner_frame, anchor="nw")
    canvas.configure(yscrollcommand=scrollbar.set)
    canvas.pack(side="left", fill="both", expand=True); scrollbar.pack(side="right", fill="y")
    
    
    def refresh():
        for widget in inner_frame.winfo_children(): widget.destroy()
        for folder, config in editor_window.data.items():
            item_row = tk.Frame(inner_frame, bg=COLORS['surface_variant'], pady=5); item_row.pack(fill='x', padx=5)
            tk.Label(item_row, text=f"📁 {folder}", font=FONTS['subtitle'], bg=COLORS['surface_variant'], width=12, anchor='w').pack(side='left')
            masks = config.get('masks', []) if isinstance(config, dict) else config
            info = f"Маски: {', '.join(masks) if isinstance(masks, list) else str(masks)}"
            if isinstance(config, dict):
                if config.get('min_size'): info += f" | >{config['min_size']}"
                if config.get('max_date'): info += f" | <{config['max_date']}"
            tk.Label(item_row, text=info, font=FONTS['caption'], bg=COLORS['surface_variant'], wraplength=250, justify='left').pack(side='left', padx=10)
            
            def make_edit_cmd(f=folder, c=config): return lambda: edit(f, c)
            def make_rem_cmd(f=folder): return lambda: rem(f)
            
            tk.Button(item_row, text="✎", bg=COLORS['surface_variant'], relief='flat', command=make_edit_cmd()).pack(side='right', padx=2)
            tk.Button(item_row, text="✕", fg=COLORS['error'], bg=COLORS['surface_variant'], relief='flat', command=make_rem_cmd()).pack(side='right')

    def edit(folder_name, config_val):
        entry_folder.delete(0, 'end'); entry_folder.insert(0, folder_name)
        masks = config_val.get('masks', []) if isinstance(config_val, dict) else config_val
        entry_masks.delete(0, 'end'); entry_masks.insert(0, ", ".join(masks) if isinstance(masks, list) else str(masks))
        entry_min_size.delete(0, 'end'); entry_min_size.insert(0, config_val.get('min_size', '') if isinstance(config_val, dict) else '')
        entry_max_date.delete(0, 'end'); entry_max_date.insert(0, config_val.get('max_date', '') if isinstance(config_val, dict) else '')

    def add():
        folder, masks_str = entry_folder.get().strip(), entry_masks.get().strip()
        if folder and masks_str:
            editor_window.data[folder] = {"masks": [m.strip() for m in masks_str.split(',')]}
            if entry_min_size.get().strip(): editor_window.data[folder]["min_size"] = entry_min_size.get().strip()
            if entry_max_date.get().strip(): editor_window.data[folder]["max_date"] = entry_max_date.get().strip()
            refresh()

    def rem(folder): del editor_window.data[folder]; refresh()

    def save():
        timestamp = datetime.now().strftime("%Y%m%d_%H%M"); filename = f"config_{timestamp}.json"
        with open(filename, 'w', encoding='utf-8') as f: json.dump(editor_window.data, f, ensure_ascii=False, indent=4)
        on_save(filename); editor_window.destroy()

    add_row_frame = tk.Frame(main_container, bg=COLORS['background'], pady=10); add_row_frame.pack(fill='x')
    entry_folder = tk.Entry(add_row_frame, font=FONTS['body'], width=15); entry_folder.grid(row=1, column=0, padx=2)
    entry_masks = tk.Entry(add_row_frame, font=FONTS['body'], width=15); entry_masks.grid(row=1, column=1, padx=2)
    entry_min_size = tk.Entry(add_row_frame, font=FONTS['body'], width=8); entry_min_size.grid(row=1, column=2, padx=2)
    entry_max_date = tk.Entry(add_row_frame, font=FONTS['body'], width=8); entry_max_date.grid(row=1, column=3, padx=2)
    tk.Label(add_row_frame, text="Папка", font=FONTS['caption'], bg=COLORS['background']).grid(row=0, column=0)
    tk.Label(add_row_frame, text="Маски", font=FONTS['caption'], bg=COLORS['background']).grid(row=0, column=1)
    tk.Label(add_row_frame, text="Мин. разм", font=FONTS['caption'], bg=COLORS['background']).grid(row=0, column=2)
    tk.Label(add_row_frame, text="Макс. дата", font=FONTS['caption'], bg=COLORS['background']).grid(row=0, column=3)
    refresh()
    create_modern_button(add_row_frame, "ДОБАВИТЬ / ОБНОВИТЬ", add, width=220, height=30).grid(row=2, column=0, columnspan=4, pady=10)
    create_modern_button(main_container, "СОХРАНИТЬ", save, width=320).pack()

# --- ANIMATION LOGIC ---

def setup_animation():
    global anim_canvas, anim_files, anim_last_update
    fc = [COLORS['file_blue'], COLORS['file_purple'], COLORS['file_yellow'], COLORS['file_pink']]
    for i in range(30):
        x, y = random.randint(50, 350), random.randint(20, 100)
        col = COLORS['file_green'] if i < 2 else random.choice(fc)
        tag = f"file_{i}"
        f_id = anim_canvas.create_polygon(0, 0, 12, 0, 16, 4, 16, 20, 0, 20, fill=col, stipple='gray25', tags=tag)
        anim_canvas.move(f_id, x, y)
        anim_files[tag] = {'id': f_id, 'x': float(x), 'y': float(y), 'vx': random.uniform(-40, 40), 'vy': random.uniform(-20, 20),
            'color': col, 'target_x': 0.0, 'target_y': 0.0, 'individual_organizing': False, 'orbit_angle': random.uniform(0, 2*math.pi), 'tele_t': 0}
        
        def make_click_cmd(t=tag): return lambda e: on_anim_file_click(t)
        if ENABLE_KEK: anim_canvas.tag_bind(tag, "<Button-1>", make_click_cmd())
    anim_last_update = time.time()
    animate()

def on_anim_file_click(tag):
    global anim_files, anim_organizing_all
    f = anim_files[tag]
    if f['individual_organizing'] or anim_organizing_all: return
    f['individual_organizing'] = True; idx = ([COLORS['file_blue'], COLORS['file_green'], COLORS['file_purple'], COLORS['file_yellow'], COLORS['file_pink']].index(f['color'])) % 4
    f['target_x'], f['target_y'] = float(100 + idx * 70), float(120 - (random.randint(0, 5)) * 4)
    root.after(2000, lambda: reset_anim_file(tag))

def reset_anim_file(tag):
    f = anim_files[tag]; f['individual_organizing'] = False; f['vx'], f['vy'] = random.uniform(-40, 40), random.uniform(-20, 20)
    f['tele_t'] = 0; anim_canvas.itemconfig(f['id'], stipple='gray25', fill=f['color'])

def push_mouse(fx, fy, fvx, fvy):
    if (anim_mouse_x - fx) * fvx + (anim_mouse_y - fy) * fvy < 0: return
    try:
        import ctypes.wintypes
        p = ctypes.wintypes.POINT(); ctypes.windll.user32.GetCursorPos(ctypes.byref(p))
        dx, dy = (15 if anim_mouse_x > fx else -15), (15 if anim_mouse_y > fy else -15)
        ctypes.windll.user32.SetCursorPos(p.x + dx, p.y + dy)
    except Exception: pass

def animate():
    global anim_files, anim_organizing_all, anim_last_update, anim_mouse_x, anim_mouse_y
    now = time.time(); dt = min(now - anim_last_update, 0.05); anim_last_update = now
    for tag, f in anim_files.items():
        old_x, old_y = f['x'], f['y']
        if not anim_organizing_all and not f['individual_organizing']:
            dist = math.sqrt((f['x'] - anim_mouse_x)**2 + (f['y'] - anim_mouse_y)**2)
            if ENABLE_KEK and dist < 65:
                if f['color'] == COLORS['file_blue']:
                    rep = 220 * (1 - dist/65); ang = math.atan2(f['y'] - anim_mouse_y, f['x'] - anim_mouse_x)
                    f['x'] += math.cos(ang) * rep * dt; f['y'] += math.sin(ang) * rep * dt
                elif f['color'] == COLORS['file_green'] and dist < 45: push_mouse(f['x'], f['y'], f['vx'], f['vy'])
                elif f['color'] == COLORS['file_purple'] and dist < 45:
                    f['tele_t'] += dt; anim_canvas.itemconfig(f['id'], fill='#a78bfa')
                    if f['tele_t'] > 0.4: f['x'], f['y'] = random.randint(50, 350), random.randint(20, 100); f['tele_t'] = 0
                elif f['color'] == COLORS['file_yellow']:
                    f['orbit_angle'] += 7 * dt; f['x'] = anim_mouse_x + math.cos(f['orbit_angle']) * 45; f['y'] = anim_mouse_y + math.sin(f['orbit_angle']) * 45
                elif f['color'] == COLORS['file_pink'] and dist < 45: anim_canvas.itemconfig(f['id'], stipple='gray12' if dist < 25 else 'gray25')
            else:
                if f['color'] == COLORS['file_purple']: anim_canvas.itemconfig(f['id'], fill=f['color'])
            if not (ENABLE_KEK and f['color'] == COLORS['file_yellow'] and dist < 65): f['x'] += f['vx'] * dt; f['y'] += f['vy'] * dt
            if f['x'] < 10: f['x'] = 10; f['vx'] *= -1
            if f['x'] > 380: f['x'] = 380; f['vx'] *= -1
            if f['y'] < 10: f['y'] = 10; f['vy'] *= -1
            if f['y'] > 120: f['y'] = 120; f['vy'] *= -1
        else:
            f['x'] += (f['target_x'] - f['x']) * 10.0 * dt; f['y'] += (f['target_y'] - f['y']) * 10.0 * dt
        anim_canvas.move(f['id'], f['x'] - old_x, f['y'] - old_y)
    root.after(10, animate)

# --- MAIN APP LOGIC ---

def browse_folder():
    p = filedialog.askdirectory()
    if p:
        p = os.path.normpath(p)
        entry_p_widget.delete(0, 'end'); entry_p_widget.insert(0, p)

def browse_config():
    p = filedialog.askopenfilename(filetypes=[("JSON", "*.json")])
    if p: cfg_p_var.set(p)

def on_safe_mode_change():
    if not safe_mode_var.get(): 
        show_modern_dialog(root, "КРИТИЧЕСКАЯ ОПАСНОСТЬ", "ВЫ ОТКЛЮЧАЕТЕ БЕЗОПАСНЫЙ РЕЖИМ!\n\nЭто позволяет программе изменять системные файлы. Ошибка может привести к поломке ОС.\n\nПрочитайте это внимательно, пока кнопка заблокирована.", is_scary=True, lock_time=10)

def show_safe_paths(): show_modern_dialog(root, "ЗАЩИТА", "Защищенные пути:\n" + "\n".join(safe_paths))

def show_help():
    help_text = (
        "ОСНОВНЫЕ ПРАВИЛА:\n\n"
        "• Маски: * (любые символы), ? (один символ). Пример: *.jpg, file_?.*\n"
        "• Regex: Гибкий поиск. Пример: ^IMG_\\d{4}.*\n"
        "• Размер (min_size): Только файлы больше лимита (5MB, 100KB).\n"
        "• Дата (max_date): Файлы старше N дней (30d, 7d).\n"
        "• Исключения (ignore): Список масок, которые нужно пропустить.\n\n"
        "РЕЖИМЫ:\n"
        "• Симуляция: Проверка правил без перемещения файлов.\n"
        "• Дедупликация: Проверка хеша (SHA-256). Одинаковые файлы пропускаются."
    )
    show_modern_dialog(root, "СПРАВКА ПО ПРАВИЛАМ", help_text)

def paste_clipboard(widget):
    try:
        text = root.clipboard_get().strip('"').strip()
        text = os.path.normpath(text)
        if isinstance(widget, tk.Entry): widget.delete(0, 'end'); widget.insert(0, text)
        else: widget.set(text)
    except Exception: pass

def paste_config_text():
    try:
        text = root.clipboard_get()
        data = json.loads(text)
        show_config_editor(root, data, lambda p: cfg_p_var.set(p))
    except Exception as e:
        messagebox.showerror("Ошибка JSON", f"Не удалось распознать JSON из буфера:\n{str(e)}")

def open_editor():
    try:
        with open(cfg_p_var.get(), 'r', encoding='utf-8') as f: data = json.load(f)
    except Exception: data = DEFAULT_FILE_TYPES
    show_config_editor(root, data, lambda p: cfg_p_var.set(p))

def run_organization():
    path = entry_p_widget.get().strip('"').strip()
    path = os.path.normpath(path)
    if not path or not os.path.isdir(path): errmsg_var.set("Путь не найден"); return
    
    safe_paths_norm = [os.path.normpath(p).lower() for p in safe_paths]
    if safe_mode_var.get() and any(path.lower() == p or path.lower().startswith(p + os.sep) for p in safe_paths_norm):
         messagebox.showwarning("Защита", "Путь защищен!"); return
    try:
        with open(cfg_p_var.get(), 'r', encoding='utf-8') as f: ft = json.load(f)
    except Exception: messagebox.showerror("Ошибка", "Конфиг не читается!"); return
    
    errmsg_var.set(""); 
    # Start animation organization
    global anim_organizing_all
    anim_organizing_all = True
    for i, (tag, f) in enumerate(anim_files.items()):
        idx = ([COLORS['file_blue'], COLORS['file_green'], COLORS['file_purple'], COLORS['file_yellow'], COLORS['file_pink']].index(f['color'])) % 4
        f['target_x'], f['target_y'] = float(100 + idx * 70), float(120 - (i % 6) * 4)
    
    files = [f for f in os.listdir(path) if os.path.isfile(os.path.join(path, f))]
    
    def step(i, count):
        if i >= len(files):
            msg = f"Завершено. Обработано файлов: {count}"
            if dry_run_var.get(): msg += " (РЕЖИМ СИМУЛЯЦИИ)"
            log_action(f"=== {msg} ===")
            messagebox.showinfo("Готово", msg); moved_msg_var.set("")
            global anim_organizing_all; anim_organizing_all = False
            for t in anim_files: reset_anim_file(t)
            return
        
        f = files[i]; f_p = os.path.join(path, f)
        if f != os.path.basename(cfg_p_var.get()):
            stat = os.stat(f_p)
            cat = 'Прочее'
            for folder, rule in ft.items():
                masks = rule.get("masks", []) if isinstance(rule, dict) else rule
                regex = rule.get("regex", []) if isinstance(rule, dict) and ENABLE_REGEX_SUPPORT else []
                ignore = rule.get("ignore", []) if isinstance(rule, dict) else []
                match = any(fnmatch.fnmatch(f.lower(), m.lower()) for m in masks)
                if not match and regex: match = any(re.search(r, f, re.IGNORECASE) for r in regex)
                if match:
                    if any(fnmatch.fnmatch(f.lower(), ig.lower()) for ig in ignore): continue
                    if isinstance(rule, dict):
                        if "min_size" in rule and stat.st_size < parse_size(rule["min_size"]): continue
                        if "max_date" in rule and stat.st_mtime < parse_date(rule["max_date"]): continue
                    cat = folder; break
            
            d = os.path.join(path, cat)
            if not dry_run_var.get() and not os.path.exists(d): os.makedirs(d)
            
            t_path, ct = os.path.join(d, f), 1
            is_duplicate = False
            if os.path.exists(t_path):
                if ENABLE_HASH_DEDUPLICATION:
                    h1, h2 = get_file_hash(f_p), get_file_hash(t_path)
                    if h1 and h2 and h1 == h2: is_duplicate = True
                if not is_duplicate:
                    while os.path.exists(t_path):
                        n, e = os.path.splitext(f); t_path, ct = os.path.join(d, f"{n}_{ct}{e}"), ct + 1
            
            if is_duplicate: log_action(f"SKIP (Duplicate): {f} -> {cat}")
            elif dry_run_var.get(): log_action(f"DRY RUN: {f} -> {cat}"); count += 1
            else: os.rename(f_p, t_path); log_action(f"MOVE: {f} -> {cat}"); count += 1
            
            moved_msg_var.set(f"Обработано: {count}")
        root.after(5, lambda: step(i+1, count))
    
    log_action(f"--- ЗАПУСК ОРГАНИЗАЦИИ: {path} (Dry Run: {dry_run_var.get()}) ---")
    step(0, 0)

# --- UI BUILDER ---

def build_field(parent, label, var_to_set=None):
    tk.Label(parent, text=label, font=FONTS['subtitle'], bg=COLORS['background']).pack(anchor='w', pady=(15, 5))
    fr = tk.Frame(parent, bg=COLORS['outline_variant'], padx=1, pady=1); fr.pack(fill='x', expand=True)
    en = tk.Entry(fr, font=FONTS['body'], relief='flat', bg=COLORS['surface'])
    en.pack(side='left', fill='x', expand=True, padx=(10, 0), pady=10)
    tk.Button(fr, text="📋", font=FONTS['caption'], bg=COLORS['surface'], relief='flat', command=lambda: paste_clipboard(en if not var_to_set else var_to_set)).pack(side='right', padx=5)
    return en

def main():
    global root, entry_p_widget, cfg_p_var, safe_mode_var, dry_run_var, errmsg_var, moved_msg_var, safe_paths, anim_canvas
    
    root = tk.Tk(); root.title("File Organizer | Order"); root.geometry("540x740")
    root.configure(bg=COLORS['background'])
    
    errmsg_var, moved_msg_var = StringVar(), StringVar()
    cfg_p_var = StringVar(value=CONFIG_FILENAME); safe_mode_var = BooleanVar(value=True); dry_run_var = BooleanVar(value=False)
    safe_paths = [os.path.normpath(os.environ.get(v, 'C:\\'+v)) for v in ['Windows', 'ProgramFiles', 'ProgramFiles(x86)']]
    
    if not os.path.exists(CONFIG_FILENAME):
        with open(CONFIG_FILENAME, 'w', encoding='utf-8') as f: json.dump(DEFAULT_FILE_TYPES, f, ensure_ascii=False, indent=4)
        
    h = tk.Frame(root, bg=COLORS['background'], pady=10); h.pack(fill='x')
    
    anim_canvas = tk.Canvas(h, width=400, height=150, bg=COLORS['background'], highlightthickness=0)
    anim_canvas.pack()
    anim_canvas.bind("<Motion>", lambda e: globals().update(anim_mouse_x=e.x, anim_mouse_y=e.y))
    anim_canvas.bind("<Leave>", lambda e: globals().update(anim_mouse_x=-100, anim_mouse_y=-100))
    setup_animation()
    
    tk.Label(h, text="FILE ORGANIZER", font=FONTS['title'], bg=COLORS['background'], fg=COLORS['primary']).pack()
    tk.Label(h, text="Сортировка вашего пространства", font=FONTS['caption'], bg=COLORS['background'], fg=COLORS['outline']).pack()
    if ENABLE_EDITOR:
        tk.Button(h, text="❔ Справка по правилам", font=FONTS['caption'], bg=COLORS['background'], fg=COLORS['primary'], relief='flat', command=show_help).pack(pady=5)
    
    c = tk.Frame(root, bg=COLORS['background'], padx=40); c.pack(fill='both', expand=True)
    entry_p_widget = build_field(c, "Целевая папка")
    
    if ENABLE_EDITOR:
        cfg_h = tk.Frame(c, bg=COLORS['background']); cfg_h.pack(fill='x', pady=(15, 0))
        tk.Label(cfg_h, text="Управление правилами", font=FONTS['subtitle'], bg=COLORS['background']).pack(side='left')
        tk.Button(cfg_h, text="⚙️", font=FONTS['caption'], bg=COLORS['surface_variant'], relief='flat', command=open_editor).pack(side='left', padx=5)
        tk.Button(cfg_h, text="📋 Вставить JSON", font=FONTS['caption'], bg=COLORS['surface_variant'], relief='flat', command=paste_config_text).pack(side='left', padx=5)
        
        e_cfg = tk.Frame(c, bg=COLORS['outline_variant'], padx=1, pady=1); e_cfg.pack(fill='x', pady=(5, 0))
        tk.Entry(e_cfg, textvariable=cfg_p_var, font=FONTS['body'], relief='flat', bg=COLORS['surface']).pack(side='left', fill='x', expand=True, padx=(10, 0), pady=8)
        tk.Button(e_cfg, text="📋", font=FONTS['caption'], bg=COLORS['surface'], relief='flat', command=lambda: paste_clipboard(cfg_p_var)).pack(side='right', padx=5)
    
    btn_r = tk.Frame(c, bg=COLORS['background'], pady=15); btn_r.pack(fill='x')
    create_modern_button(btn_r, "ВЫБОР ПАПКИ", browse_folder, 150, primary=False).pack(side='left', padx=(0,10))
    if ENABLE_EDITOR:
        create_modern_button(btn_r, "ВЫБОР КОНФИГА", browse_config, 150, primary=False).pack(side='left')
        
    if ENABLE_SAFE_MODE_UI:
        opt_r = tk.Frame(c, bg=COLORS['background'], pady=10); opt_r.pack(fill='x')
        tk.Checkbutton(opt_r, text="Безопасный режим", variable=safe_mode_var, font=FONTS['body'], bg=COLORS['background'], command=on_safe_mode_change).pack(side='left')
        if ENABLE_DRY_RUN_UI:
            tk.Checkbutton(opt_r, text="Симуляция (Dry Run)", variable=dry_run_var, font=FONTS['body'], bg=COLORS['background']).pack(side='left', padx=10)
        tk.Button(opt_r, text="🛡️", font=FONTS['caption'], bg=COLORS['surface_variant'], relief='flat', command=show_safe_paths).pack(side='left', padx=5)
        
    tk.Label(c, textvariable=errmsg_var, font=FONTS['caption'], bg=COLORS['background'], fg=COLORS['error']).pack(pady=5)
    create_modern_button(c, "УПОРЯДОЧИТЬ ФАЙЛЫ", run_organization, 360).pack(pady=15)
    tk.Label(c, textvariable=moved_msg_var, font=FONTS['body'], bg=COLORS['background'], fg=COLORS['success']).pack()
    
    root.mainloop()

if __name__ == "__main__":
    main()
