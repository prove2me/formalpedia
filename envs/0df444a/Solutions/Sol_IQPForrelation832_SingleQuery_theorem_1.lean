-- Prove2me | solution 1 for IQPForrelation832.SingleQuery.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:39:34.141939+00:00
-- url     : https://prove2.me/submissions/9e1508e0-2493-4616-8f89-f75fb9ba0dbc

import Definitions.Def_IQPForrelation832_SingleQuery_Programs
import Theorems.Thm_QAlgorithms_DeWolf_clocked_tm2_polytime
import Theorems.Thm_IQPForrelation832_SingleQuery_proposition_4

set_option autoImplicit false

-- ===== Prog =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity IQPForrelation832.SingleQuery

/-- indices `i` of row `j = i+1`: `imin, …, i` with `imin = 0` if `b`, else `1`. -/
def rowIdx : ℕ → Bool → List ℕ
  | 0, b => if b then [0] else []
  | i+1, b => rowIdx i b ++ [i+1]

def czs : ℕ → Bool → List Instruction
  | 0, _ => []
  | j+1, b => czs j b ++ (rowIdx j b).map (fun i => Instruction.cz i (j+1))

def tOf (n : ℕ) : ℕ := if Odd n then n else n + 1

def prog (n : ℕ) (b : Bool) : Program := ⟨tOf n + 1, Instruction.query :: czs (tOf n) b⟩

def encInstr : Instruction → Str
  | .z w => encNat 0 ++ encNat w
  | .cz u v => encNat 1 ++ encNat u ++ encNat v
  | .query => encNat 2

def encProg (p : Program) : Str :=
  encNat p.wires ++ encNat p.body.length ++ (p.body.map encInstr).flatten

theorem readNat_encNat (k : ℕ) (s : Str) : readNat (encNat k ++ s) = some (k, s) := by
  induction k with
  | zero => simp [encNat, readNat]
  | succ k ih =>
    simp only [encNat, List.append_assoc, List.singleton_append] at ih ⊢
    simp [List.replicate_succ, readNat, ih]

theorem readInstruction_enc (i : Instruction) (s : Str) :
    readInstruction (encInstr i ++ s) = some (i, s) := by
  cases i with
  | z w => simp [encInstr, readInstruction, List.append_assoc, readNat_encNat]
  | cz u v => simp [encInstr, readInstruction, List.append_assoc, readNat_encNat]
  | query => simp [encInstr, readInstruction, readNat_encNat]

theorem readInstructions_enc (l : List Instruction) (s : Str) :
    readInstructions l.length ((l.map encInstr).flatten ++ s) = some (l, s) := by
  induction l with
  | nil => simp [readInstructions]
  | cons i l ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc]
    simp [readInstructions, readInstruction_enc, ih]

theorem decode_encProg (p : Program) : decode (encProg p) = some p := by
  have := readInstructions_enc p.body []
  simp only [List.append_nil] at this
  simp only [decode, encProg, List.append_assoc, readNat_encNat]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [readNat_encNat]
  simp [this]

end IQPSol

-- ===== Decider =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity

/-- Automaton state: phase, n mod 8, b, z0, weight mod 4. -/
abbrev St := Fin 5 × Fin 8 × Bool × Bool × Fin 4

def δ (v : St) (x : Bool) : St :=
  match v with
  | (0, k, b, z, w) => if x then (0, k+1, b, z, w) else (1, k, b, z, w)
  | (1, k, _, z, w) => (2, k, x, z, w)
  | (2, k, b, z, w) => if x then (2, k, b, z, w) else (3, k, b, z, w)
  | (3, k, b, _, w) => (4, k, b, x, w)
  | (4, k, b, z, w) => (4, k, b, z, if x then w+1 else w)

/-- decision from n mod 8, branch, z0, weight mod 4 -/
def decide' (k : Fin 8) (b z : Bool) (w : Fin 4) : Bool :=
  let tm : ℕ := if k.val % 2 = 1 then k.val else (k.val + 1) % 8
  let e : ℕ := ((tm - 1) / 2 + 4 - w.val) % 4
  let pos : Bool := if b then (e = 0 ∨ e = 3) else (e = 0 ∨ e = 1)
  pos == !z

def result (v : St) : Bool := decide' v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2

abbrev DK := Bool
abbrev DΓ : DK → Type := fun _ => Bool

def dcode : Unit → Turing.TM2.Stmt DΓ Unit (St × Bool) := fun _ =>
  Turing.TM2.Stmt.pop false (fun v o => match o with
      | some x => (δ v.1 x, false)
      | none => (v.1, true))
    (Turing.TM2.Stmt.branch (fun v => v.2)
      (Turing.TM2.Stmt.push true (fun v => result v.1) Turing.TM2.Stmt.halt)
      (Turing.TM2.Stmt.goto (fun _ => ())))

theorem drun (l : List Bool) (v : St) (S : ∀ k : DK, List (DΓ k)) (hS : S false = l) :
    (flip bind (Turing.TM2.step dcode))^[l.length]
      (some ⟨some (), (v, false), S⟩) =
      some ⟨some (), (l.foldl δ v, false), Function.update S false []⟩ := by
  induction l generalizing v S with
  | nil =>
    simp only [List.length_nil, Function.iterate_zero, id_eq, List.foldl_nil]
    congr
    funext k
    by_cases hk : k = false
    · subst hk; simp [hS]
    · simp [Function.update_of_ne hk]
  | cons x l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : (flip bind (Turing.TM2.step dcode)) (some ⟨some (), (v, false), S⟩) =
        some ⟨some (), (δ v x, false), Function.update S false l⟩ := by
      simp [flip, dcode, Turing.TM2.step, Turing.TM2.stepAux, hS]
    rw [hstep, ih (δ v x) _ (by simp)]
    simp [List.foldl_cons]

def v0 : St := (0, 0, false, false, 0)

theorem decider_exists : ∃ a : Str → Str, PolyTimeComputable a ∧
    ∀ s, a s = [result (s.foldl δ v0)] := by
  obtain ⟨u, hu, hout⟩ := QAlgorithms.DeWolf.clocked_tm2_polytime (K := DK) (Γ := DΓ)
    false true dcode () 1 1 (v0, false) (Equiv.refl Bool) (Equiv.refl Bool)
    (I := Str) id (fun s => [result (s.foldl δ v0)]) (by
      intro s
      refine ⟨s.length, by simp, ?_⟩
      refine ⟨⟨none, (s.foldl δ v0, true),
        Function.update (Function.update (Function.update (fun k => ([] : List (DΓ k))) false
          (s.map (Equiv.refl Bool).symm)) false []) true [result (s.foldl δ v0)]⟩, ?_, rfl, ?_⟩
      · rw [Function.iterate_succ_apply', drun s v0 _ (by simp)]
        simp [flip, dcode, Turing.TM2.step, Turing.TM2.stepAux]
      · simp)
  exact ⟨u, hu, hout⟩

end IQPSol

-- ===== GenBase =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity Turing

/-- stacks: 0 inp, 1 out, 2 J, 3 I, 4 T, 5 Kc, 6 N -/
abbrev GK := Fin 7
/-- labels: 0 A0, 1 A1, 2 B0, 3 B1, 4 B2, 5 R0, 6 E0, 7 E1, 8 E2, 9 E3, 10 E4, 11 E5, 12 E6,
13 C0, 14 C1, 15 C2, 16 C3 -/
abbrev Lbl := Fin 17

structure GS where
  reg : Option Bool
  b : Bool
  par : Bool
  fin : Bool
  deriving DecidableEq

def GS.equiv : GS ≃ Option Bool × Bool × Bool × Bool where
  toFun v := (v.reg, v.b, v.par, v.fin)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv v := rfl
  right_inv x := rfl

instance : Fintype GS := Fintype.ofEquiv _ GS.equiv.symm

abbrev GΓ : GK → Type := fun _ => Bool

abbrev GStmt := TM2.Stmt GΓ Lbl GS

def setReg (v : GS) (o : Option Bool) : GS := { v with reg := o }

def loopStmt (src : GK) (ds : List GK) (self next : Lbl) : GStmt :=
  TM2.Stmt.pop src setReg
    (TM2.Stmt.branch (fun v => v.reg.isSome)
      (ds.foldr (fun d q => TM2.Stmt.push d (fun _ => true) q) (TM2.Stmt.goto fun _ => self))
      (TM2.Stmt.goto fun _ => next))

def gcode (l : Lbl) : GStmt :=
  match l with
  | 0 => TM2.Stmt.pop (0 : GK) setReg
      (TM2.Stmt.branch (fun v => v.reg == some true)
        (TM2.Stmt.push (2 : GK) (fun _ => true) (TM2.Stmt.push (6 : GK) (fun _ => true)
          (TM2.Stmt.load (fun v => { v with par := !v.par }) (TM2.Stmt.goto fun _ => (0 : Lbl)))))
        (TM2.Stmt.goto fun _ => (1 : Lbl)))
  | 1 => TM2.Stmt.pop (0 : GK) (fun v o => { v with b := o.getD false })
      (TM2.Stmt.branch (fun v => !v.par)
        (TM2.Stmt.push (2 : GK) (fun _ => true) (TM2.Stmt.push (6 : GK) (fun _ => true)
          (TM2.Stmt.goto fun _ => (2 : Lbl))))
        (TM2.Stmt.goto fun _ => (2 : Lbl)))
  | 2 => TM2.Stmt.pop (2 : GK) setReg
      (TM2.Stmt.branch (fun v => v.reg.isSome) (TM2.Stmt.goto fun _ => (3 : Lbl))
        (TM2.Stmt.goto fun _ => (13 : Lbl)))
  | 3 => loopStmt (2 : GK) [(3 : GK), (4 : GK)] (3 : Lbl) (4 : Lbl)
  | 4 => loopStmt (4 : GK) [(2 : GK)] (4 : Lbl) (5 : Lbl)
  | 5 => TM2.Stmt.peek (3 : GK) setReg
      (TM2.Stmt.branch (fun v => v.reg.isSome) (TM2.Stmt.goto fun _ => (6 : Lbl))
        (TM2.Stmt.branch (fun v => v.b)
          (TM2.Stmt.load (fun v => { v with fin := true }) (TM2.Stmt.goto fun _ => (6 : Lbl)))
          (TM2.Stmt.goto fun _ => (2 : Lbl))))
  | 6 => TM2.Stmt.push (1 : GK) (fun _ => false) (TM2.Stmt.push (1 : GK) (fun _ => true)
      (TM2.Stmt.goto fun _ => (7 : Lbl)))
  | 7 => loopStmt (2 : GK) [(1 : GK), (4 : GK)] (7 : Lbl) (8 : Lbl)
  | 8 => loopStmt (4 : GK) [(2 : GK)] (8 : Lbl) (9 : Lbl)
  | 9 => TM2.Stmt.push (1 : GK) (fun _ => false) (TM2.Stmt.goto fun _ => (10 : Lbl))
  | 10 => loopStmt (3 : GK) [(1 : GK), (4 : GK)] (10 : Lbl) (11 : Lbl)
  | 11 => loopStmt (4 : GK) [(3 : GK)] (11 : Lbl) (12 : Lbl)
  | 12 => TM2.Stmt.push (1 : GK) (fun _ => false) (TM2.Stmt.push (1 : GK) (fun _ => true)
      (TM2.Stmt.push (5 : GK) (fun _ => true)
        (TM2.Stmt.branch (fun v => v.fin)
          (TM2.Stmt.load (fun v => { v with fin := false }) (TM2.Stmt.goto fun _ => (2 : Lbl)))
          (TM2.Stmt.pop (3 : GK) setReg (TM2.Stmt.goto fun _ => (5 : Lbl))))))
  | 13 => TM2.Stmt.push (1 : GK) (fun _ => false) (TM2.Stmt.push (1 : GK) (fun _ => true)
      (TM2.Stmt.push (1 : GK) (fun _ => true) (TM2.Stmt.push (5 : GK) (fun _ => true)
        (TM2.Stmt.push (1 : GK) (fun _ => false) (TM2.Stmt.goto fun _ => (14 : Lbl))))))
  | 14 => loopStmt (5 : GK) [(1 : GK)] (14 : Lbl) (15 : Lbl)
  | 15 => TM2.Stmt.push (1 : GK) (fun _ => false) (TM2.Stmt.push (1 : GK) (fun _ => true)
      (TM2.Stmt.goto fun _ => (16 : Lbl)))
  | _ => TM2.Stmt.pop (6 : GK) setReg
      (TM2.Stmt.branch (fun v => v.reg.isSome)
        (TM2.Stmt.push (1 : GK) (fun _ => true) (TM2.Stmt.goto fun _ => (16 : Lbl)))
        TM2.Stmt.halt)

abbrev GCfg := TM2.Cfg GΓ Lbl GS

def Run (a b : GCfg) (k : ℕ) : Prop :=
  (flip bind (TM2.step gcode))^[k] (some a) = some b

theorem Run.refl (a : GCfg) : Run a a 0 := rfl

theorem Run.trans {a b c : GCfg} {k k' : ℕ} (h1 : Run a b k) (h2 : Run b c k') :
    Run a c (k + k') := by
  unfold Run at *
  rw [add_comm, Function.iterate_add_apply, h1, h2]

theorem Run.single {l : Lbl} {v : GS} {S : ∀ k, List (GΓ k)} {c : GCfg}
    (h : TM2.stepAux (gcode l) v S = c) : Run ⟨some l, v, S⟩ c 1 := by
  simp [Run, flip, TM2.step, h]

theorem Run.mono {a b : GCfg} {k k' : ℕ} (h : Run a b k) (hk : k = k') : Run a b k' := hk ▸ h

/-- stacks as an explicit tuple -/
def mk (i o j ii tt kc nn : List Bool) : ∀ k : GK, List (GΓ k) := ![i, o, j, ii, tt, kc, nn]

section upd
variable (i o j ii tt kc nn v : List Bool)
@[simp] theorem upd0 : Function.update (mk i o j ii tt kc nn) 0 v = mk v o j ii tt kc nn := by
  funext k; fin_cases k <;> rfl
@[simp] theorem upd1 : Function.update (mk i o j ii tt kc nn) 1 v = mk i v j ii tt kc nn := by
  funext k; fin_cases k <;> rfl
@[simp] theorem upd2 : Function.update (mk i o j ii tt kc nn) 2 v = mk i o v ii tt kc nn := by
  funext k; fin_cases k <;> rfl
@[simp] theorem upd3 : Function.update (mk i o j ii tt kc nn) 3 v = mk i o j v tt kc nn := by
  funext k; fin_cases k <;> rfl
@[simp] theorem upd4 : Function.update (mk i o j ii tt kc nn) 4 v = mk i o j ii v kc nn := by
  funext k; fin_cases k <;> rfl
@[simp] theorem upd5 : Function.update (mk i o j ii tt kc nn) 5 v = mk i o j ii tt v nn := by
  funext k; fin_cases k <;> rfl
@[simp] theorem upd6 : Function.update (mk i o j ii tt kc nn) 6 v = mk i o j ii tt kc v := by
  funext k; fin_cases k <;> rfl
@[simp] theorem mk0 : mk i o j ii tt kc nn 0 = i := rfl
@[simp] theorem mk1 : mk i o j ii tt kc nn 1 = o := rfl
@[simp] theorem mk2 : mk i o j ii tt kc nn 2 = j := rfl
@[simp] theorem mk3 : mk i o j ii tt kc nn 3 = ii := rfl
@[simp] theorem mk4 : mk i o j ii tt kc nn 4 = tt := rfl
@[simp] theorem mk5 : mk i o j ii tt kc nn 5 = kc := rfl
@[simp] theorem mk6 : mk i o j ii tt kc nn 6 = nn := rfl
end upd

def pushAll (ds : List GK) (S : ∀ k, List (GΓ k)) : ∀ k, List (GΓ k) :=
  ds.foldr (fun d S => Function.update S d (true :: S d)) S

theorem stepAux_pushAll (ds : List GK) (q : GStmt) (v : GS) (S : ∀ k, List (GΓ k)) :
    TM2.stepAux (ds.foldr (fun d q => TM2.Stmt.push d (fun _ => true) q) q) v S =
      TM2.stepAux q v (pushAll ds.reverse S) := by
  induction ds generalizing S with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldr_cons, TM2.stepAux, ih, pushAll, List.reverse_cons, List.foldr_append,
      List.foldr_cons, List.foldr_nil]

theorem pushAll_apply (ds : List GK) (S : ∀ k, List (GΓ k)) (k : GK) :
    pushAll ds S k = List.replicate (ds.count k) true ++ S k := by
  induction ds with
  | nil => simp [pushAll]
  | cons d ds ih =>
    simp only [pushAll, List.foldr_cons] at ih ⊢
    by_cases h : k = d
    · subst h; simp [ih, List.count_cons, List.replicate_succ]
    · rw [Function.update_of_ne h, ih, List.count_cons_of_ne (Ne.symm h)]

/-- generic loop: pop `src` until empty, pushing `true` on each of `ds`. -/
theorem loop_run (l next : Lbl) (src : GK) (ds : List GK) (hl : gcode l = loopStmt src ds l next)
    (hsrc : src ∉ ds) (a : ℕ) (S : ∀ k, List (GΓ k)) (hS : S src = List.replicate a true)
    (v : GS) :
    Run ⟨some l, v, S⟩ ⟨some next, setReg v none, fun k => if k = src then [] else
          List.replicate (a * ds.count k) true ++ S k⟩ (a + 1) := by
  induction a generalizing S v with
  | zero =>
    apply Run.single
    rw [hl]
    simp only [loopStmt, TM2.stepAux, hS, List.replicate_zero, List.head?_nil, setReg]
    simp only [Option.isSome_none, cond_false, TM2.stepAux, TM2.Cfg.mk.injEq, true_and]
    funext k
    by_cases hk : k = src
    · subst hk; simp
    · simp [hk, Function.update_of_ne hk]
  | succ a ih =>
    have h1 : Run ⟨some l, v, S⟩ ⟨some l, setReg v (some true),
        pushAll ds.reverse (Function.update S src (List.replicate a true))⟩ 1 := by
      apply Run.single
      rw [hl]
      simp only [loopStmt, TM2.stepAux, hS, List.replicate_succ, List.head?_cons, List.tail_cons]
      simp only [setReg, Option.isSome_some, cond_true]
      rw [stepAux_pushAll]
      rfl
    have h2 := ih (pushAll ds.reverse (Function.update S src (List.replicate a true)))
      (by rw [pushAll_apply]; simp [List.count_reverse, List.count_eq_zero_of_not_mem hsrc])
      (setReg v (some true))
    have h := h1.trans h2
    rw [show 1 + (a + 1) = a + 1 + 1 by omega] at h
    convert h using 2
    · simp [setReg]
    · funext k
      by_cases hk : k = src
      · simp [hk]
      · simp only [hk, if_false, pushAll_apply, List.count_reverse, Function.update_of_ne hk,
          ← List.append_assoc, ← List.replicate_add]
        congr 2
        ring

end IQPSol

-- ===== GenRun =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity Turing IQPForrelation832.SingleQuery

local notation "rep" => List.replicate

def RunLe (a b : GCfg) (K : ℕ) : Prop := ∃ k ≤ K, Run a b k

theorem Run.le {a b : GCfg} {k K : ℕ} (h : Run a b k) (hk : k ≤ K) : RunLe a b K := ⟨k, hk, h⟩

theorem RunLe.trans {a b c : GCfg} {K K' : ℕ} (h1 : RunLe a b K) (h2 : RunLe b c K') :
    RunLe a c (K + K') := by
  obtain ⟨k, hk, h⟩ := h1
  obtain ⟨k', hk', h'⟩ := h2
  exact ⟨k + k', by omega, h.trans h'⟩

theorem RunLe.mono {a b : GCfg} {K K' : ℕ} (h : RunLe a b K) (hK : K ≤ K') : RunLe a b K' := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, by omega, h⟩

section loops
variable (a : ℕ) (i o j ii tt kc nn : List Bool) (v : GS)

theorem runB1 : Run ⟨some 3, v, mk i o (rep a true) ii tt kc nn⟩
    ⟨some 4, setReg v none, mk i o [] (rep a true ++ ii) (rep a true ++ tt) kc nn⟩ (a + 1) := by
  have h := loop_run 3 4 2 [3, 4] rfl (by decide) a (mk i o (rep a true) ii tt kc nn) rfl v
  convert h using 3
  rename_i k; fin_cases k <;> simp

theorem runB2 : Run ⟨some 4, v, mk i o j ii (rep a true) kc nn⟩
    ⟨some 5, setReg v none, mk i o (rep a true ++ j) ii [] kc nn⟩ (a + 1) := by
  have h := loop_run 4 5 4 [2] rfl (by decide) a (mk i o j ii (rep a true) kc nn) rfl v
  convert h using 3
  rename_i k; fin_cases k <;> simp

theorem runE1 : Run ⟨some 7, v, mk i o (rep a true) ii tt kc nn⟩
    ⟨some 8, setReg v none, mk i (rep a true ++ o) [] ii (rep a true ++ tt) kc nn⟩ (a + 1) := by
  have h := loop_run 7 8 2 [1, 4] rfl (by decide) a (mk i o (rep a true) ii tt kc nn) rfl v
  convert h using 3
  rename_i k; fin_cases k <;> simp

theorem runE2 : Run ⟨some 8, v, mk i o j ii (rep a true) kc nn⟩
    ⟨some 9, setReg v none, mk i o (rep a true ++ j) ii [] kc nn⟩ (a + 1) := by
  have h := loop_run 8 9 4 [2] rfl (by decide) a (mk i o j ii (rep a true) kc nn) rfl v
  convert h using 3
  rename_i k; fin_cases k <;> simp

theorem runE4 : Run ⟨some 10, v, mk i o j (rep a true) tt kc nn⟩
    ⟨some 11, setReg v none, mk i (rep a true ++ o) j [] (rep a true ++ tt) kc nn⟩ (a + 1) := by
  have h := loop_run 10 11 3 [1, 4] rfl (by decide) a (mk i o j (rep a true) tt kc nn) rfl v
  convert h using 3
  rename_i k; fin_cases k <;> simp

theorem runE5 : Run ⟨some 11, v, mk i o j ii (rep a true) kc nn⟩
    ⟨some 12, setReg v none, mk i o j (rep a true ++ ii) [] kc nn⟩ (a + 1) := by
  have h := loop_run 11 12 4 [3] rfl (by decide) a (mk i o j ii (rep a true) kc nn) rfl v
  convert h using 3
  rename_i k; fin_cases k <;> simp

theorem runC1 : Run ⟨some 14, v, mk i o j ii tt (rep a true) nn⟩
    ⟨some 15, setReg v none, mk i (rep a true ++ o) j ii tt [] nn⟩ (a + 1) := by
  have h := loop_run 14 15 5 [1] rfl (by decide) a (mk i o j ii tt (rep a true) nn) rfl v
  convert h using 3
  rename_i k; fin_cases k <;> simp

theorem runC3 : ∃ v' : GS, Run ⟨some 16, v, mk i o j ii tt kc (rep a true)⟩
    ⟨none, v', mk i (rep a true ++ o) j ii tt kc []⟩ (a + 1) := by
  induction a generalizing o v with
  | zero =>
    refine ⟨setReg v none, Run.single ?_⟩
    simp [gcode, TM2.stepAux, setReg]
  | succ a ih =>
    obtain ⟨v', h⟩ := ih (true :: o) (setReg v (some true))
    refine ⟨v', ?_⟩
    have h1 : Run ⟨some 16, v, mk i o j ii tt kc (rep (a+1) true)⟩
        ⟨some 16, setReg v (some true), mk i (true :: o) j ii tt kc (rep a true)⟩ 1 := by
      apply Run.single
      simp [gcode, TM2.stepAux, setReg, List.replicate_succ]
    have h2 := h1.trans h
    rw [show 1 + (a + 1) = a + 1 + 1 by omega] at h2
    convert h2 using 3
    simp [List.replicate_succ']
end loops

theorem encInstr_cz (u v : ℕ) (o : List Bool) :
    encInstr (.cz u (v+1)) ++ o =
      true :: false :: rep u true ++ false :: rep v true ++ true :: false :: o := by
  simp [encInstr, encNat, List.replicate_succ', List.append_assoc]

theorem runEmit (jj ii : ℕ) (i o kc nn : List Bool) (v : GS) :
    ∃ v' : GS, v'.b = v.b ∧ v'.par = v.par ∧ v'.fin = false ∧
      Run ⟨some 6, v, mk i o (rep jj true) (rep ii true) [] kc nn⟩
        ⟨some (if v.fin then 2 else 5), v', mk i (encInstr (.cz ii (jj+1)) ++ o) (rep jj true)
          (if v.fin then rep ii true else rep (ii-1) true) [] (true :: kc) nn⟩
        (2*jj + 2*ii + 7) := by
  have h0 : Run ⟨some 6, v, mk i o (rep jj true) (rep ii true) [] kc nn⟩
      ⟨some 7, v, mk i (true :: false :: o) (rep jj true) (rep ii true) [] kc nn⟩ 1 := by
    apply Run.single; simp [gcode, TM2.stepAux]
  have h1 := runE1 jj i (true :: false :: o) (rep ii true) [] kc nn v
  simp only [List.append_nil] at h1
  have h2 := runE2 jj i (rep jj true ++ true :: false :: o) [] (rep ii true) kc nn (setReg v none)
  simp only [List.append_nil] at h2
  have h3 : Run ⟨some 9, setReg (setReg v none) none,
        mk i (rep jj true ++ true :: false :: o) (rep jj true) (rep ii true) [] kc nn⟩
      ⟨some 10, setReg (setReg v none) none,
        mk i (false :: (rep jj true ++ true :: false :: o)) (rep jj true) (rep ii true) [] kc nn⟩
      1 := by
    apply Run.single; simp [gcode, TM2.stepAux]
  have h4 := runE4 ii i (false :: (rep jj true ++ true :: false :: o)) (rep jj true) [] kc nn
    (setReg (setReg v none) none)
  simp only [List.append_nil] at h4
  have h5 := runE5 ii i (rep ii true ++ false :: (rep jj true ++ true :: false :: o))
    (rep jj true) [] kc nn (setReg (setReg (setReg v none) none) none)
  simp only [List.append_nil] at h5
  have hc := (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5)
  rw [encInstr_cz]
  cases hf : v.fin with
  | true =>
    refine ⟨{ setReg (setReg (setReg (setReg v none) none) none) none with fin := false },
      by simp [setReg], by simp [setReg], rfl, ?_⟩
    have h6 : Run ⟨some 12, setReg (setReg (setReg (setReg v none) none) none) none,
        mk i (rep ii true ++ false :: (rep jj true ++ true :: false :: o)) (rep jj true)
          (rep ii true) [] kc nn⟩
        ⟨some 2, { setReg (setReg (setReg (setReg v none) none) none) none with fin := false },
          mk i (true :: false :: rep ii true ++ false :: rep jj true ++ true :: false :: o)
          (rep jj true) (rep ii true) [] (true :: kc) nn⟩ 1 := by
      apply Run.single; simp [gcode, TM2.stepAux, setReg, hf]
    have := hc.trans h6
    simp only [if_true]
    exact this.mono (by omega)
  | false =>
    refine ⟨setReg (setReg (setReg (setReg v none) none) none) (rep ii true).head?,
      by simp [setReg], by simp [setReg], by simp [setReg, hf], ?_⟩
    have h6 : Run ⟨some 12, setReg (setReg (setReg (setReg v none) none) none) none,
        mk i (rep ii true ++ false :: (rep jj true ++ true :: false :: o)) (rep jj true)
          (rep ii true) [] kc nn⟩
        ⟨some 5, setReg (setReg (setReg (setReg v none) none) none) (rep ii true).head?,
          mk i (true :: false :: rep ii true ++ false :: rep jj true ++ true :: false :: o)
          (rep jj true) (rep (ii - 1) true) [] (true :: kc) nn⟩ 1 := by
      apply Run.single; simp [gcode, TM2.stepAux, setReg, hf, List.tail_replicate]
    have := hc.trans h6
    simp only [Bool.false_eq_true, if_false]
    exact this.mono (by omega)

def rowEnc (ii jj : ℕ) (b : Bool) : List Bool :=
  ((rowIdx ii b).map (fun u => encInstr (.cz u (jj+1)))).flatten

theorem runInner (jj : ℕ) (i nn : List Bool) : ∀ (ii : ℕ) (o kc : List Bool) (v : GS),
    v.fin = false → ∃ v' : GS, v'.b = v.b ∧ v'.par = v.par ∧ v'.fin = false ∧
      RunLe ⟨some 5, v, mk i o (rep jj true) (rep ii true) [] kc nn⟩
        ⟨some 2, v', mk i (rowEnc ii jj v.b ++ o) (rep jj true) [] []
          (rep (rowIdx ii v.b).length true ++ kc) nn⟩
        ((ii+1) * (2*jj + 2*ii + 8)) := by
  intro ii
  induction ii with
  | zero =>
    intro o kc v hv
    cases hb : v.b with
    | true =>
      have h0 : Run ⟨some 5, v, mk i o (rep jj true) (rep 0 true) [] kc nn⟩
          ⟨some 6, { setReg v none with fin := true }, mk i o (rep jj true) (rep 0 true) [] kc nn⟩
          1 := by
        apply Run.single; simp [gcode, TM2.stepAux, setReg, hb]
      obtain ⟨v', hb', hp', hf', h1⟩ := runEmit jj 0 i o kc nn { setReg v none with fin := true }
      refine ⟨v', by simp [hb', setReg, hb], by simp [hp', setReg], hf', ?_⟩
      have := h0.trans h1
      simp only [if_true] at this
      refine ⟨1 + (2 * jj + 2 * 0 + 7), by omega, ?_⟩
      convert this using 4 <;> simp [rowEnc, rowIdx]
    | false =>
      refine ⟨setReg v none, by simp [setReg, hb], by simp [setReg], by simp [setReg, hv], ?_⟩
      refine (Run.single ?_).le (by omega)
      simp [gcode, TM2.stepAux, setReg, hb, rowEnc, rowIdx]
  | succ ii ih =>
    intro o kc v hv
    have h0 : Run ⟨some 5, v, mk i o (rep jj true) (rep (ii+1) true) [] kc nn⟩
        ⟨some 6, setReg v (some true), mk i o (rep jj true) (rep (ii+1) true) [] kc nn⟩ 1 := by
      apply Run.single; simp [gcode, TM2.stepAux, setReg, List.replicate_succ]
    obtain ⟨v2, hb2, hp2, hf2, h1⟩ := runEmit jj (ii+1) i o kc nn (setReg v (some true))
    have hfv : (setReg v (some true)).fin = false := by simp [setReg, hv]
    simp only [hfv, Bool.false_eq_true, if_false, Nat.add_sub_cancel] at h1
    obtain ⟨v3, hb3, hp3, hf3, h2⟩ := ih (encInstr (.cz (ii+1) (jj+1)) ++ o) (true :: kc) v2 hf2
    refine ⟨v3, by rw [hb3, hb2]; rfl, by rw [hp3, hp2]; rfl, hf3, ?_⟩
    have := ((h0.le le_rfl).trans (h1.le le_rfl)).trans h2
    have hb2' : v2.b = v.b := by rw [hb2]; rfl
    rw [hb2'] at this
    have h := this.mono (K' := ((ii+1)+1) * (2*jj + 2*(ii+1) + 8)) (by nlinarith)
    have e1 : rowEnc (ii+1) jj v.b ++ o = rowEnc ii jj v.b ++ (encInstr (.cz (ii+1) (jj+1)) ++ o) := by
      simp [rowEnc, rowIdx, List.map_append, List.flatten_append, List.append_assoc]
    have e2 : rep (rowIdx (ii+1) v.b).length true ++ kc = rep (rowIdx ii v.b).length true ++ true :: kc := by
      simp [rowIdx, List.replicate_succ', List.append_assoc]
    rw [e1, e2]
    exact h

theorem runRow (jj : ℕ) (i o kc nn : List Bool) (v : GS) (hv : v.fin = false) :
    ∃ v' : GS, v'.b = v.b ∧ v'.par = v.par ∧ v'.fin = false ∧
      RunLe ⟨some 2, v, mk i o (rep (jj+1) true) [] [] kc nn⟩
        ⟨some 2, v', mk i (rowEnc jj jj v.b ++ o) (rep jj true) [] []
          (rep (rowIdx jj v.b).length true ++ kc) nn⟩
        (11 * (jj+1)^2) := by
  have h0 : Run ⟨some 2, v, mk i o (rep (jj+1) true) [] [] kc nn⟩
      ⟨some 3, setReg v (some true), mk i o (rep jj true) [] [] kc nn⟩ 1 := by
    apply Run.single; simp [gcode, TM2.stepAux, setReg, List.replicate_succ]
  have h1 := runB1 jj i o [] [] kc nn (setReg v (some true))
  simp only [List.append_nil] at h1
  have h2 := runB2 jj i o [] (rep jj true) kc nn (setReg (setReg v (some true)) none)
  simp only [List.append_nil] at h2
  obtain ⟨v', hb, hp, hf, h3⟩ := runInner jj i nn jj o kc
    (setReg (setReg (setReg v (some true)) none) none) (by simp [setReg, hv])
  refine ⟨v', by rw [hb]; rfl, by rw [hp]; rfl, hf, ?_⟩
  have := (((h0.trans h1).trans h2).le le_rfl).trans h3
  have hb' : (setReg (setReg (setReg v (some true)) none) none).b = v.b := rfl
  rw [hb'] at this
  exact this.mono (by nlinarith)

def czsEnc (j : ℕ) (b : Bool) : List Bool := ((czs j b).map encInstr).flatten

theorem runRows (i nn : List Bool) : ∀ (j : ℕ) (o kc : List Bool) (v : GS), v.fin = false →
    ∃ v' : GS, v'.b = v.b ∧ v'.par = v.par ∧
      RunLe ⟨some 2, v, mk i o (rep j true) [] [] kc nn⟩
        ⟨some 13, v', mk i (czsEnc j v.b ++ o) [] [] [] (rep (czs j v.b).length true ++ kc) nn⟩
        (11 * (j+1)^3) := by
  intro j
  induction j with
  | zero =>
    intro o kc v hv
    refine ⟨setReg v none, rfl, rfl, (Run.single ?_).le (by norm_num)⟩
    simp [gcode, TM2.stepAux, setReg, czsEnc, czs]
  | succ j ih =>
    intro o kc v hv
    obtain ⟨v1, hb1, hp1, hf1, h1⟩ := runRow j i o kc nn v hv
    obtain ⟨v2, hb2, hp2, h2⟩ := ih (rowEnc j j v.b ++ o) (rep (rowIdx j v.b).length true ++ kc)
      v1 hf1
    refine ⟨v2, by rw [hb2, hb1], by rw [hp2, hp1], ?_⟩
    have := h1.trans h2
    rw [hb1] at this
    have e1 : czsEnc (j+1) v.b ++ o = czsEnc j v.b ++ (rowEnc j j v.b ++ o) := by
      simp [czsEnc, czs, rowEnc, List.map_append, List.flatten_append, List.append_assoc,
        List.map_map, Function.comp_def]
    have e2 : rep (czs (j+1) v.b).length true ++ kc =
        rep (czs j v.b).length true ++ (rep (rowIdx j v.b).length true ++ kc) := by
      simp only [czs, List.length_append, List.length_map, List.replicate_add, List.append_assoc]
    rw [e1, e2]
    have key : 11 * (j+1)^2 + 11*(j+1)^3 ≤ 11*(j+1+1)^3 := by ring_nf; nlinarith
    exact this.mono key

theorem runA0 (rest : List Bool) : ∀ (n a : ℕ) (v : GS), ∃ v' : GS, v'.b = v.b ∧ v'.fin = v.fin ∧
    v'.par = (if n % 2 = 1 then !v.par else v.par) ∧
    Run ⟨some 0, v, mk (rep n true ++ false :: rest) [] (rep a true) [] [] [] (rep a true)⟩
      ⟨some 1, v', mk rest [] (rep (a+n) true) [] [] [] (rep (a+n) true)⟩ (n+1) := by
  intro n
  induction n with
  | zero =>
    intro a v
    refine ⟨setReg v (some false), rfl, rfl, by simp [setReg], Run.single ?_⟩
    simp [gcode, TM2.stepAux, setReg]
  | succ n ih =>
    intro a v
    obtain ⟨v', hb, hf, hp, h⟩ := ih (a+1) { setReg v (some true) with par := !v.par }
    refine ⟨v', hb, hf, ?_, ?_⟩
    · rw [hp]
      simp only [setReg]
      split_ifs with h1 h2 h2 <;> simp_all <;> omega
    · have h0 : Run ⟨some 0, v, mk (rep (n+1) true ++ false :: rest) [] (rep a true) [] [] []
          (rep a true)⟩
          ⟨some 0, { setReg v (some true) with par := !v.par },
            mk (rep n true ++ false :: rest) [] (rep (a+1) true) [] [] [] (rep (a+1) true)⟩ 1 := by
        apply Run.single; simp [gcode, TM2.stepAux, setReg, List.replicate_succ]
      have := h0.trans h
      rw [show 1 + (n + 1) = n + 1 + 1 by omega, show a + 1 + n = a + (n+1) by omega] at this
      exact this

theorem czs_length (j : ℕ) (b : Bool) : (czs j b).length ≤ (j+1)^2 := by
  have hr : ∀ i, (rowIdx i b).length ≤ i + 1 := by
    intro i; induction i with
    | zero => cases b <;> simp [rowIdx]
    | succ i ih => simp [rowIdx]; omega
  induction j with
  | zero => simp [czs]
  | succ j ih =>
    simp only [czs, List.length_append, List.length_map]
    have := hr j
    nlinarith

theorem tOf_le (n : ℕ) : tOf n ≤ n + 1 := by unfold tOf; split_ifs <;> omega

theorem generator_run (n : ℕ) (b : Bool) : ∃ cf : GCfg, cf.l = none ∧ cf.stk 1 = encProg (prog n b) ∧
    RunLe ⟨some 0, ⟨none, false, false, false⟩, mk (encNat n ++ [b]) [] [] [] [] [] []⟩ cf
      ((n+1) + 1 + 11 * (n+3)^3 + 1 + ((n+2)^2 + 2) + 1 + (n+2)) := by
  -- phase A
  obtain ⟨v1, hb1, hf1, hp1, hA⟩ := runA0 [b] n 0 ⟨none, false, false, false⟩
  simp only [zero_add, List.replicate_zero] at hA
  have hencn : encNat n ++ [b] = rep n true ++ false :: [b] := by simp [encNat]
  rw [hencn]
  set t := tOf n with ht
  have hA1 : Run ⟨some 1, v1, mk [b] [] (rep n true) [] [] [] (rep n true)⟩
      ⟨some 2, { v1 with b := b }, mk [] [] (rep t true) [] [] [] (rep t true)⟩ 1 := by
    apply Run.single
    have hpar : v1.par = decide (Odd n) := by
      rw [hp1]; simp only [Bool.not_false]
      by_cases ho : Odd n
      · have : n % 2 = 1 := Nat.odd_iff.mp ho
        simp [this, ho]
      · have : n % 2 ≠ 1 := fun h => ho (Nat.odd_iff.mpr h)
        simp [this, ho]
    by_cases ho : Odd n
    · have : t = n := by rw [ht]; unfold tOf; simp [ho]
      rw [this]; simp [gcode, TM2.stepAux, hpar, ho]
    · have : t = n + 1 := by rw [ht]; unfold tOf; simp [ho]
      rw [this]; simp [gcode, TM2.stepAux, hpar, ho, List.replicate_succ]
  -- rows
  obtain ⟨v2, hb2, hp2, hR⟩ := runRows [] (rep t true) t [] [] { v1 with b := b }
    (by simp [hf1])
  simp only [List.append_nil] at hR
  -- phase C
  have hC0 : Run ⟨some 13, v2, mk [] (czsEnc t b) [] [] [] (rep (czs t b).length true) (rep t true)⟩
      ⟨some 14, v2, mk [] (false :: true :: true :: false :: czsEnc t b) [] [] []
        (rep ((czs t b).length + 1) true) (rep t true)⟩ 1 := by
    apply Run.single; simp [gcode, TM2.stepAux, List.replicate_succ]
  have hC1 := runC1 ((czs t b).length + 1) [] (false :: true :: true :: false :: czsEnc t b) [] []
    [] (rep t true) v2
  have hC2 : Run ⟨some 15, setReg v2 none, mk [] (rep ((czs t b).length + 1) true ++
        false :: true :: true :: false :: czsEnc t b) [] [] [] [] (rep t true)⟩
      ⟨some 16, setReg v2 none, mk [] (true :: false :: rep ((czs t b).length + 1) true ++
        false :: true :: true :: false :: czsEnc t b) [] [] [] [] (rep t true)⟩ 1 := by
    apply Run.single; simp [gcode, TM2.stepAux]
  obtain ⟨v3, hC3⟩ := runC3 t [] (true :: false :: rep ((czs t b).length + 1) true ++
        false :: true :: true :: false :: czsEnc t b) [] [] [] [] (setReg v2 none)
  refine ⟨⟨none, v3, mk [] (rep t true ++ (true :: false :: rep ((czs t b).length + 1) true ++
        false :: true :: true :: false :: czsEnc t b)) [] [] [] [] []⟩, rfl, ?_, ?_⟩
  · simp only [mk1, encProg, prog, czsEnc, encNat, List.length_cons, List.map_cons,
      List.flatten_cons, encInstr]
    simp only [ht, List.replicate_succ', List.append_assoc]
    simp
  · have hlen := czs_length t b
    have htl := tOf_le n
    have := (((((((hA.le le_rfl).trans (hA1.le le_rfl)).trans hR).trans (hC0.le le_rfl)).trans
      (hC1.le le_rfl)).trans (hC2.le le_rfl)).trans (hC3.le le_rfl))
    refine this.mono ?_
    rw [← ht] at htl
    have h1 : 11 * (t+1)^3 ≤ 11 * (n+3)^3 := by
      have : t + 1 ≤ n + 3 := by omega
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 3)
    have h2 : (t+1)^2 ≤ (n+2)^2 := Nat.pow_le_pow_left (by omega) 2
    omega

end IQPSol

namespace IQPSol
open QAlgorithms QAlgorithms.Complexity Turing IQPForrelation832.SingleQuery

theorem generator_exists : ∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ n b, g (encNat n ++ [b]) = encProg (prog n b) := by
  obtain ⟨u, hu, hout⟩ := QAlgorithms.DeWolf.clocked_tm2_polytime (K := GK) (Γ := GΓ)
    0 1 gcode 0 12 4 ⟨none, false, false, false⟩ (Equiv.refl Bool) (Equiv.refl Bool)
    (I := ℕ × Bool) (fun p => encNat p.1 ++ [p.2]) (fun p => encProg (prog p.1 p.2)) (by
      rintro ⟨n, b⟩
      obtain ⟨cf, hl, hs, k, hk, hrun⟩ := generator_run n b
      have hinit : (Function.update (fun k => ([] : List (GΓ k))) 0
          ((encNat n ++ [b]).map (Equiv.refl Bool).symm)) = mk (encNat n ++ [b]) [] [] [] [] [] [] := by
        funext k; fin_cases k <;> simp [mk]
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          simp only [Run, Function.iterate_zero, id_eq, Option.some.injEq] at hrun
          rw [← hrun] at hl; simp at hl
        · exact h0
      refine ⟨k - 1, ?_, cf, ?_, hl, ?_⟩
      · have hlen : (encNat n ++ [b]).length = n + 2 := by simp [encNat]
        rw [hlen, show n + 2 + 12 = n + 14 by omega]
        have h1 : 11 * (n+3)^3 ≤ 11 * (n+14)^3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
        have h2 : (n+2)^2 ≤ (n+14)^2 := Nat.pow_le_pow_left (by omega) 2
        have h3 : 14 * (n+14)^3 ≤ (n+14)^4 := by
          rw [pow_succ]; rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
        have h4 : (n+14)^2 * 14 ≤ (n+14)^3 := by
          rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega)
        have h5 : (n + 14) * 14 ≤ (n+14)^2 := by
          rw [pow_two]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      · rw [hinit, Nat.sub_add_cancel hk1]; exact hrun
      · simp [hs])
  exact ⟨u, hu, fun n b => hout (n, b)⟩

end IQPSol

-- ===== Fourier =====


namespace IQPSol

open IQPForrelation832.SingleQuery Finset

/-- the additive character of `ZMod 2` -/
noncomputable def χ2 (a : ZMod 2) : ℝ := (-1 : ℝ) ^ a.val

theorem χ2_zero : χ2 0 = 1 := by simp [χ2]
theorem χ2_one : χ2 1 = -1 := by
  simp only [χ2]; rw [show (1 : ZMod 2).val = 1 from rfl]; norm_num

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

theorem χ2_add (a b : ZMod 2) : χ2 (a + b) = χ2 a * χ2 b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [χ2_zero, χ2_one]
  rw [show (1 + 1 : ZMod 2) = 0 from rfl, χ2_zero]

theorem χ2_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    χ2 (∑ i ∈ s, f i) = ∏ i ∈ s, χ2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [χ2_zero]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, χ2_add, ih]

theorem χ2_natCast (k : ℕ) : χ2 (k : ZMod 2) = (-1 : ℝ) ^ k := by
  simp only [χ2, ZMod.val_natCast]
  rw [← Nat.mod_add_div k 2, pow_add, pow_mul]; simp

theorem χ2_sq (a : ZMod 2) : χ2 a * χ2 a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp [χ2_zero, χ2_one]

theorem χ2_mul_self_eq (a : ZMod 2) : χ2 a ^ 2 = 1 := by rw [sq, χ2_sq]

theorem character_eq {n : ℕ} (x y : Cube n) : character x y = χ2 (dot x y) := rfl

theorem character_prod {n : ℕ} (x y : Cube n) : character x y = ∏ k, χ2 (x k * y k) := by
  rw [character_eq]; exact χ2_sum _ _

theorem dot_comm {n : ℕ} (x y : Cube n) : dot x y = dot y x := by
  simp [dot, ExtremalForrelation.Nonadaptive.dot, mul_comm]

theorem character_comm {n : ℕ} (x y : Cube n) : character x y = character y x := by
  rw [character_eq, character_eq, dot_comm]

theorem dot_add_left {n : ℕ} (x y z : Cube n) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, ExtremalForrelation.Nonadaptive.dot, add_mul, sum_add_distrib]

theorem character_add_left {n : ℕ} (x y z : Cube n) :
    character (x + y) z = character x z * character y z := by
  rw [character_eq, character_eq, character_eq, dot_add_left, χ2_add]

theorem character_sq {n : ℕ} (x y : Cube n) : character x y * character x y = 1 := by
  rw [character_eq, χ2_sq]

theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube, ExtremalForrelation.Nonadaptive.V]

/-- Character orthogonality (first part of Claim 1). -/
theorem sum_character {n : ℕ} (x : Cube n) :
    (∑ y, character x y) = if x = 0 then (2 : ℝ) ^ n else 0 := by
  have hprod : (∑ y, character x y) = ∏ k, ∑ a : ZMod 2, χ2 (x k * a) := by
    rw [prod_univ_sum, Fintype.piFinset_univ]
    exact sum_congr rfl (fun y _ => character_prod x y)
  rw [hprod]
  split_ifs with hx
  · subst hx; simp [χ2_zero]
  · obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
      by_contra h; push Not at h; exact hx (funext h)
    apply prod_eq_zero (mem_univ k)
    have : x k = 1 := (zmod2_cases (x k)).resolve_left hk
    rw [this]
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
    simp [χ2_zero, χ2_one]

theorem cube_add_eq_zero {n : ℕ} {u w : Cube n} : u + w = 0 ↔ u = w := by
  constructor
  · intro h; funext k; have := congrFun h k
    simp only [Pi.add_apply, Pi.zero_apply] at this
    rcases zmod2_cases (u k) with h1 | h1 <;> rcases zmod2_cases (w k) with h2 | h2 <;>
      simp_all
  · intro h; subst h; funext k; simp only [Pi.add_apply, Pi.zero_apply]
    rcases zmod2_cases (u k) with h1 | h1 <;> rw [h1] <;> decide

theorem sum_character_mul {n : ℕ} (u w : Cube n) :
    (∑ v, character u v * character w v) = if u = w then (2 : ℝ) ^ n else 0 := by
  have : ∀ v, character u v * character w v = character (u + w) v := by
    intro v; rw [character_add_left]
  simp only [this, sum_character]
  congr 1
  apply propext
  exact cube_add_eq_zero

theorem weight_cons {n : ℕ} (x : Cube (n+1)) :
    weight x = (x 0).val + weight (Fin.tail x : Cube n) := by
  simp [weight, Fin.sum_univ_succ, Fin.tail]

theorem weight_cast {n : ℕ} (x : Cube n) : ((weight x : ℕ) : ZMod 2) = ∑ i, x i := by
  simp [weight, Nat.cast_sum, ZMod.natCast_zmod_val]

theorem Q_cons {n : ℕ} (x : Cube (n+1)) :
    Q x = x 0 * ∑ j : Fin n, x j.succ + Q (Fin.tail x : Cube n) := by
  simp only [Q, Fin.sum_univ_succ, lt_self_iff_false, if_false, Fin.succ_pos, if_true,
    Fin.succ_lt_succ_iff, Fin.tail, zero_add, Finset.mul_sum]
  simp [Fin.not_lt_zero]

theorem Q_eq_choose : ∀ {n : ℕ} (x : Cube n), Q x = ((weight x).choose 2 : ZMod 2) := by
  intro n
  induction n with
  | zero => intro x; simp [Q, weight]
  | succ n ih =>
    intro x
    rw [Q_cons, ih, weight_cons]
    have hw : (∑ j : Fin n, x j.succ) = ((weight (Fin.tail x : Cube n) : ℕ) : ZMod 2) := by
      rw [weight_cast]; rfl
    rw [hw]
    rcases zmod2_cases (x 0) with h | h
    · rw [h]; simp
    · rw [h]
      have : (1 : ZMod 2).val = 1 := rfl
      rw [this, add_comm 1, Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast; ring

theorem χ2_Q {n : ℕ} (x : Cube n) : χ2 (Q x) = (-1 : ℝ) ^ ((weight x).choose 2) := by
  rw [Q_eq_choose, χ2_natCast]

/-- sign identity from Proposition 4 -/
theorem χ2_Q_polar {n : ℕ} (x y : Cube n) :
    χ2 (Q x) * χ2 (Q y) * χ2 (Q (x + y)) =
      character x y * χ2 ((weight x : ZMod 2) * (weight y : ZMod 2)) := by
  rw [← χ2_add, ← χ2_add, proposition_4, χ2_add, character_eq]

theorem weight_add_cast {n : ℕ} (x y : Cube n) :
    ((weight (x + y) : ℕ) : ZMod 2) = (weight x : ZMod 2) + (weight y : ZMod 2) := by
  rw [weight_cast, weight_cast, weight_cast, ← sum_add_distrib]; rfl

theorem I_pow_eq (w : ℕ) : (Complex.I : ℂ) ^ w = (-1 : ℂ) ^ (w.choose 2) * Complex.I ^ (w % 2) := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hc : (w+1).choose 2 = w.choose 2 + w := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
    rw [pow_succ, ih, hc, pow_add]
    rcases Nat.even_or_odd w with he | ho
    · have h1 : w % 2 = 0 := Nat.even_iff.mp he
      have h2 : (w+1) % 2 = 1 := by omega
      rw [h1, h2, he.neg_one_pow]; simp
    · have h1 : w % 2 = 1 := Nat.odd_iff.mp ho
      have h2 : (w+1) % 2 = 0 := by omega
      rw [h1, h2, ho.neg_one_pow]; simp [mul_assoc]

theorem neg_one_pow_ofReal (k : ℕ) : (-1 : ℂ) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl

@[simp] theorem re_neg_one_pow (k : ℕ) : ((-1 : ℂ) ^ k).re = (-1 : ℝ) ^ k := by
  rw [neg_one_pow_ofReal, Complex.ofReal_re]

@[simp] theorem im_neg_one_pow (k : ℕ) : ((-1 : ℂ) ^ k).im = 0 := by
  rw [neg_one_pow_ofReal, Complex.ofReal_im]

theorem sigmaOdd_eq {n : ℕ} (y : Cube n) :
    sigmaOdd y = Real.sqrt 2 * ((Complex.I : ℂ) ^ (weight y)).im := by
  have hq : (-1 : ℝ) ^ ((Q y).val) = (-1 : ℝ) ^ ((weight y).choose 2) := χ2_Q y
  rw [I_pow_eq, sigmaOdd, hq]
  split_ifs with h
  · have : weight y % 2 = 1 := Nat.odd_iff.mp h
    rw [this]; simp
  · have : weight y % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h)
    rw [this]; simp

theorem sigmaEven_eq {n : ℕ} (y : Cube n) :
    sigmaEven y = Real.sqrt 2 * ((Complex.I : ℂ) ^ (weight y)).re := by
  have hq : (-1 : ℝ) ^ ((Q y).val) = (-1 : ℝ) ^ ((weight y).choose 2) := χ2_Q y
  rw [I_pow_eq, sigmaEven, hq]
  split_ifs with h
  · have : weight y % 2 = 0 := Nat.even_iff.mp h
    rw [this]; simp
  · have : weight y % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp h)
    rw [this]; simp

theorem weight_eq_card {n : ℕ} (x : Cube n) : weight x = (univ.filter (fun k => x k = 1)).card := by
  rw [weight, card_filter]
  apply sum_congr rfl
  intro k _
  rcases zmod2_cases (x k) with h | h <;> rw [h] <;> rfl

theorem sum_character_Ipow {n : ℕ} (x : Cube n) :
    (∑ y, (character x y : ℂ) * Complex.I ^ (weight y)) =
      (1 + Complex.I) ^ (n - weight x) * (1 - Complex.I) ^ (weight x) := by
  have h1 : ∀ y : Cube n, (character x y : ℂ) * Complex.I ^ (weight y) =
      ∏ k, ((χ2 (x k * y k) : ℂ) * Complex.I ^ (y k).val) := by
    intro y
    rw [prod_mul_distrib, character_prod, Complex.ofReal_prod, weight, prod_pow_eq_pow_sum]
  simp only [h1]
  have h3 := (prod_univ_sum (fun _ => (univ : Finset (ZMod 2)))
    (fun k a => (χ2 (x k * a) : ℂ) * Complex.I ^ a.val)).symm
  rw [Fintype.piFinset_univ] at h3
  rw [h3]
  have h2 : ∀ k, (∑ a : ZMod 2, (χ2 (x k * a) : ℂ) * Complex.I ^ a.val) =
      if x k = 1 then 1 - Complex.I else 1 + Complex.I := by
    intro k
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
    rw [sum_pair (by decide)]
    rcases zmod2_cases (x k) with h | h <;> rw [h] <;>
      simp [χ2_zero, χ2_one, show (1 : ZMod 2).val = 1 from rfl] <;> ring
  simp only [h2]
  rw [prod_ite, prod_const, prod_const, mul_comm, ← weight_eq_card]
  congr 2
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun k => x k = 1)
  rw [← weight_eq_card, card_univ, Fintype.card_fin] at this
  omega

def eIdx (n w : ℕ) : ℕ := ((n - 1) / 2 + 3 * w) % 4

noncomputable def tauO (n w : ℕ) : ℝ := if eIdx n w = 0 ∨ eIdx n w = 1 then 1 else -1
noncomputable def tauE (n w : ℕ) : ℝ := if eIdx n w = 0 ∨ eIdx n w = 3 then 1 else -1

theorem I_pow_mod (m : ℕ) : (Complex.I : ℂ) ^ m = Complex.I ^ (m % 4) := by
  conv_lhs => rw [← Nat.mod_add_div m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, mul_one]

theorem closed_form (k w : ℕ) (hw : w ≤ 2 * k + 1) :
    (1 + Complex.I) ^ (2 * k + 1 - w) * (1 - Complex.I) ^ w =
      (2 : ℂ) ^ k * ((1 + Complex.I) * Complex.I ^ ((k + 3 * w) % 4)) := by
  have hm : (1 - Complex.I) = (1 + Complex.I) * Complex.I ^ 3 := by
    rw [show Complex.I ^ 3 = - Complex.I by rw [pow_succ, pow_two, Complex.I_mul_I]; ring]
    ring_nf; rw [Complex.I_sq]; ring
  rw [hm, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hw, ← pow_mul,
    ← I_pow_mod, pow_succ, pow_mul]
  have h2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by ring_nf; rw [Complex.I_sq]; ring
  rw [h2, mul_pow, pow_add]
  ring

theorem sqrt_two_pow_odd (k : ℕ) : Real.sqrt ((2 : ℝ) ^ (2 * k + 1)) = Real.sqrt 2 * 2 ^ k := by
  rw [pow_succ, mul_comm 2 k, pow_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

theorem realFourier_sigma_aux {n : ℕ} (hn : Odd n) (x : Cube n) (part : ℂ → ℝ)
    (hpart : ∀ (r : ℝ) (z : ℂ), part (r * z) = r * part z)
    (hadd : ∀ s : Finset (Cube n), ∀ f : Cube n → ℂ, part (∑ y ∈ s, f y) = ∑ y ∈ s, part (f y))
    (h : Cube n → ℝ) (hh : ∀ y, h y = Real.sqrt 2 * part (Complex.I ^ (weight y))) :
    realFourier h x = part ((1 + Complex.I) * Complex.I ^ eIdx n (weight x)) := by
  obtain ⟨k, rfl⟩ := hn
  have hw : weight x ≤ 2 * k + 1 := by
    rw [weight_eq_card]; exact (card_filter_le _ _).trans (by simp)
  unfold realFourier
  have : (∑ y, character x y * h y) =
      Real.sqrt 2 * part (∑ y, (character x y : ℂ) * Complex.I ^ (weight y)) := by
    rw [hadd, mul_sum]
    apply sum_congr rfl; intro y _
    rw [hh, hpart]; ring
  rw [this, sum_character_Ipow, closed_form k _ hw]
  rw [show ((2 : ℂ) ^ k) = (((2 : ℝ) ^ k : ℝ) : ℂ) by push_cast; rfl, hpart, sqrt_two_pow_odd]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h3 : (0 : ℝ) < 2 ^ k := by positivity
  unfold eIdx
  rw [show (2 * k + 1 - 1) / 2 = k by omega]
  field_simp

theorem part_values (e : ℕ) (he : e < 4) :
    ((1 + Complex.I) * Complex.I ^ e).im = (if e = 0 ∨ e = 1 then 1 else -1) ∧
    ((1 + Complex.I) * Complex.I ^ e).re = (if e = 0 ∨ e = 3 then 1 else -1) := by
  interval_cases e <;> simp [pow_succ, Complex.mul_re, Complex.mul_im]

theorem realFourier_sigmaOdd {n : ℕ} (hn : Odd n) (x : Cube n) :
    realFourier sigmaOdd x = tauO n (weight x) := by
  rw [realFourier_sigma_aux hn x Complex.im (fun r z => by simp) (fun s f => Complex.im_sum s f)
    sigmaOdd sigmaOdd_eq]
  exact (part_values _ (Nat.mod_lt _ (by norm_num))).1

theorem realFourier_sigmaEven {n : ℕ} (hn : Odd n) (x : Cube n) :
    realFourier sigmaEven x = tauE n (weight x) := by
  rw [realFourier_sigma_aux hn x Complex.re (fun r z => by simp) (fun s f => Complex.re_sum s f)
    sigmaEven sigmaEven_eq]
  exact (part_values _ (Nat.mod_lt _ (by norm_num))).2

end IQPSol

-- ===== FourierB =====


namespace IQPSol

open IQPForrelation832.SingleQuery Finset

noncomputable def Psi {n : ℕ} (f g : Cube n → ℝ) : ℝ := ∑ x, ∑ y, character x y * f x * g y

theorem sqrt_two_pow (m : ℕ) : Real.sqrt ((2 : ℝ) ^ m) = Real.sqrt 2 ^ m := by
  rw [show (2 : ℝ) ^ m = (Real.sqrt 2 ^ m) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sqrt_two_pow_two_mul (m : ℕ) : Real.sqrt 2 ^ (2 * m) = 2 ^ m := by
  rw [pow_mul, sqrt_two_sq]

theorem rpow_neg_half (n : ℕ) : (2 : ℝ) ^ (-(n : ℝ) / 2) = (Real.sqrt 2 ^ n)⁻¹ := by
  rw [neg_div, Real.rpow_neg (by norm_num), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  congr 2; ring

theorem Phi_eq {n : ℕ} (f g : Cube n → ℝ) : Phi f g = (Real.sqrt 2 ^ (3 * n))⁻¹ * Psi f g := by
  show ExtremalForrelation.Nonadaptive.forr f g = _
  unfold ExtremalForrelation.Nonadaptive.forr ExtremalForrelation.Nonadaptive.fourier
  rw [rpow_neg_half]
  have h3 : Real.sqrt 2 ^ (3 * n) = Real.sqrt 2 ^ n * 2 ^ n := by
    rw [show 3 * n = n + 2 * n by ring, pow_add, sqrt_two_pow_two_mul]
  rw [h3, Psi, mul_inv, mul_assoc]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine sum_congr rfl (fun x _ => sum_congr rfl (fun y _ => ?_))
  simp only [character, dot]
  ring

theorem parityPhi_add {n : ℕ} (f g : Cube n → ℝ) :
    parityPhi true f g + parityPhi false f g = Phi f g := by
  rw [Phi_eq, parityPhi, parityPhi, ← mul_add, sqrt_two_pow, Psi, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl; intro x _
  rw [← sum_add_distrib]
  apply sum_congr rfl; intro y _
  have := Nat.mod_two_eq_zero_or_one (weight (x + y))
  rcases this with h | h <;> simp [h]

theorem sum_zmod2 (F : ZMod 2 → ℝ) : (∑ a : ZMod 2, F a) = F 0 + F 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl, sum_pair (by decide)]

theorem sum_cube_snoc {n : ℕ} (F : Cube (n+1) → ℝ) :
    (∑ x, F x) = ∑ a : ZMod 2, ∑ x : Cube n, F (Fin.snoc x a) := by
  rw [← (Fin.snocEquiv (fun _ => ZMod 2)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem character_snoc {n : ℕ} (x y : Cube n) (a c : ZMod 2) :
    character (Fin.snoc x a : Cube (n+1)) (Fin.snoc y c) = character x y * χ2 (a * c) := by
  rw [character_eq, character_eq, ← χ2_add]
  congr 1
  simp [dot, ExtremalForrelation.Nonadaptive.dot, Fin.sum_univ_castSucc]

theorem pad_snoc {n : ℕ} (f : Cube n → ℝ) (x : Cube n) (a : ZMod 2) :
    pad f (Fin.snoc x a : Cube (n+1)) = f x := by
  simp [pad]

theorem Psi_pad {n : ℕ} (f g : Cube n → ℝ) : Psi (pad f) (pad g) = 2 * Psi f g := by
  unfold Psi
  rw [sum_cube_snoc]
  simp only [sum_cube_snoc (fun y => _), character_snoc, pad_snoc]
  simp only [sum_zmod2, zero_mul, one_mul, χ2_zero, χ2_one, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  ring

theorem Phi_pad {n : ℕ} (f g : Cube n → ℝ) : Phi (pad f) (pad g) = Phi f g / Real.sqrt 2 := by
  rw [Phi_eq, Phi_eq, Psi_pad]
  have h : Real.sqrt 2 ^ (3 * (n+1)) = Real.sqrt 2 ^ (3 * n) * 2 * Real.sqrt 2 := by
    rw [show 3 * (n+1) = 3 * n + 2 + 1 by ring, pow_succ, pow_add, sqrt_two_sq]
  rw [h]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  field_simp

theorem sum_comm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (g : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, g a b c) = ∑ b, ∑ c, ∑ a, g a b c := by
  rw [sum_comm]; apply sum_congr rfl; intro b _; rw [sum_comm]

theorem parseval {t : ℕ} (H : Cube t → ℝ) (hH : IsSign H) :
    (∑ v', (∑ v, character v v' * H v) ^ 2) = 2 ^ t * 2 ^ t := by
  have hexp : ∀ v', (∑ v, character v v' * H v) ^ 2 =
      ∑ v, ∑ u, (H v * H u) * (character v v' * character u v') := by
    intro v'
    rw [sq, sum_mul_sum]
    apply sum_congr rfl; intro v _; apply sum_congr rfl; intro u _; ring
  simp only [hexp]
  rw [sum_comm3]
  simp only [← mul_sum]
  have : ∀ v u : Cube t, (∑ v', character v v' * character u v') = if v = u then (2:ℝ)^t else 0 := by
    intro v u
    rw [← sum_character_mul v u]
  simp only [this, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
  have hsq : ∀ v, H v * H v = 1 := by
    intro v; rcases hH v with h | h <;> rw [h] <;> norm_num
  simp only [hsq, one_mul, sum_const, card_univ, card_cube, nsmul_eq_mul]
  push_cast; ring

theorem tau_sum {t : ℕ} (σ τ : Cube t → ℝ) (hτσ : ∀ v, τ v = realFourier σ v) (w : Cube t) :
    (∑ v', τ v' * character w v') = Real.sqrt 2 ^ t * σ w := by
  simp only [hτσ, realFourier, sqrt_two_pow]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  have : ∀ y : Cube t, (∑ v', (Real.sqrt 2 ^ t)⁻¹ * (character v' y * σ y) * character w v') =
      (Real.sqrt 2 ^ t)⁻¹ * σ y * (∑ v', character y v' * character w v') := by
    intro y; rw [mul_sum]; apply sum_congr rfl; intro v' _; rw [character_comm v' y]; ring
  simp only [this, sum_character_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  have h2 : (0 : ℝ) < Real.sqrt 2 ^ t := by positivity
  rw [show (2 : ℝ) ^ t = Real.sqrt 2 ^ t * Real.sqrt 2 ^ t by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]]
  field_simp

theorem core {t : ℕ} (H0 H1 σ τ : Cube t → ℝ) (h0 : IsSign H0) (h1 : IsSign H1)
    (hτσ : ∀ v, τ v = realFourier σ v) :
    (∑ v', ((∑ v, character v v' * H0 v) ^ 2 + (∑ v, character v v' * H1 v) ^ 2 +
      2 * τ v' * ((∑ v, character v v' * H0 v) * (∑ v, character v v' * H1 v)))) =
      2 * (2 ^ t * 2 ^ t) + 2 * Real.sqrt 2 ^ t * ∑ v, ∑ u, H0 v * H1 u * σ (v + u) := by
  rw [sum_add_distrib, sum_add_distrib, parseval H0 h0, parseval H1 h1]
  have hcross : ∀ v', 2 * τ v' * ((∑ v, character v v' * H0 v) * (∑ v, character v v' * H1 v)) =
      2 * ∑ v, ∑ u, H0 v * H1 u * (τ v' * character (v + u) v') := by
    intro v'
    rw [sum_mul_sum]
    simp only [mul_sum]
    apply sum_congr rfl; intro v _
    apply sum_congr rfl; intro u _
    rw [character_add_left]; ring
  simp only [hcross]
  rw [← mul_sum, sum_comm3]
  simp only [← mul_sum, tau_sum σ τ hτσ]
  rw [mul_sum, mul_sum]
  ring_nf
  congr 1
  apply sum_congr rfl; intro v _
  rw [mul_sum]
  congr 1
  apply sum_congr rfl; intro u _
  ring

theorem natCast_zmod2 (k : ℕ) : ((k : ℕ) : ZMod 2) = if k % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp

theorem neg_one_pow_val (a : ZMod 2) : (-1 : ℝ) ^ a.val = χ2 a := rfl

theorem spec_term {t : ℕ} (b : Bool) (F G : Cube t → ℝ) (v u : Cube t) :
    (F v * χ2 (Q v)) * (G u * χ2 (Q u) * (if b then χ2 (weight u : ZMod 2) else 1)) *
      (if b then sigmaEven (v + u) else sigmaOdd (v + u)) =
    Real.sqrt 2 * (if weight (v + u) % 2 = (if !b then 1 else 0) then
      character v u * F v * G u else 0) := by
  have hpol := χ2_Q_polar v u
  have hw := weight_add_cast v u
  rw [natCast_zmod2, natCast_zmod2, natCast_zmod2] at hw
  rw [natCast_zmod2, natCast_zmod2] at hpol
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false, mul_one, Bool.not_false, if_true]
    unfold sigmaOdd
    by_cases ho : Odd (weight (v + u))
    · have h1 : weight (v + u) % 2 = 1 := Nat.odd_iff.mp ho
      rw [if_pos ho, if_pos h1, neg_one_pow_val]
      have hz : (if weight v % 2 = 1 then (1 : ZMod 2) else 0) *
          (if weight u % 2 = 1 then 1 else 0) = 0 := by
        rw [h1] at hw
        rcases Nat.mod_two_eq_zero_or_one (weight v) with hv | hv <;>
        rcases Nat.mod_two_eq_zero_or_one (weight u) with hu | hu <;>
        simp only [hv, hu, if_true, if_false, zero_ne_one, one_ne_zero] at hw ⊢ <;>
        revert hw <;> decide
      rw [hz, χ2_zero] at hpol
      calc F v * χ2 (Q v) * (G u * χ2 (Q u)) * (Real.sqrt 2 * χ2 (Q (v + u)))
          = Real.sqrt 2 * F v * G u * (χ2 (Q v) * χ2 (Q u) * χ2 (Q (v + u))) := by ring
        _ = _ := by rw [hpol]; ring
    · have h1 : ¬ weight (v + u) % 2 = 1 := fun h => ho (Nat.odd_iff.mpr h)
      rw [if_neg ho, if_neg h1]; ring
  | true =>
    simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
    rw [natCast_zmod2 (weight u)]
    unfold sigmaEven
    by_cases he : Even (weight (v + u))
    · have h1 : weight (v + u) % 2 = 0 := Nat.even_iff.mp he
      rw [if_pos he, if_pos h1, neg_one_pow_val]
      have hz' : (if weight v % 2 = 1 then (1 : ZMod 2) else 0) *
          (if weight u % 2 = 1 then 1 else 0) + (if weight u % 2 = 1 then 1 else 0) = 0 := by
        rw [h1] at hw
        rcases Nat.mod_two_eq_zero_or_one (weight v) with hv | hv <;>
        rcases Nat.mod_two_eq_zero_or_one (weight u) with hu | hu <;>
        simp only [hv, hu, if_true, if_false, zero_ne_one, one_ne_zero] at hw ⊢ <;>
        revert hw <;> decide
      have hz : χ2 ((if weight v % 2 = 1 then (1 : ZMod 2) else 0) *
          (if weight u % 2 = 1 then 1 else 0)) * χ2 (if weight u % 2 = 1 then 1 else 0) = 1 := by
        rw [← χ2_add, hz', χ2_zero]
      calc F v * χ2 (Q v) * (G u * χ2 (Q u) * χ2 (if weight u % 2 = 1 then 1 else 0)) *
            (Real.sqrt 2 * χ2 (Q (v + u)))
          = Real.sqrt 2 * F v * G u * (χ2 (Q v) * χ2 (Q u) * χ2 (Q (v + u))) *
            χ2 (if weight u % 2 = 1 then 1 else 0) := by ring
        _ = Real.sqrt 2 * (character v u * F v * G u) *
            (χ2 ((if weight v % 2 = 1 then (1 : ZMod 2) else 0) *
              (if weight u % 2 = 1 then 1 else 0)) * χ2 (if weight u % 2 = 1 then 1 else 0)) := by
            rw [hpol]; ring
        _ = _ := by rw [hz]; ring
    · have h1 : ¬ weight (v + u) % 2 = 0 := fun h => he (Nat.even_iff.mpr h)
      rw [if_neg he, if_neg h1]; ring

theorem spec_sum {t : ℕ} (b : Bool) (F G : Cube t → ℝ) :
    (∑ v, ∑ u, (F v * χ2 (Q v)) * (G u * χ2 (Q u) * (if b then χ2 (weight u : ZMod 2) else 1)) *
      (if b then sigmaEven (v + u) else sigmaOdd (v + u))) =
    Real.sqrt 2 * Real.sqrt 2 ^ (3 * t) * parityPhi (!b) F G := by
  simp only [spec_term, ← mul_sum]
  have h : Real.sqrt 2 ^ (3 * t) ≠ 0 := by positivity
  rw [parityPhi, sqrt_two_pow, mul_assoc, ← mul_assoc (Real.sqrt 2 ^ (3 * t)),
    mul_inv_cancel₀ h, one_mul]

end IQPSol

-- ===== Circuit =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity IQPForrelation832.SingleQuery Finset

theorem mapM_eq_filterMap {α β : Type*} (f : α → Option β) (l : List α)
    (h : ∀ a ∈ l, (f a).isSome) : l.mapM f = some (l.filterMap f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (by simp))
    rw [List.mapM_cons, hb, ih (fun x hx => h x (by simp [hx])), List.filterMap_cons_some hb]
    rfl

theorem prod_filterMap {α β M : Type*} [CommMonoid M] (f : α → Option β) (g : β → M) (l : List α) :
    ((l.filterMap f).map g).prod = (l.map (fun a => match f a with | some b => g b | none => 1)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filterMap_cons]
    cases h : f a with
    | none => simp [ih, h]
    | some b => simp [ih, h]

theorem embedOp_diagonal {k n : ℕ} (d : Qubits k → ℂ) (w : Fin k ↪ Fin n) :
    embedOp (Matrix.diagonal d) w = Matrix.diagonal (fun y => d (y ∘ w)) := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; apply hyz; funext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨b, rfl⟩ := ha; exact congrFun h2 b
      · exact h1 a ha
    · rfl
    · rfl

/-- a list of diagonal steps multiplies to a diagonal matrix -/
theorem unitary_diag {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) (c : OracleCircuit S a m)
    (hc : ∀ s ∈ c, ∃ d, OracleStep.mat orc s = Matrix.diagonal d) :
    OracleCircuit.unitary c orc =
      Matrix.diagonal (fun y => (c.map (fun s => OracleStep.mat orc s y y)).prod) := by
  induction c with
  | nil => simp [OracleCircuit.unitary]
  | cons s c ih =>
    obtain ⟨d, hd⟩ := hc s (by simp)
    have ih' := ih (fun s' hs' => hc s' (by simp [hs']))
    simp only [OracleCircuit.unitary, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one] at ih' ⊢
    rw [ih', hd, Matrix.diagonal_mul_diagonal]
    congr 1; funext y
    simp [Matrix.diagonal_apply, mul_comm]

theorem cz_mat_eq : (controlled pauliZ).submatrix (fun b : Qubits 2 => (b 0, b 1))
    (fun b => (b 0, b 1)) =
    Matrix.diagonal (fun q : Qubits 2 => if q 0 && q 1 then (-1 : ℂ) else 1) := by
  ext x y
  simp only [Matrix.submatrix_apply, controlled, pauliZ, Matrix.of_apply,
    Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; cases hx0 : x 0 <;> cases hx1 : x 1 <;> simp
  · have : ¬ (x 0 = y 0 ∧ x 1 = y 1) := by
      intro ⟨h0, h1⟩; apply hxy; funext i; fin_cases i <;> simp [h0, h1]
    rw [if_neg hxy]
    by_cases h0 : x 0 = y 0
    · have h1 : x 1 ≠ y 1 := fun h1 => this ⟨h0, h1⟩
      rw [if_pos h0]; split_ifs <;> simp_all
    · rw [if_neg h0]

theorem czGate_mat : (Gate.ofMatrix2 (controlled pauliZ)).mat =
    Matrix.diagonal (fun q : Qubits 2 => if q 0 && q 1 then (-1 : ℂ) else 1) := cz_mat_eq

theorem diag_sign_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Bool) :
    Matrix.diagonal (fun q => if p q then (-1 : ℂ) else 1) ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext q
  split_ifs with h <;> simp [h]

theorem czGate_diagUnitary : DiagonalUnitary (Gate.ofMatrix2 (controlled pauliZ)) := by
  refine ⟨?_, ?_⟩
  · show (Gate.ofMatrix2 (controlled pauliZ)).mat ∈ _
    rw [czGate_mat]; exact diag_sign_unitary _
  · intro x y hxy
    rw [czGate_mat]
    exact Matrix.diagonal_apply_ne (fun q : Qubits 2 => if q 0 && q 1 then (-1 : ℂ) else 1) hxy

theorem mem_rowIdx {i : ℕ} {b : Bool} {u : ℕ} (h : u ∈ rowIdx i b) : u ≤ i := by
  induction i with
  | zero => cases b <;> simp [rowIdx] at h; omega
  | succ i ih =>
    simp only [rowIdx, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact (ih h).trans (Nat.le_succ i)
    · omega

theorem mem_czs {t : ℕ} {b : Bool} {ins : Instruction} (h : ins ∈ czs t b) :
    ∃ u v, ins = Instruction.cz u v ∧ u < v ∧ v ≤ t := by
  induction t with
  | zero => simp [czs] at h
  | succ t ih =>
    simp only [czs, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨u, hu, rfl⟩
    · obtain ⟨u, v, h1, h2, h3⟩ := ih h; exact ⟨u, v, h1, h2, by omega⟩
    · exact ⟨u, t+1, rfl, by have := mem_rowIdx hu; omega, le_rfl⟩

/-- the program on `t+1` wires -/
def progT (t : ℕ) (b : Bool) : Program := ⟨t + 1, Instruction.query :: czs t b⟩

theorem prog_eq (n : ℕ) (b : Bool) : prog n b = progT (tOf n) b := rfl

theorem compile_isSome {n t : ℕ} (hnt : n ≤ t) (b : Bool) :
    ∀ ins ∈ (progT t b).body, (compileInstruction n (t+1) ins).isSome := by
  intro ins hins
  simp only [progT, List.mem_cons] at hins
  rcases hins with rfl | hins
  · simp [compileInstruction, show n + 1 ≤ t + 1 by omega]
  · obtain ⟨u, v, rfl, huv, hv⟩ := mem_czs hins
    simp only [compileInstruction]
    rw [dif_pos ⟨by omega, by omega, by omega⟩]; rfl

/-- the compiled circuit -/
noncomputable def circT (n t : ℕ) (b : Bool) : Middle n (t+1) :=
  (progT t b).body.filterMap (compileInstruction n (t+1))

theorem compile_eq {n t : ℕ} (hnt : n ≤ t) (b : Bool) :
    compile n (progT t b) = some (circT n t b) :=
  mapM_eq_filterMap _ _ (compile_isSome hnt b)

theorem circT_isIQP {n t : ℕ} (hnt : n ≤ t) (b : Bool) : IsIQP (circT n t b) := by
  intro s hs
  obtain ⟨ins, hins, hcs⟩ := List.mem_filterMap.mp hs
  simp only [progT, List.mem_cons] at hins
  rcases hins with rfl | hins
  · simp only [compileInstruction, dif_pos (show n + 1 ≤ t + 1 by omega), Option.some.injEq] at hcs
    subst hcs; exact ⟨rfl, rfl⟩
  · obtain ⟨u, v, rfl, huv, hv⟩ := mem_czs hins
    simp only [compileInstruction, dif_pos (show u < t + 1 ∧ v < t + 1 ∧ u ≠ v by omega),
      Option.some.injEq] at hcs
    subst hcs; exact czGate_diagUnitary

theorem circT_queryCount {n t : ℕ} (hnt : n ≤ t) (b : Bool) :
    OracleCircuit.queryCount (circT n t b) 0 = 1 := by
  have hq : compileInstruction n (t+1) Instruction.query = some (.query 0 false none
      ⟨Fin.castLE (show n + 1 ≤ t + 1 by omega), Fin.castLE_injective _⟩ (by simp)) := by
    simp [compileInstruction, show n + 1 ≤ t + 1 by omega]
  unfold circT OracleCircuit.queryCount
  rw [progT, List.filterMap_cons_some hq, List.countP_cons]
  have : List.countP (OracleStep.IsQueryTo 0) ((czs t b).filterMap (compileInstruction n (t+1))) = 0 := by
    rw [List.countP_eq_zero]
    intro s hs
    obtain ⟨ins, hins, hcs⟩ := List.mem_filterMap.mp hs
    obtain ⟨u, v, rfl, huv, hv⟩ := mem_czs hins
    simp only [compileInstruction, dif_pos (show u < t + 1 ∧ v < t + 1 ∧ u ≠ v by omega),
      Option.some.injEq] at hcs
    subst hcs; simp [OracleStep.IsQueryTo]
  rw [this]; simp [OracleStep.IsQueryTo]

end IQPSol

-- ===== Amp =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity IQPForrelation832.SingleQuery Finset

noncomputable def sB {m : ℕ} (z w : Qubits m) : ℝ := if dotBits w z then -1 else 1

theorem hadamardN_apply {m : ℕ} (j i : Qubits m) :
    hadamardN m j i = (((Real.sqrt 2)⁻¹ ^ m * sB j i : ℝ) : ℂ) := by
  simp only [hadamardN, Matrix.of_apply, sB]
  split_ifs <;> push_cast <;> ring

theorem dotBits_zero_left {m : ℕ} (w : Qubits m) : dotBits (fun _ => false) w = false := by
  simp only [dotBits, Bool.false_and]; exact sum_const_zero

theorem run_apply {n m : ℕ} (c : Middle n m) (f g : Cube n → ℝ) (Dr : Qubits m → ℝ)
    (hU : OracleCircuit.unitary c (fun _ => jointOracle f g) = Matrix.diagonal (fun y => (Dr y : ℂ)))
    (z : Qubits m) :
    run c f g z = ((((Real.sqrt 2)⁻¹ ^ m) ^ 2 * ∑ w, sB z w * Dr w : ℝ) : ℂ) := by
  unfold run act zeroKet ket
  rw [hU]
  simp only [EuclideanSpace.single, PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, hadamardN_apply]
  rw [Complex.ofReal_mul, Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl; intro w _
  have : sB w (fun _ => false) = 1 := by simp [sB, dotBits_zero_left]
  rw [this]; push_cast; ring

open Classical in
theorem born_eq {n m : ℕ} (c : Middle n m) (Acc : Qubits m → Prop) (f g : Cube n → ℝ)
    (Dr : Qubits m → ℝ)
    (hU : OracleCircuit.unitary c (fun _ => jointOracle f g) = Matrix.diagonal (fun y => (Dr y : ℂ))) :
    born c Acc f g = ∑ z, if Acc z then (((Real.sqrt 2)⁻¹ ^ m) ^ 2 * ∑ w, sB z w * Dr w) ^ 2 else 0 := by
  unfold born probEvent
  rw [sum_filter]
  apply sum_congr rfl; intro z _
  congr 1
  rw [prob]
  simp only [ket, EuclideanSpace.inner_single_left, map_one, one_mul, run_apply c f g Dr hU,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

noncomputable def sgnB (β : Bool) : ℝ := if β then -1 else 1

theorem sgnB_add (x y : Bool) : sgnB (x + y) = sgnB x * sgnB y := by
  cases x <;> cases y <;>
    norm_num [sgnB, show (true + true : Bool) = false from rfl,
      show (true + false : Bool) = true from rfl, show (false + true : Bool) = true from rfl,
      show (false + false : Bool) = false from rfl]

theorem sgnB_sum {ι : Type*} (s : Finset ι) (β : ι → Bool) :
    sgnB (∑ i ∈ s, β i) = ∏ i ∈ s, sgnB (β i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgnB]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, sgnB_add, ih]

theorem cubeEquiv_apply' {n : ℕ} (a : Qubits n) (k : Fin n) : cubeEquiv n a k = bitEquiv (a k) := rfl

theorem sgnB_dotBits {n : ℕ} (a a' : Qubits n) :
    sgnB (dotBits a a') = character (cubeEquiv n a) (cubeEquiv n a') := by
  rw [dotBits, sgnB_sum, character_prod]
  apply prod_congr rfl; intro k _
  rw [cubeEquiv_apply', cubeEquiv_apply']
  cases a k <;> cases a' k <;> simp [sgnB, bitEquiv, χ2_zero, χ2_one]

/-- splitting the register into selector and address -/
def e1 (t : ℕ) : Bool × Cube t ≃ Qubits (t+1) :=
  (Equiv.prodCongr (Equiv.refl Bool) (cubeEquiv t).symm).trans (Fin.consEquiv (fun _ => Bool))

theorem e1_apply (t : ℕ) (s : Bool) (v : Cube t) :
    e1 t (s, v) = Fin.cons s ((cubeEquiv t).symm v) := rfl

theorem dotBits_cons {t : ℕ} (s s' : Bool) (a a' : Qubits t) :
    dotBits (Fin.cons s a : Qubits (t+1)) (Fin.cons s' a') = (s && s') + dotBits a a' := by
  simp [dotBits, Fin.sum_univ_succ]

theorem sB_e1 {t : ℕ} (s' s : Bool) (v' v : Cube t) :
    sB (e1 t (s', v')) (e1 t (s, v)) = sgnB (s && s') * character v v' := by
  rw [sB, e1_apply, e1_apply, dotBits_cons, ← sgnB, sgnB_add, sgnB_dotBits]
  simp

theorem sum_qubits_succ {t : ℕ} (F : Qubits (t+1) → ℝ) :
    (∑ w, F w) = ∑ v : Cube t, F (e1 t (false, v)) + ∑ v : Cube t, F (e1 t (true, v)) := by
  rw [← (e1 t).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]

theorem amp_e1 {t : ℕ} (Dr : Qubits (t+1) → ℝ) (s' : Bool) (v' : Cube t) :
    (∑ w, sB (e1 t (s', v')) w * Dr w) =
      (∑ v, character v v' * Dr (e1 t (false, v))) +
        sgnB s' * ∑ v, character v v' * Dr (e1 t (true, v)) := by
  rw [sum_qubits_succ]
  simp only [sB_e1, mul_sum]
  congr 1
  · apply sum_congr rfl; intro v _; simp [sgnB]
  · apply sum_congr rfl; intro v _; simp only [Bool.true_and]; ring

theorem born_split {n t : ℕ} (c : Middle n (t+1)) (Acc : Qubits (t+1) → Prop) (f g : Cube n → ℝ)
    (Dr : Qubits (t+1) → ℝ)
    (hU : OracleCircuit.unitary c (fun _ => jointOracle f g) = Matrix.diagonal (fun y => (Dr y : ℂ)))
    (τ : Cube t → ℝ) (hτ : IsSign τ)
    (hAcc : ∀ s' v', Acc (e1 t (s', v')) ↔ (τ v' = 1 ↔ s' = false)) :
    born c Acc f g = (((Real.sqrt 2)⁻¹ ^ (t+1)) ^ 2) ^ 2 *
      ∑ v', ((∑ v, character v v' * Dr (e1 t (false, v))) ^ 2 +
        (∑ v, character v v' * Dr (e1 t (true, v))) ^ 2 +
        2 * τ v' * ((∑ v, character v v' * Dr (e1 t (false, v))) *
          (∑ v, character v v' * Dr (e1 t (true, v))))) := by
  classical
  rw [born_eq c Acc f g Dr hU, sum_qubits_succ, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl; intro v' _
  simp only [amp_e1]
  have hF := hAcc false v'
  have hT := hAcc true v'
  rcases hτ v' with h | h
  · have h1 : ¬ τ v' = 1 := by rw [h]; norm_num
    simp only [h1, false_iff, Bool.true_eq_false, iff_false, not_true_eq_false] at hF hT
    simp only [hF, hT, if_false, if_true, h, sgnB]
    simp; ring
  · simp only [h, true_iff, iff_true, Bool.true_eq_false] at hF hT
    simp only [hF, hT, if_false, if_true, h, sgnB]
    simp; ring

def cnt (W : ℕ → Bool) (i : ℕ) : ℕ := ∑ k ∈ range i, if W (k+1) then 1 else 0

theorem cnt_succ (W : ℕ → Bool) (i : ℕ) : cnt W (i+1) = cnt W i + (if W (i+1) then 1 else 0) := by
  simp only [cnt, sum_range_succ]

theorem rowProd (W : ℕ → Bool) (b X : Bool) : ∀ i,
    ((rowIdx i b).map (fun u => if W u && X then (-1 : ℝ) else 1)).prod =
      if X then (-1) ^ (cnt W i) * (if b && W 0 then -1 else 1) else 1 := by
  intro i
  induction i with
  | zero =>
    have h0 : cnt W 0 = 0 := rfl
    rw [h0]
    cases b <;> cases X <;> rcases Bool.eq_false_or_eq_true (W 0) with hw | hw <;>
      simp [rowIdx, hw]
  | succ i ih =>
    rw [rowIdx, List.map_append, List.prod_append, ih, cnt_succ]
    generalize cnt W i = c
    generalize hB : (b && W 0) = B
    cases X <;> rcases Bool.eq_false_or_eq_true (W (i+1)) with hw | hw <;> cases B <;>
      simp [hw, pow_succ]

def czSignW (W : ℕ → Bool) (ins : Instruction) : ℝ :=
  match ins with
  | .cz u v => if W u && W v then -1 else 1
  | _ => 1

theorem czsProd (W : ℕ → Bool) (b : Bool) : ∀ j,
    ((czs j b).map (czSignW W)).prod =
      (-1) ^ ((cnt W j).choose 2) * (if b && W 0 then (-1) ^ (cnt W j) else 1) := by
  intro j
  induction j with
  | zero => simp [czs, cnt]
  | succ j ih =>
    rw [czs, List.map_append, List.prod_append, ih, List.map_map]
    have : (czSignW W ∘ fun i => Instruction.cz i (j+1)) =
        (fun u => if W u && W (j+1) then (-1 : ℝ) else 1) := by
      funext u; simp [czSignW]
    rw [this, rowProd, cnt_succ]
    generalize cnt W j = c
    generalize (b && W 0) = B
    rcases Bool.eq_false_or_eq_true (W (j+1)) with hw | hw <;> cases B <;>
      simp [hw, Nat.choose_succ_succ, pow_add, pow_succ] <;> ring

end IQPSol

-- ===== Born =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity IQPForrelation832.SingleQuery Finset

def wn {m : ℕ} (y : Qubits m) (k : ℕ) : Bool := if h : k < m then y ⟨k, h⟩ else false

theorem ofReal_list_prod (l : List ℝ) : ((l.prod : ℝ) : ℂ) = (l.map (fun x : ℝ => (x : ℂ))).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

noncomputable def DrT (n t : ℕ) (hnt : n ≤ t) (b : Bool) (f g : Cube n → ℝ) (y : Qubits (t+1)) : ℝ :=
  (if (y ∘ Fin.castLE (Nat.succ_le_succ hnt)) 0 then g else f)
      (cubeEquiv n (Fin.tail (y ∘ Fin.castLE (Nat.succ_le_succ hnt)))) *
    ((czs t b).map (czSignW (wn y))).prod

theorem compile_query {n t : ℕ} (hnt : n ≤ t) :
    compileInstruction n (t+1) Instruction.query = some (.query 0 false none
      ⟨Fin.castLE (Nat.succ_le_succ hnt), Fin.castLE_injective _⟩ (by simp)) := by
  simp [compileInstruction, Nat.succ_le_succ hnt]

theorem compile_cz {n t u v : ℕ} (h : u < t + 1 ∧ v < t + 1 ∧ u ≠ v) :
    ∃ (emb : Fin 2 ↪ Fin (t+1)), emb 0 = ⟨u, h.1⟩ ∧ emb 1 = ⟨v, h.2.1⟩ ∧
      compileInstruction n (t+1) (Instruction.cz u v) =
        some (.gate ⟨Gate.ofMatrix2 (controlled pauliZ), Set.mem_univ _, emb⟩) := by
  simp only [compileInstruction, dif_pos h]
  exact ⟨_, rfl, rfl, rfl⟩

theorem jointOracle_diag {n : ℕ} (f g : Cube n → ℝ) :
    jointOracle f g = Matrix.diagonal (fun z : Qubits (n+1) =>
      ((if z 0 then g else f) (cubeEquiv n (Fin.tail z)) : ℂ)) := rfl

theorem embed_cz {m : ℕ} (w : Fin 2 ↪ Fin m) :
    embedOp (k := 2) (Gate.ofMatrix2 (controlled pauliZ)).mat w =
      Matrix.diagonal (fun y => if y (w 0) && y (w 1) then (-1 : ℂ) else 1) := by
  rw [czGate_mat, embedOp_diagonal]
  rfl

theorem unitary_circT {n t : ℕ} (hnt : n ≤ t) (b : Bool) (f g : Cube n → ℝ) :
    OracleCircuit.unitary (circT n t b) (fun _ => jointOracle f g) =
      Matrix.diagonal (fun y => (DrT n t hnt b f g y : ℂ)) := by
  rw [unitary_diag]
  · congr 1; funext y
    unfold circT
    rw [prod_filterMap]
    simp only [progT, List.map_cons, List.prod_cons]
    rw [compile_query hnt]
    simp only [OracleStep.mat, Bool.false_eq_true, if_false]
    rw [jointOracle_diag, embedOp_diagonal, Matrix.diagonal_apply_eq, DrT, Complex.ofReal_mul]
    congr 1
    · rw [ofReal_list_prod]
      conv_rhs => rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro ins hins
      obtain ⟨u, v, rfl, huv, hv⟩ := mem_czs hins
      obtain ⟨emb, he0, he1, hc⟩ := compile_cz (n := n) (show u < t + 1 ∧ v < t + 1 ∧ u ≠ v by omega)
      simp only [hc, OracleStep.mat]
      erw [embed_cz, Matrix.diagonal_apply_eq]
      simp only [Function.comp_apply, he0, he1, czSignW, wn, dif_pos (show u < t + 1 by omega),
        dif_pos (show v < t + 1 by omega)]
      split_ifs <;> simp
  · intro s hs
    obtain ⟨ins, hins, hcs⟩ := List.mem_filterMap.mp hs
    simp only [progT, List.mem_cons] at hins
    rcases hins with rfl | hins
    · rw [compile_query hnt, Option.some.injEq] at hcs
      subst hcs
      exact ⟨_, by simp only [OracleStep.mat, Bool.false_eq_true, if_false]; rw [jointOracle_diag,
        embedOp_diagonal]⟩
    · obtain ⟨u, v, rfl, huv, hv⟩ := mem_czs hins
      obtain ⟨emb, he0, he1, hc⟩ := compile_cz (n := n) (show u < t + 1 ∧ v < t + 1 ∧ u ≠ v by omega)
      rw [hc, Option.some.injEq] at hcs
      subst hcs
      exact ⟨_, by simp only [OracleStep.mat]; erw [embed_cz]⟩

def restrict {n t : ℕ} (hnt : n ≤ t) (v : Cube t) : Cube n := fun k => v (Fin.castLE hnt k)

theorem cnt_wn_e1 {t : ℕ} (s : Bool) (v : Cube t) : cnt (wn (e1 t (s, v))) t = weight v := by
  unfold cnt weight
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl; intro k _
  simp only [wn, dif_pos (show (k : ℕ) + 1 < t + 1 by omega), e1_apply]
  rw [show (⟨(k : ℕ) + 1, by omega⟩ : Fin (t+1)) = k.succ from rfl, Fin.cons_succ]
  simp only [cubeEquiv, Equiv.piCongrRight_symm_apply, bitEquiv, Equiv.coe_fn_symm_mk, Pi.map_apply]
  rcases zmod2_cases (v k) with h | h <;> simp [h] <;> rfl

theorem DrT_e1 {n t : ℕ} (hnt : n ≤ t) (b : Bool) (f g : Cube n → ℝ) (s : Bool) (v : Cube t) :
    DrT n t hnt b f g (e1 t (s, v)) =
      (if s then g else f) (restrict hnt v) * (χ2 (Q v) * (if b && s then χ2 (weight v : ZMod 2) else 1)) := by
  unfold DrT
  have h0 : (e1 t (s, v) ∘ Fin.castLE (Nat.succ_le_succ hnt)) 0 = s := by
    simp only [Function.comp_apply, e1_apply]
    rw [show Fin.castLE (Nat.succ_le_succ hnt) (0 : Fin (n+1)) = 0 from rfl, Fin.cons_zero]
  have h1 : cubeEquiv n (Fin.tail (e1 t (s, v) ∘ Fin.castLE (Nat.succ_le_succ hnt))) = restrict hnt v := by
    funext k
    rw [cubeEquiv_apply']
    show bitEquiv ((Fin.cons s ((cubeEquiv t).symm v) : Qubits (t+1)) ((Fin.castLE hnt k).succ)) =
      v (Fin.castLE hnt k)
    rw [Fin.cons_succ]
    simp [cubeEquiv]
  rw [h0, h1, czsProd, cnt_wn_e1, χ2_Q, χ2_natCast]
  have hw0 : wn (e1 t (s, v)) 0 = s := by
    simp only [wn, dif_pos (show 0 < t + 1 by omega), e1_apply]; rfl
  rw [hw0]

theorem isSign_tau {t : ℕ} (ht : Odd t) (b : Bool) :
    IsSign (realFourier (if b then sigmaEven else sigmaOdd : Cube t → ℝ)) := by
  intro v
  cases b
  · simp only [Bool.false_eq_true, if_false]; rw [realFourier_sigmaOdd ht, tauO]; split_ifs <;> simp
  · simp only [if_true]; rw [realFourier_sigmaEven ht, tauE]; split_ifs <;> simp

theorem born_circT {n t : ℕ} (hnt : n ≤ t) (ht : Odd t) (b : Bool) (f g : Cube n → ℝ)
    (hf : IsSign f) (hg : IsSign g) (Acc : Qubits (t+1) → Prop)
    (hAcc : ∀ s' v', Acc (e1 t (s', v')) ↔
      (realFourier (if b then sigmaEven else sigmaOdd : Cube t → ℝ) v' = 1 ↔ s' = false)) :
    born (circT n t b) Acc f g =
      1/2 + parityPhi (!b) (fun v => f (restrict hnt v)) (fun v => g (restrict hnt v)) / Real.sqrt 2 := by
  rw [born_split (circT n t b) Acc f g (DrT n t hnt b f g) (unitary_circT hnt b f g) _
    (isSign_tau ht b) hAcc]
  have hs : ∀ (x : ℝ) (a : ZMod 2), IsSign (fun _ : Unit => x) → True := fun _ _ _ => trivial
  have hH0 : IsSign (fun v => DrT n t hnt b f g (e1 t (false, v))) := by
    intro v; dsimp only; rw [DrT_e1]
    simp only [Bool.false_eq_true, if_false, Bool.and_false, mul_one]
    rcases hf (restrict hnt v) with h | h <;> rw [h] <;>
      rcases zmod2_cases (Q v) with hq | hq <;> rw [hq] <;> simp [χ2_zero, χ2_one]
  have hH1 : IsSign (fun v => DrT n t hnt b f g (e1 t (true, v))) := by
    intro v; dsimp only; rw [DrT_e1]
    simp only [if_true, Bool.and_true]
    rcases hg (restrict hnt v) with h | h <;> rw [h] <;>
      rcases zmod2_cases (Q v) with hq | hq <;> rw [hq] <;>
      cases b <;> simp [χ2_zero, χ2_one] <;>
      rcases zmod2_cases ((weight v : ℕ) : ZMod 2) with hw | hw <;> rw [hw] <;> simp [χ2_zero, χ2_one]
  rw [core (fun v => DrT n t hnt b f g (e1 t (false, v))) (fun v => DrT n t hnt b f g (e1 t (true, v)))
    (if b then sigmaEven else sigmaOdd) _ hH0 hH1 (fun v => rfl)]
  have key : (∑ v, ∑ u, DrT n t hnt b f g (e1 t (false, v)) * DrT n t hnt b f g (e1 t (true, u)) *
      (if b then sigmaEven else sigmaOdd : Cube t → ℝ) (v + u)) =
      Real.sqrt 2 * Real.sqrt 2 ^ (3 * t) *
        parityPhi (!b) (fun v => f (restrict hnt v)) (fun v => g (restrict hnt v)) := by
    rw [← spec_sum b]
    apply sum_congr rfl; intro v _; apply sum_congr rfl; intro u _
    rw [DrT_e1, DrT_e1]
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true, Bool.and_true, Bool.and_false,
      mul_one] <;> ring
  rw [key]
  have h2 : ((Real.sqrt 2)⁻¹ ^ (t+1)) ^ 2 = ((2 : ℝ) ^ (t+1))⁻¹ := by
    rw [inv_pow, inv_pow, ← pow_mul, mul_comm, pow_mul, sqrt_two_sq]
  have h3 : Real.sqrt 2 ^ (3 * t) = Real.sqrt 2 ^ t * 2 ^ t := by
    rw [show 3 * t = t + 2 * t by ring, pow_add, sqrt_two_pow_two_mul]
  have h4 : Real.sqrt 2 ^ t * Real.sqrt 2 ^ t = 2 ^ t := by
    rw [← pow_add, ← two_mul, sqrt_two_pow_two_mul]
  rw [h2, h3]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := sqrt_two_sq
  have hpos : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hpos2 : (0 : ℝ) < 2 ^ t := by positivity
  set P := parityPhi (!b) (fun v => f (restrict hnt v)) (fun v => g (restrict hnt v))
  have e : 2 * Real.sqrt 2 ^ t * (Real.sqrt 2 * (Real.sqrt 2 ^ t * 2 ^ t) * P) =
      2 * Real.sqrt 2 * 2 ^ t * 2 ^ t * P := by
    rw [← h4]; ring
  rw [e, pow_succ]
  field_simp
  linear_combination (4 * (2 ^ t) ^ 2 * P) * hs2

end IQPSol

-- ===== Main =====


namespace IQPSol

open QAlgorithms QAlgorithms.Complexity IQPForrelation832.SingleQuery Finset

theorem foldl_rep0 (n : ℕ) (k : Fin 8) (b z : Bool) (w : Fin 4) :
    ∃ k' : Fin 8, (List.replicate n true).foldl δ (0, k, b, z, w) = (0, k', b, z, w) ∧
      k'.val = (k.val + n) % 8 := by
  induction n generalizing k with
  | zero => exact ⟨k, by simp, by simp [Nat.mod_eq_of_lt k.isLt]⟩
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons]
    simp only [δ, if_true]
    obtain ⟨k', h1, h2⟩ := ih (k + 1)
    refine ⟨k', h1, ?_⟩
    rw [h2, Fin.val_add]
    simp only [show (1 : Fin 8).val = 1 from rfl]
    omega

theorem foldl_rep2 (m : ℕ) (k : Fin 8) (b z : Bool) (w : Fin 4) :
    (List.replicate m true).foldl δ (2, k, b, z, w) = (2, k, b, z, w) := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.foldl_cons]; simp only [δ, if_true]; exact ih

theorem foldl_bits (l : List Bool) (k : Fin 8) (b z : Bool) (w : Fin 4) :
    ∃ w' : Fin 4, l.foldl δ (4, k, b, z, w) = (4, k, b, z, w') ∧
      w'.val = (w.val + l.count true) % 4 := by
  induction l generalizing w with
  | nil => exact ⟨w, by simp, by simp [Nat.mod_eq_of_lt w.isLt]⟩
  | cons x l ih =>
    rw [List.foldl_cons]
    simp only [δ]
    obtain ⟨w', h1, h2⟩ := ih (if x then w + 1 else w)
    refine ⟨w', h1, ?_⟩
    rw [h2]
    cases x
    · simp
    · simp only [if_true, Fin.val_add, show (1 : Fin 4).val = 1 from rfl, List.count_cons_self]
      omega

theorem count_ofFn_eq_weight : ∀ {t : ℕ} (a : Qubits t),
    (List.ofFn a).count true = weight (cubeEquiv t a) := by
  intro t
  induction t with
  | zero => intro a; simp [weight]
  | succ t ih =>
    intro a
    rw [List.ofFn_succ, List.count_cons, ih, weight, weight, Fin.sum_univ_succ]
    simp only [cubeEquiv_apply']
    cases a 0 <;> simp [bitEquiv]
    rw [show (1 : ZMod 2).val = 1 from rfl]; ring

theorem tOf_odd (n : ℕ) : Odd (tOf n) := by
  unfold tOf; split_ifs with h
  · exact h
  · exact Nat.odd_add_one.mpr h

theorem le_tOf (n : ℕ) : n ≤ tOf n := by unfold tOf; split_ifs <;> omega

theorem fold_decision (n : ℕ) (b : Bool) (s' : Bool) (v' : Cube (tOf n)) :
    ∃ (k1 : Fin 8) (w' : Fin 4),
      (decisionInput n b (e1 (tOf n) (s', v'))).foldl δ v0 = (4, k1, b, s', w') ∧
      k1.val = n % 8 ∧ w'.val = weight v' % 4 := by
  obtain ⟨k1, hk1, hk1v⟩ := foldl_rep0 n 0 false false 0
  obtain ⟨w', hw', hw'v⟩ := foldl_bits (List.ofFn ((cubeEquiv (tOf n)).symm v')) k1 b s' 0
  refine ⟨k1, w', ?_, by simpa using hk1v, ?_⟩
  · simp only [decisionInput, encNat, List.foldl_append, v0, e1_apply, List.ofFn_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [hk1]
    simp only [List.foldl_cons, List.foldl_nil, δ, Bool.false_eq_true, if_false]
    rw [foldl_rep2]
    simp only [δ, Bool.false_eq_true, if_false]
    rw [hw']
  · rw [hw'v, count_ofFn_eq_weight, Equiv.apply_symm_apply]; simp

theorem decider_correct (n : ℕ) (b : Bool) (s' : Bool) (v' : Cube (tOf n)) :
    result ((decisionInput n b (e1 (tOf n) (s', v'))).foldl δ v0) = true ↔
      (realFourier (if b then sigmaEven else sigmaOdd : Cube (tOf n) → ℝ) v' = 1 ↔ s' = false) := by
  obtain ⟨k1, w', hf, hk, hw⟩ := fold_decision n b s' v'
  rw [hf]
  have ht := tOf_odd n
  have he : ((if k1.val % 2 = 1 then k1.val else (k1.val + 1) % 8) - 1) / 2 + 4 - w'.val =
      0 + (((if k1.val % 2 = 1 then k1.val else (k1.val + 1) % 8) - 1) / 2 + 4 - w'.val) := by omega
  have heq : (((if k1.val % 2 = 1 then k1.val else (k1.val + 1) % 8) - 1) / 2 + 4 - w'.val) % 4 =
      eIdx (tOf n) (weight v') := by
    unfold eIdx
    rw [hk, hw]
    generalize weight v' = W
    have htv : tOf n = if Odd n then n else n + 1 := rfl
    rw [htv]
    by_cases ho : Odd n
    · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
      have h2 : n % 8 % 2 = 1 := by omega
      rw [if_pos h2, if_pos ho]; omega
    · have h1 : n % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h
        · exact h
        · exact absurd (Nat.odd_iff.mpr h) ho
      have h2 : ¬ n % 8 % 2 = 1 := by omega
      rw [if_neg h2, if_neg ho]; omega
  simp only [result, decide']
  rw [heq]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [realFourier_sigmaOdd ht, tauO]
    by_cases hc : eIdx (tOf n) (weight v') = 0 ∨ eIdx (tOf n) (weight v') = 1
    · simp only [hc, if_true, decide_true]; cases s' <;> simp
    · simp only [hc, if_false, decide_false]; cases s' <;> norm_num
  · simp only [if_true]
    rw [realFourier_sigmaEven ht, tauE]
    by_cases hc : eIdx (tOf n) (weight v') = 0 ∨ eIdx (tOf n) (weight v') = 3
    · simp only [hc, if_true, decide_true]; cases s' <;> simp
    · simp only [hc, if_false, decide_false]; cases s' <;> norm_num

theorem phi_restrict_odd {n t : ℕ} (h : n ≤ t) (heq : t = n) (f g : Cube n → ℝ) :
    Phi (fun v : Cube t => f (restrict h v)) (fun v => g (restrict h v)) = Phi f g := by
  subst heq; rfl

theorem phi_restrict_even {n t : ℕ} (h : n ≤ t) (heq : t = n + 1) (f g : Cube n → ℝ) :
    Phi (fun v : Cube t => f (restrict h v)) (fun v => g (restrict h v)) = Phi f g / Real.sqrt 2 := by
  subst heq
  rw [← Phi_pad]
  rfl

theorem main_theorem :
    ∃ (p : ℕ → Bool → Program) (a : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str),
      EfficientOn (fun _ => True) p a ∧
      ∀ n, (∀ b, (p n b).wires = (if Odd n then n+1 else n+2)) ∧
        ∀ f g : Cube n → ℝ, IsSign f → IsSign g →
          fairBorn n p a f g =
            (if Odd n then 1/2 + Phi f g / (2 * Real.sqrt 2) else 1/2 + Phi f g / 4) := by
  obtain ⟨gen, hgenPT, hgen⟩ := generator_exists
  obtain ⟨a, haPT, ha⟩ := decider_exists
  refine ⟨prog, a, ⟨haPT, gen, hgenPT, 16, 2, ?_⟩, ?_⟩
  · intro n _ b
    refine ⟨by rw [hgen, decode_encProg], ⟨?_, circT n (tOf n) b, compile_eq (le_tOf n) b,
      circT_isIQP (le_tOf n) b, circT_queryCount (le_tOf n) b⟩, ?_⟩
    · show n + 1 ≤ tOf n + 1
      have := le_tOf n; omega
    · show tOf n + 1 + ((czs (tOf n) b).length + 1) + 2 * (tOf n + 1) ≤ 16 * (n + 1) ^ 2
      have h1 := czs_length (tOf n) b
      have h2 := tOf_le n
      have h3 : (tOf n + 1) ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith
  · intro n
    refine ⟨fun b => ?_, fun f g hf hg => ?_⟩
    · show tOf n + 1 = _
      unfold tOf; split_ifs <;> rfl
    · have hb : ∀ b, programBorn n (prog n b) a b f g = 1/2 +
          parityPhi (!b) (fun v => f (restrict (le_tOf n) v)) (fun v => g (restrict (le_tOf n) v)) /
            Real.sqrt 2 := by
        intro b
        unfold programBorn
        rw [prog_eq, compile_eq (le_tOf n) b]
        apply born_circT (le_tOf n) (tOf_odd n) b f g hf hg
        intro s' v'
        rw [← decider_correct n b s' v']
        simp only [accepts, ha, List.cons.injEq, and_true]
        exact Iff.rfl
      unfold fairBorn
      rw [hb, hb]
      simp only [Bool.not_false, Bool.not_true]
      have hsum : (1 / 2 + parityPhi true (fun v => f (restrict (le_tOf n) v))
            (fun v => g (restrict (le_tOf n) v)) / Real.sqrt 2 +
          (1 / 2 + parityPhi false (fun v => f (restrict (le_tOf n) v))
            (fun v => g (restrict (le_tOf n) v)) / Real.sqrt 2)) / 2 =
          1 / 2 + Phi (fun v => f (restrict (le_tOf n) v)) (fun v => g (restrict (le_tOf n) v)) /
            (2 * Real.sqrt 2) := by
        rw [← parityPhi_add]; ring
      rw [hsum]
      have hpos : (0 : ℝ) < Real.sqrt 2 := by positivity
      split_ifs with ho
      · rw [phi_restrict_odd (le_tOf n) (by unfold tOf; simp [ho])]
      · rw [phi_restrict_even (le_tOf n) (by unfold tOf; simp [ho])]
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        field_simp
        rw [hs]; ring

end IQPSol


open IQPForrelation832.SingleQuery in
theorem solution :
    ∃ (p : ℕ → Bool → Program) (a : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str),
      EfficientOn (fun _ => True) p a ∧
      ∀ n, (∀ b, (p n b).wires = (if Odd n then n+1 else n+2)) ∧
        ∀ f g : Cube n → ℝ, IsSign f → IsSign g →
          fairBorn n p a f g =
            (if Odd n then 1/2 + Phi f g / (2 * Real.sqrt 2) else 1/2 + Phi f g / 4) :=
  IQPSol.main_theorem
