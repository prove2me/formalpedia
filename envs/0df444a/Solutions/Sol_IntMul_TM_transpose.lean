-- Prove2me | solution 1 for IntMul.TM.transpose
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T00:39:54.616749+00:00
-- url     : https://prove2.me/submissions/cbc6afd1-5d33-4662-ac42-e036214999aa

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_MultitapeWords

-- ===== Basic =====


/-!
# A relaxed machine layer over `IntMul.MultitapeTM`

`Prog Γ k` is a deterministic `k`-tape machine over an arbitrary alphabet whose transition
function returns `none` to halt.  Its step semantics silently enforce the platform rules
(`▷` is kept and never written elsewhere, no left move from `▷`, tape `0` is read-only), so
`compile` turns any program into a `MultitapeTM` with one extra step.
-/

namespace IntMul.Mach

open IntMul

variable {Γ : Type} {k : ℕ}

/-- Tape contents and head positions. -/
structure Tapes (Γ : Type) (k : ℕ) where
  cells : Fin k → ℕ → Γ
  head : Fin k → ℕ

/-- Head movement, in the same shape as `MultitapeTM.step`. -/
def moveHead (m : Move) (h : ℕ) : ℕ :=
  match m with
  | Move.left => h - 1
  | Move.stay => h
  | Move.right => h + 1

namespace Tapes

/-- The scanned symbols. -/
def read (T : Tapes Γ k) : Fin k → Γ := fun i => T.cells i (T.head i)

/-- Write and move on every tape. -/
def write (T : Tapes Γ k) (w : Fin k → Γ × Move) : Tapes Γ k where
  cells i := Function.update (T.cells i) (T.head i) (w i).1
  head i := moveHead (w i).2 (T.head i)

end Tapes

/-- The action actually performed: `▷` is kept and never moved left from, `▷` is never written
elsewhere, and tape `0` is read-only. -/
def fix [DecidableEq Γ] (st : Γ) (a : Fin k → Γ) (w : Fin k → Γ × Move) : Fin k → Γ × Move :=
  fun i =>
    if a i = st then (st, if (w i).2 = Move.left then Move.stay else (w i).2)
    else ((if i.val = 0 ∨ (w i).1 = st then a i else (w i).1), (w i).2)

/-- A relaxed program: `δ` returns `none` to halt. -/
structure Prog (Γ : Type) (k : ℕ) where
  Q : Type
  [fintypeQ : Fintype Q]
  q0 : Q
  δ : Q → (Fin k → Γ) → Option (Q × (Fin k → Γ × Move))

attribute [instance] Prog.fintypeQ

section Sem

variable [DecidableEq Γ] (st : Γ)

/-- `Halts st P q T t T'`: started in state `q` on tapes `T`, the program halts after exactly
`t` steps with tapes `T'`. -/
inductive Halts (P : Prog Γ k) : P.Q → Tapes Γ k → ℕ → Tapes Γ k → Prop
  | done {q : P.Q} {T : Tapes Γ k} : P.δ q T.read = none → Halts P q T 0 T
  | step {q q' : P.Q} {T T' : Tapes Γ k} {w : Fin k → Γ × Move} {t : ℕ} :
      P.δ q T.read = some (q', w) → Halts P q' (T.write (fix st T.read w)) t T' →
        Halts P q T (t + 1) T'

/-- Run from the start state. -/
def Runs (P : Prog Γ k) (T : Tapes Γ k) (t : ℕ) (T' : Tapes Γ k) : Prop :=
  Halts st P P.q0 T t T'

variable {st}

theorem Halts.det {P : Prog Γ k} {q : P.Q} {T T₁ T₂ : Tapes Γ k} {t₁ t₂ : ℕ}
    (h₁ : Halts st P q T t₁ T₁) (h₂ : Halts st P q T t₂ T₂) : t₁ = t₂ ∧ T₁ = T₂ := by
  induction h₁ generalizing t₂ with
  | done h => cases h₂ with
    | done _ => exact ⟨rfl, rfl⟩
    | step h' _ => rw [h] at h'; cases h'
  | step h _ ih => cases h₂ with
    | done h' => rw [h] at h'; cases h'
    | step h' hr =>
      rw [h] at h'; cases h'
      obtain ⟨rfl, rfl⟩ := ih hr
      exact ⟨rfl, rfl⟩

/-- Two states with the same transition on the current symbols behave the same. -/
theorem Halts.congr_state {P : Prog Γ k} {q₁ q₂ : P.Q} {T T' : Tapes Γ k} {t : ℕ}
    (hq : P.δ q₁ T.read = P.δ q₂ T.read) (h : Halts st P q₂ T t T') : Halts st P q₁ T t T' := by
  cases h with
  | done h0 => exact Halts.done (hq.trans h0)
  | step h0 hr => exact Halts.step (hq.trans h0) hr

/-- Transport along a state map that commutes with the transition function. -/
theorem Halts.map {P R : Prog Γ k} (f : P.Q → R.Q)
    (hf : ∀ q a, R.δ (f q) a = (P.δ q a).map (fun r => (f r.1, r.2)))
    {q : P.Q} {T T' : Tapes Γ k} {t : ℕ} (h : Halts st P q T t T') :
    Halts st R (f q) T t T' := by
  induction h with
  | done h0 => exact Halts.done (by rw [hf, h0]; rfl)
  | step h0 _ ih => exact Halts.step (by rw [hf, h0]; rfl) ih

/-- A run given by an explicit trajectory of states and tapes. -/
theorem halts_of_traj (P : Prog Γ k) (m : ℕ) (qs : ℕ → P.Q) (Ts : ℕ → Tapes Γ k)
    (hstep : ∀ j < m, ∃ w, P.δ (qs j) (Ts j).read = some (qs (j + 1), w) ∧
      (Ts j).write (fix st (Ts j).read w) = Ts (j + 1))
    (hend : P.δ (qs m) (Ts m).read = none) : Halts st P (qs 0) (Ts 0) m (Ts m) := by
  suffices ∀ i ≤ m, Halts st P (qs (m - i)) (Ts (m - i)) i (Ts m) by
    simpa using this m le_rfl
  intro i
  induction i with
  | zero => intro _; simpa using Halts.done hend
  | succ i ih =>
    intro hi
    obtain ⟨w, hw, hT⟩ := hstep (m - (i + 1)) (by omega)
    have e : m - (i + 1) + 1 = m - i := by omega
    rw [e] at hw hT
    exact Halts.step hw (hT ▸ ih (by omega))

end Sem

/-! ## Combinators -/

/-- Run `P₁`, then `P₂` (no extra step at the junction). -/
def seq (P₁ P₂ : Prog Γ k) : Prog Γ k where
  Q := P₁.Q ⊕ P₂.Q
  q0 := Sum.inl P₁.q0
  δ q a := match q with
    | Sum.inl q => match P₁.δ q a with
      | some r => some (Sum.inl r.1, r.2)
      | none => (P₂.δ P₂.q0 a).map (fun r => (Sum.inr r.1, r.2))
    | Sum.inr q => (P₂.δ q a).map (fun r => (Sum.inr r.1, r.2))

/-- Branch on the scanned symbols, then run `P₁` or `P₂`. -/
def ite (c : (Fin k → Γ) → Bool) (P₁ P₂ : Prog Γ k) : Prog Γ k where
  Q := Option (P₁.Q ⊕ P₂.Q)
  q0 := none
  δ q a := match q with
    | none => if c a then (P₁.δ P₁.q0 a).map (fun r => (some (Sum.inl r.1), r.2))
        else (P₂.δ P₂.q0 a).map (fun r => (some (Sum.inr r.1), r.2))
    | some (Sum.inl q) => (P₁.δ q a).map (fun r => (some (Sum.inl r.1), r.2))
    | some (Sum.inr q) => (P₂.δ q a).map (fun r => (some (Sum.inr r.1), r.2))

/-- `while c do B`: the test is made on the scanned symbols before every pass. -/
def loop (c : (Fin k → Γ) → Bool) (B : Prog Γ k) : Prog Γ k where
  Q := Option B.Q
  q0 := none
  δ q a := match q with
    | none => if c a then (B.δ B.q0 a).map (fun r => (some r.1, r.2)) else none
    | some q => match B.δ q a with
      | some r => some (some r.1, r.2)
      | none => if c a then (B.δ B.q0 a).map (fun r => (some r.1, r.2)) else none

/-- A program with a single step. -/
def act (f : (Fin k → Γ) → Fin k → Γ × Move) : Prog Γ k where
  Q := Bool
  q0 := false
  δ q a := if q then none else some (true, f a)

/-- The empty program. -/
def skip : Prog Γ k where
  Q := Unit
  q0 := ()
  δ _ _ := none

section CombSem

variable [DecidableEq Γ] {st : Γ}

theorem seq_halts {P₁ P₂ : Prog Γ k} {q : P₁.Q} {T T₁ T₂ : Tapes Γ k} {t₁ t₂ : ℕ}
    (h₁ : Halts st P₁ q T t₁ T₁) (h₂ : Runs st P₂ T₁ t₂ T₂) :
    Halts st (seq P₁ P₂) (Sum.inl q) T (t₁ + t₂) T₂ := by
  have hR : ∀ {q' : P₂.Q} {U U' : Tapes Γ k} {s : ℕ}, Halts st P₂ q' U s U' →
      Halts st (seq P₁ P₂) (Sum.inr q') U s U' := fun h =>
    Halts.map (R := seq P₁ P₂) Sum.inr (fun _ _ => rfl) h
  induction h₁ with
  | done h0 =>
    simp only [Nat.zero_add]
    cases h₂ with
    | done h' => exact Halts.done (by simp [seq, h0, h'])
    | step h' hr => exact Halts.step (by simp [seq, h0, h']) (hR hr)
  | step h0 _ ih =>
    rw [Nat.add_right_comm]
    exact Halts.step (by simp [seq, h0]) (ih h₂)

theorem seq_runs {P₁ P₂ : Prog Γ k} {T T₁ T₂ : Tapes Γ k} {t₁ t₂ : ℕ}
    (h₁ : Runs st P₁ T t₁ T₁) (h₂ : Runs st P₂ T₁ t₂ T₂) :
    Runs st (seq P₁ P₂) T (t₁ + t₂) T₂ := seq_halts h₁ h₂

theorem ite_runs_true {c : (Fin k → Γ) → Bool} {P₁ P₂ : Prog Γ k} {T T' : Tapes Γ k} {t : ℕ}
    (hc : c T.read = true) (h : Runs st P₁ T t T') : Runs st (ite c P₁ P₂) T t T' := by
  have hm := Halts.map (R := ite c P₁ P₂) (fun q => some (Sum.inl q)) (fun _ _ => rfl) h
  exact Halts.congr_state (by simp [ite, hc]) hm

theorem ite_runs_false {c : (Fin k → Γ) → Bool} {P₁ P₂ : Prog Γ k} {T T' : Tapes Γ k} {t : ℕ}
    (hc : c T.read = false) (h : Runs st P₂ T t T') : Runs st (ite c P₁ P₂) T t T' := by
  have hm := Halts.map (R := ite c P₁ P₂) (fun q => some (Sum.inr q)) (fun _ _ => rfl) h
  exact Halts.congr_state (by simp [ite, hc]) hm

theorem loop_stop {c : (Fin k → Γ) → Bool} {B : Prog Γ k} {T : Tapes Γ k}
    (hc : c T.read = false) : Runs st (loop c B) T 0 T :=
  Halts.done (by simp [loop, hc])

theorem loop_body {c : (Fin k → Γ) → Bool} {B : Prog Γ k} {q : B.Q} {T T₁ T₂ : Tapes Γ k}
    {t s : ℕ} (h : Halts st B q T t T₁) (hl : Runs st (loop c B) T₁ s T₂) :
    Halts st (loop c B) (some q) T (t + s) T₂ := by
  induction h with
  | done h0 =>
    simp only [Nat.zero_add]
    exact Halts.congr_state (by simp [loop, h0]) hl
  | step h0 _ ih =>
    rw [Nat.add_right_comm]
    exact Halts.step (by simp [loop, h0]) (ih hl)

theorem loop_iter {c : (Fin k → Γ) → Bool} {B : Prog Γ k} {T T₁ T₂ : Tapes Γ k} {t s : ℕ}
    (hc : c T.read = true) (ht : 0 < t) (h : Runs st B T t T₁)
    (hl : Runs st (loop c B) T₁ s T₂) : Runs st (loop c B) T (t + s) T₂ := by
  cases h with
  | done _ => omega
  | step h0 hr =>
    rw [Nat.add_right_comm]
    exact Halts.step (by simp [loop, hc, h0]) (loop_body hr hl)

theorem act_runs (f : (Fin k → Γ) → Fin k → Γ × Move) (T : Tapes Γ k) :
    Runs st (act f) T 1 (T.write (fix st T.read (f T.read))) :=
  Halts.step (by simp [act]; rfl) (Halts.done (by simp [act]))

theorem skip_runs (T : Tapes Γ k) : Runs st (skip : Prog Γ k) T 0 T :=
  Halts.done rfl

end CombSem

/-! ## Compilation to the platform model -/

/-- The five distinguished symbols of the platform model. -/
structure Syms (Γ : Type) where
  blank : Γ
  st : Γ
  zero : Γ
  one : Γ
  sep : Γ
  nodup : [blank, st, zero, one, sep].Nodup

variable [DecidableEq Γ] [Fintype Γ]

/-- The platform machine running `P`; one extra step moves to `HALT`. -/
def compile (S : Syms Γ) (hk : 2 ≤ k) (P : Prog Γ k) : MultitapeTM where
  Sym := Γ
  blank := S.blank
  startSym := S.st
  zero := S.zero
  one := S.one
  sep := S.sep
  syms_distinct := S.nodup
  K := Option P.Q
  qStart := some P.q0
  qHalt := none
  start_ne_halt := by simp
  k := k
  two_le_k := hk
  δ q a := match q with
    | none => (none, fun i => (a i, Move.stay))
    | some q => match P.δ q a with
      | none => (none, fun i => (a i, Move.stay))
      | some r => (some r.1, fix S.st a r.2)
  start_preserved := by
    intro q a i hi
    rcases q with _ | q
    · simp [hi]
    · rcases h : P.δ q a with _ | r <;> simp only [h]
      · simp [hi]
      · simp only [fix, hi, if_true]
        split_ifs with hm <;> simp_all
  start_only_at_start := by
    intro q a i hi
    rcases q with _ | q
    · simpa using hi
    · rcases h : P.δ q a with _ | r <;> simp only [h]
      · simpa using hi
      · simp only [fix, hi, if_false]
        split_ifs with h'
        · exact hi
        · simp_all
  halt_fixed := fun _ => rfl
  input_readonly := by
    intro q a
    rcases q with _ | q
    · rfl
    · rcases h : P.δ q a with _ | r <;> simp only [h]
      simp only [fix]
      split_ifs <;> simp_all

/-- A configuration of the compiled machine. -/
def toCfg (S : Syms Γ) (hk : 2 ≤ k) (P : Prog Γ k) (q : Option P.Q) (T : Tapes Γ k) :
    (compile S hk P).Cfg :=
  ⟨q, T.cells, T.head⟩

theorem compile_step (S : Syms Γ) (hk : 2 ≤ k) (P : Prog Γ k) (q q' : P.Q) (T : Tapes Γ k)
    (w : Fin k → Γ × Move) (h : P.δ q T.read = some (q', w)) :
    (compile S hk P).step (toCfg S hk P (some q) T) =
      toCfg S hk P (some q') (T.write (fix S.st T.read w)) := by
  have h' : P.δ q (fun i => T.cells i (T.head i)) = some (q', w) := h
  simp only [MultitapeTM.step, toCfg, compile, h', Tapes.write]
  rfl

theorem compile_halt_step (S : Syms Γ) (hk : 2 ≤ k) (P : Prog Γ k) (q : Option P.Q)
    (T : Tapes Γ k) (h : ∀ q', q = some q' → P.δ q' T.read = none) :
    (compile S hk P).step (toCfg S hk P q T) = toCfg S hk P none T := by
  rcases q with _ | q
  · simp only [MultitapeTM.step, toCfg, compile]
    congr 1 <;> funext i <;> simp
  · have h' : P.δ q (fun i => T.cells i (T.head i)) = none := h q rfl
    simp only [MultitapeTM.step, toCfg, compile, h']
    congr 1 <;> funext i <;> simp

theorem compile_halts (S : Syms Γ) (hk : 2 ≤ k) (P : Prog Γ k) {q : P.Q} {T T' : Tapes Γ k}
    {t : ℕ} (h : Halts S.st P q T t T') :
    (compile S hk P).step^[t + 1] (toCfg S hk P (some q) T) = toCfg S hk P none T' := by
  induction h with
  | done h0 =>
    simp only [Nat.zero_add, Function.iterate_one]
    exact compile_halt_step S hk P _ _ (fun q' hq => by cases hq; exact h0)
  | step h0 _ ih =>
    rw [show _ + 1 + 1 = _ + 1 + 1 from rfl, Function.iterate_succ_apply,
      compile_step S hk P _ _ _ _ h0]
    exact ih

/-- The platform's initial tapes on input `x#y`. -/
def initTapes (S : Syms Γ) (hk : 2 ≤ k) (x y : List Bool) : Tapes Γ k :=
  ⟨fun i => if i.val = 0 then
      (fun p => match p with
        | 0 => S.st
        | p + 1 => ((x.map (fun b => if b then S.one else S.zero)) ++
            S.sep :: y.map (fun b => if b then S.one else S.zero)).getD p S.blank)
      else (fun p => match p with
        | 0 => S.st
        | _ + 1 => S.blank),
   fun _ => 0⟩

/-- The tape `▷ w □ □ …`. -/
def tapeOf (S : Syms Γ) (w : List Γ) : ℕ → Γ
  | 0 => S.st
  | p + 1 => w.getD p S.blank

/-- Encoding of a bit. -/
def bitSym (S : Syms Γ) (b : Bool) : Γ := if b then S.one else S.zero

theorem initCfg_eq (S : Syms Γ) (hk : 2 ≤ k) (P : Prog Γ k) (x y : List Bool) :
    (compile S hk P).initCfg x y = toCfg S hk P (some P.q0) (initTapes S hk x y) := by
  simp only [MultitapeTM.initCfg, toCfg, initTapes]
  congr 1
  funext i p
  by_cases hi : i.val = 0
  · have : i = (compile S hk P).inTape := Fin.ext (by simp [MultitapeTM.inTape, hi])
    rw [if_pos this, if_pos hi]
    cases p <;> rfl
  · have : i ≠ (compile S hk P).inTape := fun h => hi (by rw [h]; rfl)
    rw [if_neg this, if_neg hi]
    cases p <;> rfl

/-- Correctness transfer: a program run that leaves `bin (2n) (val x * val y)` on tape `1`
gives `HaltsWithOutput` for the compiled machine, one step later. -/
theorem compile_haltsWithOutput (S : Syms Γ) (hk : 2 ≤ k) (P : Prog Γ k) (x y : List Bool)
    (w : List Bool) (t : ℕ) (T' : Tapes Γ k)
    (h : Runs S.st P (initTapes S hk x y) t T')
    (hout : T'.cells ⟨1, by omega⟩ = tapeOf S (w.map (bitSym S))) :
    (compile S hk P).HaltsWithOutput x y (t + 1) w := by
  unfold MultitapeTM.HaltsWithOutput
  rw [initCfg_eq, compile_halts S hk P h]
  refine ⟨rfl, ?_⟩
  simp only [toCfg]
  rw [show (compile S hk P).outTape = (⟨1, by omega⟩ : Fin k) from rfl, hout]
  funext p
  cases p <;> rfl

end IntMul.Mach

-- ===== Walk =====


/-!
# Scans, copies and finite-state walks

Generic single-loop programs and their exact running times.
-/

namespace IntMul.Mach

open IntMul

set_option linter.unusedSectionVars false

variable {Γ : Type} {k : ℕ} [DecidableEq Γ]

/-! ## Tape lemmas -/

theorem tapeOf_zero (S : Syms Γ) (w : List Γ) : tapeOf S w 0 = S.st := rfl

theorem tapeOf_succ (S : Syms Γ) (w : List Γ) (p : ℕ) : tapeOf S w (p + 1) = w.getD p S.blank :=
  rfl

theorem tapeOf_append_singleton (S : Syms Γ) (P : List Γ) (s : Γ) :
    Function.update (tapeOf S P) (P.length + 1) s = tapeOf S (P ++ [s]) := by
  funext p
  rcases p with _ | p
  · simp [Function.update, tapeOf]
  · by_cases hp : p = P.length
    · subst hp; simp [tapeOf]
    · rw [Function.update_of_ne (by omega)]
      simp only [tapeOf]
      rcases Nat.lt_or_gt_of_ne hp with h | h
      · rw [List.getD_append _ _ _ _ h]
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem tapeOf_set (S : Syms Γ) (L R : List Γ) (x y : Γ) :
    Function.update (tapeOf S (L ++ x :: R)) (L.length + 1) y = tapeOf S (L ++ y :: R) := by
  funext p
  rcases p with _ | p
  · simp [Function.update, tapeOf]
  · by_cases hp : p = L.length
    · subst hp; simp [tapeOf]
    · rw [Function.update_of_ne (by omega)]
      simp only [tapeOf]
      rcases Nat.lt_or_gt_of_ne hp with h | h
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
      · obtain ⟨q, rfl⟩ : ∃ q, p = L.length + 1 + q := ⟨p - (L.length + 1), by omega⟩
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp [show L.length + 1 + q - L.length = q + 1 by omega]

theorem tapeOf_get (S : Syms Γ) (L R : List Γ) (x : Γ) :
    tapeOf S (L ++ x :: R) (L.length + 1) = x := by
  simp [tapeOf]

/-! ## Writing with `fix` -/

theorem fix_eq_of {st : Γ} {a : Fin k → Γ} {w : Fin k → Γ × Move}
    (h : ∀ i, ((w i).1 = a i ∧ ((w i).2 = Move.left → a i ≠ st)) ∨
      (i.val ≠ 0 ∧ a i ≠ st ∧ (w i).1 ≠ st)) :
    fix st a w = w := by
  funext i
  simp only [fix]
  rcases h i with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · split_ifs <;> simp_all [Prod.ext_iff]
  · simp [h1, h2, h3]

/-- The write vector that changes tape `i` only. -/
def wr1 (a : Fin k → Γ) (i : Fin k) (s : Γ) (m : Move) : Fin k → Γ × Move :=
  fun l => if l = i then (s, m) else (a l, Move.stay)

/-- The write vector that changes tapes `i` and `j` only. -/
def wr2 (a : Fin k → Γ) (i : Fin k) (s : Γ) (m : Move) (j : Fin k) (s' : Γ) (m' : Move) :
    Fin k → Γ × Move :=
  fun l => if l = j then (s', m') else if l = i then (s, m) else (a l, Move.stay)

theorem write_wr1 (T : Tapes Γ k) (i : Fin k) (s : Γ) (m : Move) :
    T.write (wr1 T.read i s m) =
      ⟨Function.update T.cells i (Function.update (T.cells i) (T.head i) s),
        Function.update T.head i (moveHead m (T.head i))⟩ := by
  simp only [Tapes.write, wr1]
  congr 1 <;> funext l <;> by_cases hl : l = i
  · subst hl; simp
  · simp [hl, Tapes.read]
  · subst hl; simp
  · simp [hl, moveHead]

theorem write_wr2 (T : Tapes Γ k) (i : Fin k) (s : Γ) (m : Move) (j : Fin k) (s' : Γ)
    (m' : Move) (hij : i ≠ j) :
    T.write (wr2 T.read i s m j s' m') =
      ⟨Function.update (Function.update T.cells i (Function.update (T.cells i) (T.head i) s)) j
          (Function.update (T.cells j) (T.head j) s'),
        Function.update (Function.update T.head i (moveHead m (T.head i))) j
          (moveHead m' (T.head j))⟩ := by
  simp only [Tapes.write, wr2]
  congr 1 <;> funext l <;> by_cases hl : l = j <;> by_cases hl' : l = i
  · subst hl; exact absurd hl' (Ne.symm hij)
  · subst hl; simp
  · subst hl'; simp [hl]
  · simp [hl, hl', Tapes.read]
  · subst hl; exact absurd hl' (Ne.symm hij)
  · subst hl; simp
  · subst hl'; simp [hl]
  · simp [hl, hl', moveHead]

theorem fix_wr1 {st : Γ} (a : Fin k → Γ) (i : Fin k) (s : Γ) (m : Move)
    (h : (s = a i ∧ (m = Move.left → a i ≠ st)) ∨ (i.val ≠ 0 ∧ a i ≠ st ∧ s ≠ st)) :
    fix st a (wr1 a i s m) = wr1 a i s m := by
  apply fix_eq_of
  intro l
  by_cases hl : l = i
  · subst hl; simpa [wr1] using h
  · left; simp [wr1, hl]

theorem fix_wr2 {st : Γ} (a : Fin k → Γ) (i : Fin k) (s : Γ) (m : Move) (j : Fin k) (s' : Γ)
    (m' : Move) (hij : i ≠ j)
    (h : (s = a i ∧ (m = Move.left → a i ≠ st)) ∨ (i.val ≠ 0 ∧ a i ≠ st ∧ s ≠ st))
    (h' : (s' = a j ∧ (m' = Move.left → a j ≠ st)) ∨ (j.val ≠ 0 ∧ a j ≠ st ∧ s' ≠ st)) :
    fix st a (wr2 a i s m j s' m') = wr2 a i s m j s' m' := by
  apply fix_eq_of
  intro l
  by_cases hl : l = j
  · subst hl; simpa [wr2] using h'
  · by_cases hl' : l = i
    · subst hl'; simpa [wr2, hl] using h
    · left; simp [wr2, hl, hl']

/-! ## Scans -/

/-- Move tape `i` right while the scanned symbol satisfies `c`. -/
def scanR (i : Fin k) (c : Γ → Bool) : Prog Γ k :=
  loop (fun a => c (a i)) (act (fun a => wr1 a i (a i) Move.right))

/-- Move tape `i` left while the scanned symbol satisfies `c`. -/
def scanL (i : Fin k) (c : Γ → Bool) : Prog Γ k :=
  loop (fun a => c (a i)) (act (fun a => wr1 a i (a i) Move.left))

theorem scanR_runs (st : Γ) (i : Fin k) (c : Γ → Bool) :
    ∀ (m : ℕ) (T : Tapes Γ k), (∀ p < m, c (T.cells i (T.head i + p)) = true) →
      c (T.cells i (T.head i + m)) = false →
      Runs st (scanR i c) T m ⟨T.cells, Function.update T.head i (T.head i + m)⟩ := by
  intro m
  induction m with
  | zero =>
    intro T _ h
    simp only [Nat.add_zero, Function.update_eq_self]
    exact loop_stop (by simpa [Tapes.read] using h)
  | succ m ih =>
    intro T hc hm
    have h1 := act_runs (st := st) (fun a => wr1 a i (a i) Move.right) T
    rw [fix_wr1 _ _ _ _ (Or.inl ⟨rfl, by simp⟩), write_wr1] at h1
    simp only [Tapes.read, Function.update_eq_self] at h1
    have := ih ⟨T.cells, Function.update T.head i (T.head i + 1)⟩
      (fun p hp => by simpa [Nat.add_assoc, Nat.add_comm 1 p] using hc (p + 1) (by omega))
      (by simpa [Nat.add_assoc, Nat.add_comm 1 m] using hm)
    simp only [Function.update_self, Function.update_idem] at this
    rw [show T.head i + 1 + m = T.head i + (m + 1) by omega] at this
    have h := loop_iter (c := fun a => c (a i)) (by simpa [Tapes.read] using hc 0 (by omega))
      (by omega) h1 this
    rwa [Nat.add_comm] at h

theorem scanL_runs (st : Γ) (i : Fin k) (c : Γ → Bool) :
    ∀ (m : ℕ) (T : Tapes Γ k), m ≤ T.head i →
      (∀ p < m, c (T.cells i (T.head i - p)) = true ∧ T.cells i (T.head i - p) ≠ st) →
      c (T.cells i (T.head i - m)) = false →
      Runs st (scanL i c) T m ⟨T.cells, Function.update T.head i (T.head i - m)⟩ := by
  intro m
  induction m with
  | zero =>
    intro T _ _ h
    simp only [Nat.sub_zero, Function.update_eq_self]
    exact loop_stop (by simpa [Tapes.read] using h)
  | succ m ih =>
    intro T hle hc hm
    have h0 := hc 0 (by omega)
    have h1 := act_runs (st := st) (fun a => wr1 a i (a i) Move.left) T
    rw [fix_wr1 _ _ _ _ (Or.inl ⟨rfl, fun _ => by simpa [Tapes.read] using h0.2⟩),
      write_wr1] at h1
    simp only [Tapes.read, Function.update_eq_self, moveHead] at h1
    have := ih ⟨T.cells, Function.update T.head i (T.head i - 1)⟩ (by simp; omega)
      (fun p hp => by
        have := hc (p + 1) (by omega)
        simpa [show T.head i - 1 - p = T.head i - (p + 1) by omega] using this)
      (by simpa [show T.head i - 1 - m = T.head i - (m + 1) by omega] using hm)
    simp only [Function.update_self, Function.update_idem] at this
    rw [show T.head i - 1 - m = T.head i - (m + 1) by omega] at this
    have h := loop_iter (c := fun a => c (a i)) (by simpa [Tapes.read] using h0.1)
      (by omega) h1 this
    rwa [Nat.add_comm] at h

/-! ## Copy -/

/-- While tape `i` scans a symbol satisfying `c`, write its image under `g` on tape `j`;
both heads move right. -/
def copy (i j : Fin k) (c : Γ → Bool) (g : Γ → Γ) : Prog Γ k :=
  loop (fun a => c (a i)) (act (fun a => wr2 a i (a i) Move.right j (g (a i)) Move.right))

theorem copy_runs (S : Syms Γ) (hbs : S.blank ≠ S.st) (i j : Fin k) (hij : i ≠ j)
    (hj : j.val ≠ 0) (c : Γ → Bool) (g : Γ → Γ) (hg : ∀ x, c x = true → g x ≠ S.st) :
    ∀ (L P : List Γ) (T : Tapes Γ k),
      (∀ p (hp : p < L.length), T.cells i (T.head i + p) = L[p]) →
      (∀ x ∈ L, c x = true) → c (T.cells i (T.head i + L.length)) = false →
      T.cells j = tapeOf S P → T.head j = P.length + 1 →
      Runs S.st (copy i j c g) T L.length
        ⟨Function.update T.cells j (tapeOf S (P ++ L.map g)),
          Function.update (Function.update T.head i (T.head i + L.length)) j
            (P.length + 1 + L.length)⟩ := by
  intro L
  induction L with
  | nil =>
    intro P T _ _ hend hcj hhj
    simp only [List.length_nil, List.map_nil, List.append_nil, Nat.add_zero]
    have e : (⟨Function.update T.cells j (tapeOf S P),
        Function.update (Function.update T.head i (T.head i)) j (P.length + 1)⟩ : Tapes Γ k) = T := by
      rw [← hcj, ← hhj]; simp
    rw [e]
    exact loop_stop (by simpa [Tapes.read] using hend)
  | cons x L ih =>
    intro P T hL hc hend hcj hhj
    have hx : T.cells i (T.head i) = x := by
      have := hL 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this
    have hrj : T.cells j (T.head j) = S.blank := by
      rw [hcj, hhj, tapeOf_succ, List.getD_eq_default _ _ le_rfl]
    have h1 := act_runs (st := S.st)
      (fun a => wr2 a i (a i) Move.right j (g (a i)) Move.right) T
    rw [fix_wr2 _ _ _ _ _ _ _ hij (Or.inl ⟨rfl, by simp⟩)
      (Or.inr ⟨hj, by simp [Tapes.read, hrj, hbs], by
        simp only [Tapes.read]; rw [hx]; exact hg x (hc x (by simp))⟩), write_wr2 _ _ _ _ _ _ _ hij]
      at h1
    simp only [Tapes.read, Function.update_eq_self, moveHead] at h1
    rw [hx, hcj, hhj, tapeOf_append_singleton] at h1
    have hij' : j ≠ i := Ne.symm hij
    have := ih (P ++ [g x])
      ⟨Function.update T.cells j (tapeOf S (P ++ [g x])),
        Function.update (Function.update T.head i (T.head i + 1)) j (P.length + 1 + 1)⟩
      (fun p hp => by
        simp only [Function.update_apply, if_neg hij, if_neg hij']
        have := hL (p + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 p] using this)
      (fun y hy => hc y (by simp [hy]))
      (by
        simp only [Function.update_apply, if_neg hij, if_neg hij']
        simpa [Nat.add_assoc, Nat.add_comm 1 L.length] using hend)
      (by simp) (by simp)
    simp only [Function.update_self, Function.update_idem, Function.update_apply, if_neg hij',
      if_true] at this
    have h := loop_iter (c := fun a => c (a i)) (by simpa [Tapes.read, hx] using hc x (by simp))
      (by omega) h1 this
    rw [show 1 + L.length = (x :: L).length by simp [Nat.add_comm]] at h
    change Runs S.st (copy i j c g) _ _ _ at h
    convert h using 2
    · funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [Function.update_apply, hl]
    · funext l
      by_cases hl : l = j
      · subst hl; simp; omega
      · by_cases hl' : l = i
        · subst hl'; simp [Function.update_apply, hl]; omega
        · simp [Function.update_apply, hl, hl']

/-! ## Finite-state walks to the left -/

/-- Right-to-left transduction of a list: final state and output. -/
def rwalk {α σ : Type} (f : σ → α → σ × α) : List α → σ → σ × List α
  | [], s => (s, [])
  | x :: xs, s => ((f (rwalk f xs s).1 x).1, (f (rwalk f xs s).1 x).2 :: (rwalk f xs s).2)

theorem rwalk_append_singleton {α σ : Type} (f : σ → α → σ × α) (L : List α) (x : α) (s : σ) :
    rwalk f (L ++ [x]) s = ((rwalk f L (f s x).1).1, (rwalk f L (f s x).1).2 ++ [(f s x).2]) := by
  induction L with
  | nil => rfl
  | cons y L ih => simp [rwalk, ih]

theorem rwalk_length {α σ : Type} (f : σ → α → σ × α) (L : List α) (s : σ) :
    (rwalk f L s).2.length = L.length := by
  induction L with
  | nil => rfl
  | cons y L ih => simp [rwalk, ih]

/-- Walk tape `i` from the current cell down to `▷`, rewriting each symbol with a
finite-state transducer. -/
def walk1 (st : Γ) {σ : Type} [Fintype σ] (i : Fin k) (s0 : σ) (f : σ → Γ → σ × Γ) : Prog Γ k where
  Q := σ
  q0 := s0
  δ s a := if a i = st then none else some ((f s (a i)).1, wr1 a i (f s (a i)).2 Move.left)

theorem walk1_halts (S : Syms Γ) {σ : Type} [Fintype σ] (i : Fin k) (hi : i.val ≠ 0) (s0 : σ)
    (f : σ → Γ → σ × Γ) (hf : ∀ s x, x ≠ S.st → (f s x).2 ≠ S.st) :
    ∀ (L R : List Γ) (s : σ) (T : Tapes Γ k), (∀ x ∈ L, x ≠ S.st) →
      T.cells i = tapeOf S (L ++ R) → T.head i = L.length →
      Halts S.st (walk1 S.st i s0 f) s T L.length
        ⟨Function.update T.cells i (tapeOf S ((rwalk f L s).2 ++ R)),
          Function.update T.head i 0⟩ := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro R s T _ hc hh
    simp only [List.nil_append, List.length_nil] at hc hh
    have e : (⟨Function.update T.cells i (tapeOf S ((rwalk f [] s).2 ++ R)),
        Function.update T.head i 0⟩ : Tapes Γ k) = T := by
      simp only [rwalk, List.nil_append, ← hc, ← hh, Function.update_eq_self]
    rw [e]
    exact Halts.done (by simp [walk1, Tapes.read, hc, hh, tapeOf_zero])
  | append_singleton L x ih =>
    intro R s T hL hc hh
    have hx : T.cells i (T.head i) = x := by
      rw [hc, hh]; simp [tapeOf, List.getD_append_right]
    have hxs : x ≠ S.st := hL x (by simp)
    have hstep : (walk1 S.st i s0 f).δ s T.read =
        some ((f s x).1, wr1 T.read i (f s x).2 Move.left) := by
      simp [walk1, Tapes.read, hx, hxs]
    rw [show (L ++ [x]).length = L.length + 1 by simp]
    · refine Halts.step hstep ?_
      rw [fix_wr1 _ _ _ _ (Or.inr ⟨hi, by simp [Tapes.read, hx, hxs], hf s x hxs⟩), write_wr1]
      have hset : Function.update (T.cells i) (T.head i) (f s x).2 =
          tapeOf S (L ++ (f s x).2 :: R) := by
        rw [hc, hh]
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append]
        exact tapeOf_set S L R x (f s x).2
      have := ih ((f s x).2 :: R) (f s x).1
        ⟨Function.update T.cells i (Function.update (T.cells i) (T.head i) (f s x).2),
          Function.update T.head i (moveHead Move.left (T.head i))⟩
        (fun y hy => hL y (by simp [hy])) (by simp [hset]) (by simp [moveHead, hh])
      simp only [Function.update_idem] at this
      convert this using 3
      rw [rwalk_append_singleton]; simp

/-- Walk tapes `i` and `j` together down to `▷` on tape `j`, rewriting tape `j` with a
finite-state transducer that also reads tape `i`. -/
def walk2 (st : Γ) {σ : Type} [Fintype σ] (i j : Fin k) (s0 : σ) (f : σ → Γ → Γ → σ × Γ) :
    Prog Γ k where
  Q := σ
  q0 := s0
  δ s a := if a j = st then none else
    some ((f s (a i) (a j)).1, wr2 a i (a i) Move.left j (f s (a i) (a j)).2 Move.left)

/-- The pair transducer behind `walk2`. -/
def pairF {σ : Type} (f : σ → Γ → Γ → σ × Γ) (s : σ) (x : Γ × Γ) : σ × (Γ × Γ) :=
  ((f s x.1 x.2).1, (x.1, (f s x.1 x.2).2))

theorem rwalk_pairF_fst {σ : Type} (f : σ → Γ → Γ → σ × Γ) (L : List (Γ × Γ)) (s : σ) :
    (rwalk (pairF f) L s).2.map Prod.fst = L.map Prod.fst := by
  induction L with
  | nil => rfl
  | cons y L ih => simp [rwalk, pairF, ih]

theorem walk2_halts (S : Syms Γ) {σ : Type} [Fintype σ] (i j : Fin k) (hij : i ≠ j)
    (hj : j.val ≠ 0) (s0 : σ)
    (f : σ → Γ → Γ → σ × Γ) (hf : ∀ s x y, y ≠ S.st → (f s x y).2 ≠ S.st) :
    ∀ (L : List (Γ × Γ)) (Ra Rc : List Γ) (s : σ) (T : Tapes Γ k),
      (∀ x ∈ L, x.1 ≠ S.st ∧ x.2 ≠ S.st) →
      T.cells i = tapeOf S (L.map Prod.fst ++ Ra) → T.head i = L.length →
      T.cells j = tapeOf S (L.map Prod.snd ++ Rc) → T.head j = L.length →
      Halts S.st (walk2 S.st i j s0 f) s T L.length
        ⟨Function.update T.cells j (tapeOf S ((rwalk (pairF f) L s).2.map Prod.snd ++ Rc)),
          Function.update (Function.update T.head i 0) j 0⟩ := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro Ra Rc s T _ hci hhi hcj hhj
    simp only [List.map_nil, List.nil_append, List.length_nil] at hci hhi hcj hhj
    have e : (⟨Function.update T.cells j (tapeOf S ((rwalk (pairF f) [] s).2.map Prod.snd ++ Rc)),
        Function.update (Function.update T.head i 0) j 0⟩ : Tapes Γ k) = T := by
      simp only [rwalk, List.map_nil, List.nil_append, ← hcj, ← hhi,
        Function.update_eq_self]
      rw [hhi, ← hhj, Function.update_eq_self]
    rw [e]
    exact Halts.done (by simp [walk2, Tapes.read, hcj, hhj, tapeOf_zero])
  | append_singleton L x ih =>
    intro Ra Rc s T hL hci hhi hcj hhj
    have hxi : T.cells i (T.head i) = x.1 := by
      rw [hci, hhi]; simp [tapeOf, List.getD_append_right]
    have hxj : T.cells j (T.head j) = x.2 := by
      rw [hcj, hhj]; simp [tapeOf, List.getD_append_right]
    have hxs := hL x (by simp)
    have hstep : (walk2 S.st i j s0 f).δ s T.read =
        some ((f s x.1 x.2).1, wr2 T.read i x.1 Move.left j (f s x.1 x.2).2 Move.left) := by
      simp [walk2, Tapes.read, hxi, hxj, hxs.2]
    rw [show (L ++ [x]).length = L.length + 1 by simp]
    refine Halts.step hstep ?_
    rw [fix_wr2 _ _ _ _ _ _ _ hij (Or.inl ⟨by simp [Tapes.read, hxi], fun _ => by
        simp [Tapes.read, hxi, hxs.1]⟩)
      (Or.inr ⟨hj, by simp [Tapes.read, hxj, hxs.2], hf s x.1 x.2 hxs.2⟩),
      write_wr2 _ _ _ _ _ _ _ hij]
    have hseti : Function.update (T.cells i) (T.head i) x.1 =
        tapeOf S (L.map Prod.fst ++ x.1 :: Ra) := by
      rw [hci, hhi]
      have := tapeOf_set S (L.map Prod.fst) Ra x.1 x.1
      simp only [List.length_map] at this
      simpa using this
    have hsetj : Function.update (T.cells j) (T.head j) (f s x.1 x.2).2 =
        tapeOf S (L.map Prod.snd ++ (f s x.1 x.2).2 :: Rc) := by
      rw [hcj, hhj]
      have := tapeOf_set S (L.map Prod.snd) Rc x.2 (f s x.1 x.2).2
      simp only [List.length_map] at this
      simpa using this
    have hji : j ≠ i := Ne.symm hij
    have := ih (x.1 :: Ra) ((f s x.1 x.2).2 :: Rc) (f s x.1 x.2).1
      ⟨Function.update (Function.update T.cells i (Function.update (T.cells i) (T.head i) x.1)) j
          (Function.update (T.cells j) (T.head j) (f s x.1 x.2).2),
        Function.update (Function.update T.head i (moveHead Move.left (T.head i))) j
          (moveHead Move.left (T.head j))⟩
      (fun y hy => hL y (by simp [hy]))
      (by simp [Function.update_apply, hij, hseti])
      (by simp [Function.update_apply, hij, moveHead, hhi])
      (by simp [hsetj]) (by simp [moveHead, hhj])
    have hTi : Function.update T.cells i (Function.update (T.cells i) (T.head i) x.1) = T.cells := by
      have : Function.update (T.cells i) (T.head i) x.1 = T.cells i := by
        rw [← hxi]; exact Function.update_eq_self _ _
      rw [this, Function.update_eq_self]
    rw [hTi] at this ⊢
    simp only [Function.update_idem] at this
    convert this using 2
    · rw [rwalk_append_singleton]; simp [pairF]
    · funext l
      simp only [Function.update_apply]
      split_ifs <;> simp_all

/-! ## Single moves -/

/-- Move head `i` one cell. -/
def mv (i : Fin k) (m : Move) : Prog Γ k := act (fun a => wr1 a i (a i) m)

theorem mv_runs (st : Γ) (i : Fin k) (m : Move) (T : Tapes Γ k)
    (h : m = Move.left → T.cells i (T.head i) ≠ st) :
    Runs st (mv i m) T 1 ⟨T.cells, Function.update T.head i (moveHead m (T.head i))⟩ := by
  have h1 := act_runs (st := st) (fun a => wr1 a i (a i) m) T
  rw [fix_wr1 _ _ _ _ (Or.inl ⟨rfl, h⟩), write_wr1] at h1
  simp only [Tapes.read, Function.update_eq_self] at h1
  exact h1

theorem Runs.of_eq {st : Γ} {P : Prog Γ k} {T T' T'' : Tapes Γ k} {t t' : ℕ}
    (h : Runs st P T t T') (e : T' = T'') (et : t = t') : Runs st P T t' T'' := e ▸ et ▸ h

theorem tapeOf_one_add (S : Syms Γ) (L : List Γ) (p : ℕ) :
    tapeOf S L (1 + p) = L.getD p S.blank := by
  rw [Nat.add_comm]; rfl

theorem tapeOf_ne_st (S : Syms Γ) (hbs : S.blank ≠ S.st) (L : List Γ) (hL : ∀ x ∈ L, x ≠ S.st)
    (p : ℕ) (hp : 1 ≤ p) : tapeOf S L p ≠ S.st := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [tapeOf_succ]
  by_cases hq : q < L.length
  · rw [List.getD_eq_getElem _ _ hq]; exact hL _ (List.getElem_mem hq)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hbs

end IntMul.Mach

-- ===== Sweep =====


/-!
# Sweeps

A sweep moves every head in a fixed direction each step and rewrites one destination tape with
a finite-state transducer reading all scanned symbols, until a condition on the scanned
symbols fails.  Its run is described in closed form: every read is a read of the original
tapes.
-/

namespace IntMul.Mach

variable {Γ : Type} {k : ℕ}

/-- Head position after `m` moves in direction `d` from `h`. -/
def offs (d : Move) (h m : ℕ) : ℕ :=
  match d with
  | Move.left => h - m
  | Move.stay => h
  | Move.right => h + m

theorem moveHead_offs (d : Move) (h m : ℕ) : moveHead d (offs d h m) = offs d h (m + 1) := by
  cases d <;> simp [moveHead, offs] <;> omega

theorem offs_zero (d : Move) (h : ℕ) : offs d h 0 = h := by cases d <;> rfl

variable [DecidableEq Γ]

/-- The sweep program. -/
def sweep {σ : Type} [Fintype σ] (d : Fin k → Move) (j : Fin k) (c : (Fin k → Γ) → Bool)
    (s0 : σ) (f : σ → (Fin k → Γ) → σ × Γ) : Prog Γ k where
  Q := σ
  q0 := s0
  δ s a := if c a then some ((f s a).1, fun i => (if i = j then (f s a).2 else a i, d i))
    else none

/-- The symbols read at step `m`: all from the original tapes. -/
def rd (T : Tapes Γ k) (d : Fin k → Move) (m : ℕ) : Fin k → Γ :=
  fun i => T.cells i (offs (d i) (T.head i) m)

section Trans

variable {σ : Type} (f : σ → (Fin k → Γ) → σ × Γ) (r : ℕ → Fin k → Γ)

/-- Transducer states along the reads `r`. -/
def sst (s0 : σ) : ℕ → σ
  | 0 => s0
  | m + 1 => (f (sst s0 m) (r m)).1

/-- Transducer outputs along the reads `r`. -/
def sout (s0 : σ) (m : ℕ) : Γ := (f (sst f r s0 m) (r m)).2

end Trans

/-- Destination cells after `m` writes. -/
def dcells (base : ℕ → Γ) (d : Move) (h : ℕ) (o : ℕ → Γ) : ℕ → ℕ → Γ
  | 0 => base
  | m + 1 => Function.update (dcells base d h o m) (offs d h m) (o m)

theorem offs_inj (d : Move) (hd : d ≠ Move.stay) (h m m' : ℕ) (hm : d = Move.left → m ≤ h)
    (hm' : m' < m) : offs d h m ≠ offs d h m' := by
  cases d <;> simp_all [offs] <;> omega

theorem dcells_other (base : ℕ → Γ) (d : Move) (hd : d ≠ Move.stay) (h : ℕ) (o : ℕ → Γ)
    (m : ℕ) (hm : d = Move.left → m ≤ h) : dcells base d h o m (offs d h m) = base (offs d h m) := by
  suffices ∀ n ≤ m, dcells base d h o n (offs d h m) = base (offs d h m) from this m le_rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dcells]
    rw [Function.update_of_ne (offs_inj d hd h m n hm (by omega)), ih (by omega)]

theorem sweep_runs (st : Γ) {σ : Type} [Fintype σ] (d : Fin k → Move) (j : Fin k)
    (c : (Fin k → Γ) → Bool) (s0 : σ) (f : σ → (Fin k → Γ) → σ × Γ) (T : Tapes Γ k) (L : ℕ)
    (hj0 : j.val ≠ 0) (hdj : d j ≠ Move.stay) (hjL : d j = Move.left → L ≤ T.head j)
    (hst : ∀ i p, d i = Move.left → T.cells i p = st → p = 0)
    (hc : ∀ m < L, c (rd T d m) = true) (hstop : c (rd T d L) = false)
    (hjst : ∀ m < L, rd T d m j ≠ st) (hout : ∀ m < L, sout f (rd T d) s0 m ≠ st) :
    Runs st (sweep d j c s0 f) T L
      ⟨Function.update T.cells j (dcells (T.cells j) (d j) (T.head j) (sout f (rd T d) s0) L),
        fun i => offs (d i) (T.head i) L⟩ := by
  let Ts : ℕ → Tapes Γ k := fun m =>
    ⟨Function.update T.cells j (dcells (T.cells j) (d j) (T.head j) (sout f (rd T d) s0) m),
      fun i => offs (d i) (T.head i) m⟩
  have hread : ∀ m ≤ L, (Ts m).read = rd T d m := by
    intro m hm
    funext i
    simp only [Ts, Tapes.read, rd]
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      exact dcells_other _ _ hdj _ _ _ (fun h => by have := hjL h; omega)
    · rw [Function.update_of_ne hi]
  have h := halts_of_traj (st := st) (sweep d j c s0 f) L (sst f (rd T d) s0) Ts ?_ ?_
  · have e0 : Ts 0 = T := by
      simp only [Ts, dcells, Function.update_eq_self, offs_zero]
    rw [e0] at h
    exact h
  · intro m hm
    refine ⟨fun i => (if i = j then sout f (rd T d) s0 m else rd T d m i, d i), ?_, ?_⟩
    · rw [hread m (by omega)]
      simp [sweep, hc m hm, sst, sout]
    · rw [hread m (by omega)]
      simp only [Tapes.write, Ts]
      congr 1
      · funext i
        by_cases hi : i = j
        · subst hi
          have h1 := hjst m hm
          have h2 := hout m hm
          simp only [fix, if_true, Function.update_self, dcells]
          rw [if_neg h1, if_neg (by tauto)]
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]
          simp only [fix, if_neg hi]
          have : (if rd T d m i = st then (st, if d i = Move.left then Move.stay else d i)
              else (if i.val = 0 ∨ rd T d m i = st then rd T d m i else rd T d m i, d i)).1 =
                rd T d m i := by
            split_ifs with h1 <;> simp_all
          rw [this]
          simp only [rd]
          exact Function.update_eq_self _ _
      · funext i
        simp only [fix]
        by_cases h1 : rd T d m i = st
        · rw [if_pos h1]
          by_cases hl : d i = Move.left
          · have h0 := hst i _ hl h1
            have : (if i = j then sout f (rd T d) s0 m else rd T d m i, d i).2 = Move.left := hl
            rw [if_pos this]
            simp only [moveHead]
            rw [h0]
            simp [offs, hl] at h0 ⊢
            omega
          · have : (if i = j then sout f (rd T d) s0 m else rd T d m i, d i).2 ≠ Move.left := hl
            rw [if_neg this]
            exact moveHead_offs _ _ _
        · rw [if_neg h1]
          exact moveHead_offs _ _ _
  · rw [hread L le_rfl]
    simp [sweep, hstop]

theorem dcells_right (base : ℕ → Γ) (h : ℕ) (o : ℕ → Γ) (L p : ℕ) :
    dcells base Move.right h o L p = if h ≤ p ∧ p < h + L then o (p - h) else base p := by
  induction L with
  | zero => simp only [dcells]; rw [if_neg (by omega)]
  | succ L ih =>
    simp only [dcells, offs]
    by_cases hp : p = h + L
    · subst hp; simp
    · rw [Function.update_of_ne hp, ih]
      by_cases h1 : h ≤ p ∧ p < h + L
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem dcells_left (base : ℕ → Γ) (h : ℕ) (o : ℕ → Γ) (L p : ℕ) (hL : L ≤ h) :
    dcells base Move.left h o L p = if h - L < p ∧ p ≤ h then o (h - p) else base p := by
  induction L with
  | zero => simp only [dcells]; rw [if_neg (by omega)]
  | succ L ih =>
    simp only [dcells, offs]
    by_cases hp : p = h - L
    · subst hp; rw [Function.update_self, if_pos (by omega)]; congr 1; omega
    · rw [Function.update_of_ne hp, ih (by omega)]
      by_cases h1 : h - L < p ∧ p ≤ h
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem getD_three (pre mid rest : List Γ) (d : Γ) (q : ℕ) :
    (pre ++ mid ++ rest).getD q d =
      if q < pre.length then pre.getD q d
      else if q < pre.length + mid.length then mid.getD (q - pre.length) d
      else rest.getD (q - pre.length - mid.length) d := by
  rw [List.append_assoc]
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]

theorem tapeOf_write_right (S : Syms Γ) (pre mid rest : List Γ) (o : ℕ → Γ) :
    (fun p => if pre.length + 1 ≤ p ∧ p < pre.length + 1 + mid.length
      then o (p - (pre.length + 1)) else tapeOf S (pre ++ mid ++ rest) p) =
      tapeOf S (pre ++ List.ofFn (fun m : Fin mid.length => o m) ++ rest) := by
  funext p
  rcases p with _ | q
  · rw [if_neg (by omega)]; rfl
  · simp only [tapeOf]
    rw [getD_three, getD_three]
    simp only [List.length_ofFn]
    split_ifs <;> first | omega | rfl |
      (rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp only [List.getElem_ofFn]; congr 1; omega)

theorem tapeOf_write_left (S : Syms Γ) (pre mid rest : List Γ) (o : ℕ → Γ) :
    (fun p => if pre.length < p ∧ p ≤ pre.length + mid.length
      then o (pre.length + mid.length - p) else tapeOf S (pre ++ mid ++ rest) p) =
      tapeOf S (pre ++ List.ofFn (fun m : Fin mid.length => o (mid.length - 1 - m)) ++ rest) := by
  funext p
  rcases p with _ | q
  · rw [if_neg (by omega)]; rfl
  · simp only [tapeOf]
    rw [getD_three, getD_three]
    simp only [List.length_ofFn]
    split_ifs <;> first | omega | rfl |
      (rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp only [List.getElem_ofFn]; congr 1; omega)

theorem tapeOf_append_blanks (S : Syms Γ) (w : List Γ) (n : ℕ) :
    tapeOf S (w ++ List.replicate n S.blank) = tapeOf S w := by
  funext p
  rcases p with _ | q
  · rfl
  · simp only [tapeOf]
    by_cases h : q < w.length
    · rw [List.getD_append _ _ _ _ h]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default w _ (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl

end IntMul.Mach

-- ===== MSDefs =====


/-!
# A stable bottom-up merge sort on six tapes

Tapes: `0` input, `1` output, `2` the current sequence `C`, `3` and `4` the distribution tapes
`A` and `B`, `5` a one-cell flag (head parked on cell `1`).

A record `(k, p)` is stored as `k sep p τ` with terminator `τ ∈ {rend, runend}`; a *run* is a
nonempty list of records whose last terminator is `runend`.  One pass distributes the runs of
`C` alternately to `A` and `B` and merges run `i` of `A` with run `i` of `B` back onto `C`.
-/

namespace IntMul.Mach.MS

open IntMul IntMul.Mach

set_option linter.unusedSectionVars false

/-- The alphabet. -/
inductive Sym7
  | blank
  | st
  | zero
  | one
  | sep
  | rend
  | runend
  deriving DecidableEq

open Sym7

instance : Fintype Sym7 :=
  ⟨{blank, st, zero, one, sep, rend, runend}, by intro x; cases x <;> simp⟩

def S7 : Syms Sym7 := ⟨blank, st, zero, one, sep, by decide⟩

def bs (b : Bool) : Sym7 := if b then one else zero

def enc (l : List Bool) : List Sym7 := l.map bs

/-- Record bodies: bits and the key/payload separator. -/
def isBody : Sym7 → Bool
  | zero | one | sep => true
  | _ => false

/-- Everything inside a run before its final `runend`. -/
def isRunBody : Sym7 → Bool
  | zero | one | sep | rend => true
  | _ => false

def isBit : Sym7 → Bool
  | zero | one => true
  | _ => false

def notSt : Sym7 → Bool
  | st => false
  | _ => true

/-- Output translation: record ends become `#`. -/
def outG : Sym7 → Sym7
  | rend => sep
  | s => s

/-- Input transduction: the parity says whether we are inside a payload. -/
def convF (s : Bool) (a : Fin 6 → Sym7) : Bool × Sym7 :=
  if a 0 = sep then (!s, if s then runend else sep) else (s, a 0)

/-! ## Encodings -/

abbrev Rec := List Bool × List Bool

def encR (τ : Sym7) (r : Rec) : List Sym7 := enc r.1 ++ sep :: enc r.2 ++ [τ]

def encRun : List Rec → List Sym7
  | [] => []
  | [r] => encR runend r
  | r :: rs => encR rend r ++ encRun rs

def encRuns (Rs : List (List Rec)) : List Sym7 := (Rs.map encRun).flatten

/-! ## Programs -/

/-- Copy one symbol from `i` to `j`; both heads move right. -/
def cp1 (i j : Fin 6) : Prog Sym7 6 :=
  act (fun a => wr2 a i (a i) Move.right j (a i) Move.right)

def wsym (i : Fin 6) (s : Sym7) : Prog Sym7 6 := act (fun a => wr1 a i s Move.right)

def setFlag (s : Sym7) : Prog Sym7 6 := act (fun a => wr1 a 5 s Move.stay)

def copyRun (i j : Fin 6) : Prog Sym7 6 := seq (copy i j isRunBody id) (cp1 i j)

/-- Back to the first cell of the current record. -/
def rewRec (i : Fin 6) : Prog Sym7 6 := seq (scanL i isBody) (mv i Move.right)

/-- Back to cell `1`. -/
def rewind (i : Fin 6) : Prog Sym7 6 := seq (scanL i notSt) (mv i Move.right)

/-- Erase tape `i` from the head down to `▷`. -/
def erase (i : Fin 6) : Prog Sym7 6 :=
  sweep (fun l => if l = i then Move.left else Move.stay) i (fun a => notSt (a i)) ()
    (fun _ _ => ((), blank))

/-- Erase a tape whose head is just past its contents; the head ends on cell `1`. -/
def wipe (i : Fin 6) : Prog Sym7 6 := seq (mv i Move.left) (seq (erase i) (mv i Move.right))

/-- Skip the common prefix of the two keys under the heads of `A` and `B`. -/
def cmp : Prog Sym7 6 :=
  loop (fun a => isBit (a 3) && decide (a 3 = a 4))
    (act (fun a => wr2 a 3 (a 3) Move.right 4 (a 4) Move.right))

/-- Emit the record under `i`; if it ends its run, finish with the rest of the run on `o`. -/
def take (i o : Fin 6) : Prog Sym7 6 :=
  seq (copy i 2 isBody id)
    (ite (fun a => decide (a i = runend))
      (seq (wsym 2 rend) (seq (mv i Move.right) (seq (copyRun o 2) (setFlag one))))
      (cp1 i 2))

def mstep : Prog Sym7 6 :=
  seq cmp (ite (fun a => decide (a 3 ≠ one))
    (seq (rewRec 3) (seq (rewRec 4) (take 3 4)))
    (seq (rewRec 3) (seq (rewRec 4) (take 4 3))))

def mergePair : Prog Sym7 6 :=
  ite (fun a => decide (a 4 = blank)) (copyRun 3 2)
    (seq (setFlag zero) (loop (fun a => decide (a 5 ≠ one)) mstep))

def mergeAll : Prog Sym7 6 := loop (fun a => decide (a 3 ≠ blank)) mergePair

def dist : Prog Sym7 6 :=
  loop (fun a => decide (a 2 ≠ blank))
    (seq (copyRun 2 3) (ite (fun a => decide (a 2 = blank)) skip (copyRun 2 4)))

def pass : Prog Sym7 6 :=
  seq (wipe 2) <| seq mergeAll <| seq (wipe 3) <| seq (wipe 4) <| seq (rewind 2) <|
  seq dist <| seq (rewind 3) (rewind 4)

def conv : Prog Sym7 6 :=
  sweep (fun l => if l = 0 ∨ l = 2 then Move.right else Move.stay) 2
    (fun a => decide (a 0 ≠ blank)) false convF

def init : Prog Sym7 6 :=
  seq (mv 5 Move.right) <| seq (mv 0 Move.right) <|
  seq (mv 2 Move.right) <| seq (mv 3 Move.right) <| seq (mv 4 Move.right) <|
  ite (fun a => decide (a 0 = blank)) skip (seq conv (wsym 2 runend))

def output : Prog Sym7 6 :=
  seq (rewind 2) (seq (mv 1 Move.right) (copy 2 1 (fun s => decide (s ≠ runend ∧ s ≠ blank)) outG))

def main : Prog Sym7 6 :=
  seq init <| seq (rewind 2) <| seq dist <| seq (rewind 3) <| seq (rewind 4) <|
  seq (loop (fun a => decide (a 4 ≠ blank)) pass) output

theorem hk6 : 2 ≤ 6 := by norm_num

/-- The sorting machine. -/
def SM : MultitapeTM := compile S7 hk6 main

end IntMul.Mach.MS

-- ===== MSOps =====


/-!
# Merge sort: basic operations on the seven-symbol alphabet
-/

namespace IntMul.Mach.MS

open IntMul IntMul.Mach Sym7

set_option linter.unusedSectionVars false

/-! ## Tape facts -/

theorem tapeOf_ne_st7 (L : List Sym7) (hL : ∀ x ∈ L, x ≠ st) (p : ℕ) (hp : 1 ≤ p) :
    tapeOf S7 L p ≠ st := tapeOf_ne_st S7 (by decide) L hL p hp

theorem tapeOf_S7_eq_st (L : List Sym7) (hL : ∀ x ∈ L, x ≠ st) (p : ℕ) (hp : tapeOf S7 L p = st) :
    p = 0 := by
  by_contra h
  exact tapeOf_ne_st7 L hL p (by omega) hp

theorem tapeOf_at7 (L R : List Sym7) (x : Sym7) : tapeOf S7 (L ++ x :: R) (L.length + 1) = x :=
  tapeOf_get S7 L R x

theorem tapeOf_get7 (L : List Sym7) (p : ℕ) (hp : p < L.length) : tapeOf S7 L (p + 1) = L[p] := by
  rw [tapeOf_succ, List.getD_eq_getElem _ _ hp]

theorem tapeOf_end7 (L : List Sym7) : tapeOf S7 L (L.length + 1) = blank := by
  rw [tapeOf_succ, List.getD_eq_default _ _ le_rfl]; rfl

theorem tapeOf_mid7 (P W R : List Sym7) (p : ℕ) (hp : p < W.length) :
    tapeOf S7 (P ++ W ++ R) (P.length + 1 + p) = W[p] := by
  rw [show P.length + 1 + p = (P.length + p) + 1 by omega, tapeOf_get7 _ _ (by simp; omega)]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem tapeOf_after7 (P W R : List Sym7) :
    tapeOf S7 (P ++ W ++ R) (P.length + 1 + W.length) = R.getD 0 blank := by
  rw [show P.length + 1 + W.length = (P ++ W).length + 1 by simp; omega, tapeOf_succ]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
    ← List.getD_eq_getElem?_getD]
  rfl

theorem notSt_of_ne {x : Sym7} (h : x ≠ st) : notSt x = true := by cases x <;> simp_all [notSt]

theorem enc_ne_st (l : List Bool) : ∀ x ∈ enc l, x ≠ st := by
  intro x hx; simp only [enc, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx; cases b <;> simp [bs]

/-! ## One-step operations -/

theorem wsym_runs (i : Fin 6) (hi0 : i.val ≠ 0) (s : Sym7) (hs : s ≠ st) (T : Tapes Sym7 6)
    (Q : List Sym7) (hc : T.cells i = tapeOf S7 Q) (hh : T.head i = Q.length + 1) :
    Runs st (wsym i s) T 1
      ⟨Function.update T.cells i (tapeOf S7 (Q ++ [s])), Function.update T.head i (Q.length + 2)⟩ := by
  have h1 := act_runs (st := st) (fun a => wr1 a i s Move.right) T
  have hT : T.cells i (T.head i) ≠ st := by rw [hc, hh, tapeOf_end7]; decide
  rw [fix_wr1 _ _ _ _ (Or.inr ⟨hi0, hT, hs⟩), write_wr1] at h1
  refine h1.of_eq ?_ rfl
  rw [hc, hh, tapeOf_append_singleton]
  rfl

theorem flag_update (F : List Sym7) (hF : F.length ≤ 1) (s : Sym7) :
    Function.update (tapeOf S7 F) 1 s = tapeOf S7 [s] := by
  rcases F with _ | ⟨x, _ | ⟨y, F⟩⟩
  · exact tapeOf_append_singleton S7 [] s
  · exact tapeOf_set S7 [] [] x s
  · simp at hF

theorem setFlag_runs (s : Sym7) (hs : s ≠ st) (T : Tapes Sym7 6) (F : List Sym7) (hF : F.length ≤ 1)
    (hF' : ∀ x ∈ F, x ≠ st) (hc : T.cells 5 = tapeOf S7 F) (hh : T.head 5 = 1) :
    Runs st (setFlag s) T 1 ⟨Function.update T.cells 5 (tapeOf S7 [s]), T.head⟩ := by
  have h1 := act_runs (st := st) (fun a => wr1 a 5 s Move.stay) T
  have hT : T.cells 5 (T.head 5) ≠ st := by rw [hc, hh]; exact tapeOf_ne_st7 F hF' 1 le_rfl
  rw [fix_wr1 _ _ _ _ (Or.inr ⟨by decide, hT, hs⟩), write_wr1] at h1
  refine h1.of_eq ?_ rfl
  rw [hc, hh, flag_update F hF]
  congr 1
  funext l; by_cases hl : l = 5
  · subst hl; simp [moveHead, hh]
  · simp [hl]

theorem cp1_runs (i j : Fin 6) (hij : i ≠ j) (hj : j.val ≠ 0) (T : Tapes Sym7 6) (x : Sym7)
    (hx : T.cells i (T.head i) = x) (hxs : x ≠ st) (Q : List Sym7)
    (hc : T.cells j = tapeOf S7 Q) (hh : T.head j = Q.length + 1) :
    Runs st (cp1 i j) T 1
      ⟨Function.update T.cells j (tapeOf S7 (Q ++ [x])),
        Function.update (Function.update T.head i (T.head i + 1)) j (Q.length + 2)⟩ := by
  have hrj : T.cells j (T.head j) = blank := by rw [hc, hh, tapeOf_end7]
  have h1 := act_runs (st := st) (fun a => wr2 a i (a i) Move.right j (a i) Move.right) T
  rw [fix_wr2 _ _ _ _ _ _ _ hij (Or.inl ⟨rfl, by simp⟩)
    (Or.inr ⟨hj, by simp [Tapes.read, hrj], by simp only [Tapes.read]; rw [hx]; exact hxs⟩),
    write_wr2 _ _ _ _ _ _ _ hij] at h1
  refine h1.of_eq ?_ rfl
  simp only [Tapes.read, Function.update_eq_self, moveHead]
  rw [hx, hc, hh, tapeOf_append_singleton]

/-! ## Copying a stretch -/

theorem copyW_runs (i j : Fin 6) (hij : i ≠ j) (hj : j.val ≠ 0) (c : Sym7 → Bool)
    (hcst : c st = false) (T : Tapes Sym7 6) (P W R Q : List Sym7)
    (hci : T.cells i = tapeOf S7 (P ++ W ++ R)) (hhi : T.head i = P.length + 1)
    (hW : ∀ x ∈ W, c x = true) (hR : c (R.getD 0 blank) = false)
    (hcj : T.cells j = tapeOf S7 Q) (hhj : T.head j = Q.length + 1) :
    Runs st (copy i j c id) T W.length
      ⟨Function.update T.cells j (tapeOf S7 (Q ++ W)),
        Function.update (Function.update T.head i (P.length + 1 + W.length)) j
          (Q.length + 1 + W.length)⟩ := by
  have h := copy_runs S7 (by decide) i j hij hj c id
    (fun x hx h' => by subst h'; change c st = true at hx; rw [hcst] at hx; exact Bool.false_ne_true hx) W Q T
    (fun p hp => by rw [hci, hhi]; exact tapeOf_mid7 P W R p hp) hW
    (by rw [hci, hhi, tapeOf_after7]; exact hR) hcj hhj
  rw [List.map_id] at h; simp only [hhi] at h
  exact h

/-! ## Encodings -/

theorem isBody_enc (l : List Bool) : ∀ x ∈ enc l, isBody x = true := by
  intro x hx; simp only [enc, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx; cases b <;> rfl

theorem isRunBody_of_isBody {x : Sym7} (h : isBody x = true) : isRunBody x = true := by
  cases x <;> simp_all [isBody, isRunBody]

/-- The body of a record (everything before its terminator). -/
def body (r : Rec) : List Sym7 := enc r.1 ++ sep :: enc r.2

theorem encR_eq (τ : Sym7) (r : Rec) : encR τ r = body r ++ [τ] := by
  simp [encR, body]

theorem isBody_body (r : Rec) : ∀ x ∈ body r, isBody x = true := by
  intro x hx
  simp only [body, List.mem_append, List.mem_cons] at hx
  rcases hx with h | h | h
  · exact isBody_enc _ x h
  · subst h; rfl
  · exact isBody_enc _ x h

theorem encRun_cons_cons (r s : Rec) (rs : List Rec) :
    encRun (r :: s :: rs) = encR rend r ++ encRun (s :: rs) := rfl

theorem encRun_split (rs : List Rec) (h : rs ≠ []) :
    ∃ B, encRun rs = B ++ [runend] ∧ ∀ x ∈ B, isRunBody x = true := by
  induction rs with
  | nil => exact absurd rfl h
  | cons r rs ih =>
    rcases rs with _ | ⟨s, rs⟩
    · exact ⟨body r, by simp [encRun, encR_eq], fun x hx => isRunBody_of_isBody (isBody_body r x hx)⟩
    · obtain ⟨B, hB, hB'⟩ := ih (by simp)
      refine ⟨body r ++ rend :: B, ?_, ?_⟩
      · rw [encRun_cons_cons, hB, encR_eq]; simp
      · intro x hx
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with h | h | h
        · exact isRunBody_of_isBody (isBody_body r x h)
        · subst h; rfl
        · exact hB' x h

theorem encRun_ne_st (rs : List Rec) : ∀ x ∈ encRun rs, x ≠ st := by
  rcases rs with _ | ⟨r, rs⟩
  · simp [encRun]
  · obtain ⟨B, hB, hB'⟩ := encRun_split (r :: rs) (by simp)
    rw [hB]; intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h | h
    · have := hB' x h; intro e; subst e; simp [isRunBody] at this
    · subst h; decide

theorem copyRun_runs (i j : Fin 6) (hij : i ≠ j) (hj : j.val ≠ 0) (T : Tapes Sym7 6)
    (P R Q : List Sym7) (rs : List Rec) (hrs : rs ≠ [])
    (hci : T.cells i = tapeOf S7 (P ++ encRun rs ++ R)) (hhi : T.head i = P.length + 1)
    (hcj : T.cells j = tapeOf S7 Q) (hhj : T.head j = Q.length + 1) :
    Runs st (copyRun i j) T (encRun rs).length
      ⟨Function.update T.cells j (tapeOf S7 (Q ++ encRun rs)),
        Function.update (Function.update T.head i (P.length + 1 + (encRun rs).length)) j
          (Q.length + 1 + (encRun rs).length)⟩ := by
  obtain ⟨B, hB, hB'⟩ := encRun_split rs hrs
  rw [hB] at hci ⊢
  have h1 := copyW_runs i j hij hj isRunBody rfl T P B ([runend] ++ R) Q
    (by rw [hci]; simp) hhi hB' rfl hcj hhj
  have h2 := cp1_runs i j hij hj ⟨Function.update T.cells j (tapeOf S7 (Q ++ B)),
      Function.update (Function.update T.head i (P.length + 1 + B.length)) j (Q.length + 1 + B.length)⟩
      runend (by
      show (Function.update T.cells j _) i ((Function.update (Function.update T.head i _) j _) i) = runend
      rw [Function.update_of_ne hij, Function.update_of_ne hij, Function.update_self, hci,
        show P.length + 1 + B.length = (P ++ B).length + 1 by simp; omega,
        show P ++ (B ++ [runend]) ++ R = (P ++ B) ++ runend :: R by simp]
      exact tapeOf_get S7 _ _ _) (by decide) (Q ++ B) (by simp) (by simp; omega)
  refine (seq_runs h1 h2).of_eq ?_ (by simp)
  congr 1
  · funext l; by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  · funext l; by_cases hl : l = j
    · subst hl; simp; omega
    · by_cases hl' : l = i
      · subst hl'; simp [hl]; omega
      · simp [hl, hl']

/-! ## Rewinding -/

theorem rewind_runs (i : Fin 6) (T : Tapes Sym7 6) (W : List Sym7) (hW : ∀ x ∈ W, x ≠ st)
    (hc : T.cells i = tapeOf S7 W) :
    Runs st (rewind i) T (T.head i + 1) ⟨T.cells, Function.update T.head i 1⟩ := by
  have h1 := scanL_runs st i notSt (T.head i) T le_rfl
    (fun p hp => by
      rw [hc]
      have := tapeOf_ne_st7 W hW (T.head i - p) (by omega)
      exact ⟨notSt_of_ne this, this⟩)
    (by rw [hc, Nat.sub_self]; rfl)
  have h2 := mv_runs st i Move.right ⟨T.cells, Function.update T.head i (T.head i - T.head i)⟩
    (by simp)
  refine (seq_runs h1 h2).of_eq ?_ (by omega)
  simp [moveHead]

theorem rewRec_runs (i : Fin 6) (T : Tapes Sym7 6) (P B R : List Sym7) (d : ℕ) (hd : d < B.length)
    (hB : ∀ x ∈ B, isBody x = true) (hP : isBody (T.cells i P.length) = false)
    (hc : T.cells i = tapeOf S7 (P ++ B ++ R)) (hh : T.head i = P.length + 1 + d) :
    Runs st (rewRec i) T (d + 2) ⟨T.cells, Function.update T.head i (P.length + 1)⟩ := by
  have h1 := scanL_runs st i isBody (d + 1) T (by omega)
    (fun p hp => by
      rw [hc, hh, show P.length + 1 + d - p = P.length + 1 + (d - p) by omega,
        tapeOf_mid7 P B R _ (by omega)]
      have := hB _ (List.getElem_mem (l := B) (n := d - p) (by omega))
      refine ⟨this, fun e => ?_⟩
      rw [e] at this; exact Bool.false_ne_true this)
    (by rw [hh, show P.length + 1 + d - (d + 1) = P.length by omega]; exact hP)
  have h2 := mv_runs st i Move.right ⟨T.cells, Function.update T.head i (T.head i - (d + 1))⟩
    (by simp)
  refine (seq_runs h1 h2).of_eq ?_ (by omega)
  congr 1
  funext l; by_cases hl : l = i
  · subst hl; simp [moveHead]; rw [hh]; omega
  · simp [hl]

/-! ## Erasing -/

theorem erase_runs (i : Fin 6) (hi0 : i.val ≠ 0) (T : Tapes Sym7 6) (W : List Sym7)
    (hW : ∀ x ∈ W, x ≠ st) (hc : T.cells i = tapeOf S7 W) (hh : T.head i = W.length) :
    Runs st (erase i) T W.length
      ⟨Function.update T.cells i (tapeOf S7 []), Function.update T.head i 0⟩ := by
  set d : Fin 6 → Move := fun l => if l = i then Move.left else Move.stay with hd
  have hdi : d i = Move.left := by simp [hd]
  have hrd : ∀ m, rd T d m i = tapeOf S7 W (W.length - m) := by
    intro m; simp only [rd, hdi, offs, hc, hh]
  have hWm : ∀ m < W.length, tapeOf S7 W (W.length - m) ≠ st :=
    fun m hm => tapeOf_ne_st7 W hW _ (by omega)
  have h := sweep_runs st d i (fun a => notSt (a i)) () (fun _ _ => ((), blank)) T W.length hi0
    (by simp [hdi]) (fun _ => by omega)
    (fun l p hl hp => by
      by_cases h1 : l = i
      · subst h1; rw [hc] at hp; exact tapeOf_S7_eq_st _ hW p hp
      · simp [hd, h1] at hl)
    (fun m hm => by rw [hrd]; exact notSt_of_ne (hWm m hm))
    (by rw [hrd, Nat.sub_self]; rfl)
    (fun m hm => by rw [hrd]; exact hWm m hm)
    (fun m _ => by simp [sout])
  refine Runs.of_eq h ?_ rfl
  congr 1
  · congr 1
    funext p
    rw [hdi, dcells_left _ _ _ _ _ (by omega), hh, hc]
    have := congrFun (tapeOf_write_left S7 [] W [] (sout (fun _ _ => ((), blank)) (rd T d) ())) p
    simp only [List.length_nil, Nat.zero_add, List.nil_append, List.append_nil] at this
    rw [Nat.sub_self, this]
    have e : (List.ofFn fun m : Fin W.length =>
        sout (fun _ _ => ((), blank)) (rd T d) () (W.length - 1 - m)) =
        List.replicate W.length blank := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2; simp [sout]
    rw [e]
    have := tapeOf_append_blanks S7 [] W.length
    rw [List.nil_append] at this
    exact congrFun this p
  · funext l
    by_cases h1 : l = i
    · subst h1; simp [hdi, offs, hh]
    · simp [hd, h1, offs]

theorem wipe_runs (i : Fin 6) (hi0 : i.val ≠ 0) (T : Tapes Sym7 6) (W : List Sym7)
    (hW : ∀ x ∈ W, x ≠ st) (hc : T.cells i = tapeOf S7 W) (hh : T.head i = W.length + 1) :
    Runs st (wipe i) T (W.length + 2)
      ⟨Function.update T.cells i (tapeOf S7 []), Function.update T.head i 1⟩ := by
  have h1 := mv_runs st i Move.left T (by intro _; rw [hc, hh, tapeOf_end7]; decide)
  have h2 := erase_runs i hi0 ⟨T.cells, Function.update T.head i (moveHead Move.left (T.head i))⟩
    W hW hc (by simp [moveHead, hh])
  have h3 := mv_runs st i Move.right ⟨Function.update T.cells i (tapeOf S7 []),
    Function.update (Function.update T.head i (moveHead Move.left (T.head i))) i 0⟩ (fun h => by cases h)
  refine (seq_runs h1 (seq_runs h2 h3)).of_eq ?_ (by omega)
  simp [moveHead]

end IntMul.Mach.MS

-- ===== MSortMath =====


namespace IntMul.Mach.MSort
open IntMul

/-! ## 1. Stable merge sort splits over append -/

section MergeSortAppend
variable {α : Type*}

theorem mergeSort_zipIdx_from (le : α → α → Bool) (k : ℕ) (l : List α) :
    ((l.zipIdx k).mergeSort (List.zipIdxLE le)).map (·.1) = l.mergeSort le := by
  have h : l.zipIdx k = l.zipIdx.map (Prod.map id (· + k)) := by
    simpa using (List.map_snd_add_zipIdx_eq_zipIdx (l := l) (n := k) (k := 0)).symm
  rw [h, ← List.map_mergeSort (r := List.zipIdxLE le), List.map_map]
  · conv_rhs => rw [← List.mergeSort_zipIdx]
    rfl
  · rintro ⟨x, i⟩ _ ⟨y, j⟩ _
    simp [List.zipIdxLE]

theorem mergeSort_append (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (a b : List α) :
    (a ++ b).mergeSort le = List.merge (a.mergeSort le) (b.mergeSort le) le := by
  rw [← List.mergeSort_zipIdx, ← mergeSort_zipIdx_from le a.length b,
    ← List.mergeSort_zipIdx (l := a)]
  rw [← List.merge_stable]
  · congr 1
    apply List.Perm.eq_of_pairwise (le := fun x y => List.zipIdxLE le x y)
    · rintro ⟨x, i⟩ ⟨y, j⟩ hx hy h1 h2
      simp only [List.mem_mergeSort] at hx
      have hy' : (y, j) ∈ (a ++ b).zipIdx := by
        have p : List.Perm (List.merge ((a.zipIdx).mergeSort (List.zipIdxLE le))
            ((b.zipIdx a.length).mergeSort (List.zipIdxLE le)) (List.zipIdxLE le))
            (a ++ b).zipIdx := by
          refine List.Perm.trans (List.merge_perm_append _) ?_
          rw [List.zipIdx_append, Nat.zero_add]
          exact List.Perm.append (List.mergeSort_perm _ _) (List.mergeSort_perm _ _)
        exact p.mem_iff.mp hy
      simp only [List.zipIdxLE] at h1 h2
      have hij : i = j := by
        by_cases hxy : le x y <;> by_cases hyx : le y x <;> simp_all <;> omega
      subst hij
      have := List.mem_zipIdx hx
      have := List.mem_zipIdx hy'
      simp_all
    · exact List.pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _
    · exact List.pairwise_merge (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _ _
        (List.pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _)
        (List.pairwise_mergeSort (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) _)
    · refine (List.mergeSort_perm _ _).trans ?_
      refine List.Perm.trans ?_ (List.Perm.symm (List.merge_perm_append _))
      rw [List.zipIdx_append, Nat.zero_add]
      exact List.Perm.append (List.mergeSort_perm _ _).symm (List.mergeSort_perm _ _).symm
  · rintro ⟨x, i⟩ ⟨y, j⟩ hx hy
    simp only [List.mem_mergeSort] at hx hy
    have := List.mem_zipIdx hx
    have := List.mem_zipIdx hy
    simp only at *
    omega

end MergeSortAppend

/-! ## 2. Pairing up chunks -/

section Pairing
variable {α : Type*}

/-- Concatenate adjacent pairs of chunks. -/
def pairUp : List (List α) → List (List α)
  | a :: b :: rest => (a ++ b) :: pairUp rest
  | rs => rs

/-- Merge adjacent pairs of (sorted) chunks. -/
def mergePairs (le : α → α → Bool) : List (List α) → List (List α)
  | a :: b :: rest => List.merge a b le :: mergePairs le rest
  | rs => rs

theorem flatten_pairUp (cs : List (List α)) : (pairUp cs).flatten = cs.flatten := by
  induction cs using pairUp.induct with
  | case1 a b rest ih => simp [pairUp, ih]
  | case2 rs h =>
    match rs, h with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, h => exact absurd rfl (h _ _ _)

theorem length_pairUp (cs : List (List α)) : (pairUp cs).length = (cs.length + 1) / 2 := by
  induction cs using pairUp.induct with
  | case1 a b rest ih => simp [pairUp, ih]; omega
  | case2 rs h =>
    match rs, h with
    | [], _ => simp [pairUp]
    | [_], _ => simp [pairUp]
    | _ :: _ :: _, h => exact absurd rfl (h _ _ _)

theorem mergePairs_map (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (cs : List (List α)) :
    mergePairs le (cs.map (·.mergeSort le)) = (pairUp cs).map (·.mergeSort le) := by
  induction cs using pairUp.induct with
  | case1 a b rest ih =>
    simp only [List.map_cons, mergePairs, pairUp, ih, mergeSort_append le trans total]
  | case2 rs h =>
    match rs, h with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, h => exact absurd rfl (h _ _ _)

theorem iterate_pairUp_flatten (k : ℕ) (cs : List (List α)) :
    (pairUp^[k] cs).flatten = cs.flatten := by
  induction k generalizing cs with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, flatten_pairUp]

theorem iterate_mergePairs (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (k : ℕ) (cs : List (List α)) :
    (mergePairs le)^[k] (cs.map (·.mergeSort le)) = (pairUp^[k] cs).map (·.mergeSort le) := by
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      mergePairs_map le trans total, ih]

theorem iterate_pairUp_length_of_le (k : ℕ) (cs : List (List α))
    (h1 : 1 ≤ cs.length) (h2 : cs.length ≤ 2 ^ k) : (pairUp^[k] cs).length = 1 := by
  induction k generalizing cs with
  | zero => simp at h2; simp; omega
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    · rw [length_pairUp]; omega
    · rw [length_pairUp]; rw [pow_succ] at h2; omega

theorem iterate_pairUp_length (cs : List (List α)) (m : ℕ) (h : cs.length = m) (hm : 1 ≤ m) :
    ((pairUp)^[Nat.clog 2 m] cs).length = 1 :=
  iterate_pairUp_length_of_le _ cs (h ▸ hm) (h ▸ Nat.le_pow_clog (by norm_num : 1 < 2) m)

theorem mergeSort_of_singleton_chunks (le : α → α → Bool) (l : List α) :
    (l.map (fun x => [x])).map (·.mergeSort le) = l.map (fun x => [x]) := by
  simp

end Pairing

/-! ## 3. Lexicographic comparison of equal-length bit strings -/

theorem val_foldl (x : List Bool) (n : ℕ) :
    x.foldl (fun a b => 2 * a + b.toNat) n = n * 2 ^ x.length + val x := by
  induction x generalizing n with
  | nil => simp [val]
  | cons b x ih =>
    have e : val (b :: x) = (2 * 0 + b.toNat) * 2 ^ x.length + val x := by
      rw [← ih]; rfl
    rw [List.foldl_cons, ih, e, List.length_cons]
    ring

@[simp] theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (x : List Bool) : val (b :: x) = b.toNat * 2 ^ x.length + val x := by
  rw [show val (b :: x) = x.foldl (fun a b => 2 * a + b.toNat) (2 * 0 + b.toNat) from rfl,
    val_foldl]; simp

theorem val_append (a b : List Bool) : val (a ++ b) = val a * 2 ^ b.length + val b := by
  rw [show val (a ++ b) = b.foldl (fun a b => 2 * a + b.toNat) (val a) from
    List.foldl_append .., val_foldl]

theorem val_lt (x : List Bool) : val x < 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [val_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- `true` iff `a ≤ b` lexicographically with `false < true` (decided at the first differing bit). -/
def lexLe : List Bool → List Bool → Bool
  | a :: as, b :: bs => if a = b then lexLe as bs else (b && !a)
  | _, _ => true

theorem lexLe_iff (a b : List Bool) (h : a.length = b.length) :
    lexLe a b = decide (val a ≤ val b) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x as ih =>
    cases b with
    | nil => simp at h
    | cons y bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have ha := val_lt as
      have hb := val_lt bs
      simp only [lexLe, val_cons]
      rw [h] at ha ⊢
      by_cases hxy : x = y
      · subst hxy; rw [if_pos rfl, ih bs h]; simp
      · rw [if_neg hxy]
        cases x <;> cases y <;> simp_all <;> omega

theorem recLe_trans : ∀ a b c : List Bool × List Bool,
    (fun (r s : List Bool × List Bool) => decide (val r.1 ≤ val s.1)) a b →
    (fun (r s : List Bool × List Bool) => decide (val r.1 ≤ val s.1)) b c →
    (fun (r s : List Bool × List Bool) => decide (val r.1 ≤ val s.1)) a c := by
  intro a b c h1 h2
  simp only [decide_eq_true_eq] at *
  omega

theorem recLe_total : ∀ a b : List Bool × List Bool,
    ((fun (r s : List Bool × List Bool) => decide (val r.1 ≤ val s.1)) a b ||
      (fun (r s : List Bool × List Bool) => decide (val r.1 ≤ val s.1)) b a) := by
  intro a b
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

end IntMul.Mach.MSort

-- ===== MSCmp =====


/-!
# Merge sort: comparing two keys
-/

namespace IntMul.Mach.MS

open IntMul IntMul.Mach Sym7 IntMul.Mach.MSort

set_option linter.unusedSectionVars false

theorem cmp_step (T : Tapes Sym7 6) :
    Runs st (act (fun a => wr2 a 3 (a 3) Move.right 4 (a 4) Move.right) : Prog Sym7 6) T 1
      ⟨T.cells, Function.update (Function.update T.head 3 (T.head 3 + 1)) 4 (T.head 4 + 1)⟩ := by
  have h1 := act_runs (st := st) (fun a => wr2 a 3 (a 3) Move.right 4 (a 4) Move.right) T
  rw [fix_wr2 _ _ _ _ _ _ _ (by decide) (Or.inl ⟨rfl, by simp⟩) (Or.inl ⟨rfl, by simp⟩),
    write_wr2 _ _ _ _ _ _ _ (by decide)] at h1
  refine h1.of_eq ?_ rfl
  simp only [Tapes.read, Function.update_eq_self, moveHead]

theorem bs_ne_one (b : Bool) : decide (bs b ≠ one) = !b := by cases b <;> rfl

theorem cmp_aux (kx : List Bool) :
    ∀ (ky : List Bool), kx.length = ky.length → ∀ (T : Tapes Sym7 6),
      (∀ p ≤ kx.length, T.cells 3 (T.head 3 + p) = (enc kx ++ [sep]).getD p blank) →
      (∀ p ≤ ky.length, T.cells 4 (T.head 4 + p) = (enc ky ++ [sep]).getD p blank) →
      ∃ d ≤ kx.length, Runs st cmp T d
        ⟨T.cells, Function.update (Function.update T.head 3 (T.head 3 + d)) 4 (T.head 4 + d)⟩ ∧
        decide (T.cells 3 (T.head 3 + d) ≠ one) = lexLe kx ky := by
  induction kx with
  | nil =>
    intro ky hl T hA _
    obtain rfl : ky = [] := List.eq_nil_of_length_eq_zero hl.symm
    have h3 : T.cells 3 (T.head 3) = sep := by simpa [enc] using hA 0 (by simp)
    refine ⟨0, le_rfl, (loop_stop (by simp [Tapes.read, h3, isBit])).of_eq ?_ rfl, ?_⟩
    · simp
    · simp [h3, lexLe]
  | cons a kx ih =>
    intro ky hl T hA hB
    obtain ⟨b, ky, rfl⟩ : ∃ b ky', ky = b :: ky' := by
      rcases ky with _ | ⟨b, ky⟩
      · simp at hl
      · exact ⟨b, ky, rfl⟩
    have h3 : T.cells 3 (T.head 3) = bs a := by simpa [enc] using hA 0 (by simp)
    have h4 : T.cells 4 (T.head 4) = bs b := by simpa [enc] using hB 0 (by simp)
    by_cases hab : a = b
    · subst hab
      have hc := cmp_step T
      obtain ⟨d, hd, hr, hdec⟩ := ih ky (by simpa using hl)
        ⟨T.cells, Function.update (Function.update T.head 3 (T.head 3 + 1)) 4 (T.head 4 + 1)⟩
        (fun p hp => by
          have := hA (p + 1) (by simp; omega)
          simp only [Function.update_of_ne (show (3 : Fin 6) ≠ 4 by decide), Function.update_self]
          rw [show T.head 3 + 1 + p = T.head 3 + (p + 1) by omega, this]
          simp [enc, List.getD_eq_getElem?_getD])
        (fun p hp => by
          have := hB (p + 1) (by simp; omega)
          simp only [Function.update_self]
          rw [show T.head 4 + 1 + p = T.head 4 + (p + 1) by omega, this]
          simp [enc, List.getD_eq_getElem?_getD])
      refine ⟨1 + d, by simp; omega, ?_, ?_⟩
      · have := loop_iter (c := fun a => isBit (a 3) && decide (a 3 = a 4))
          (by simp [Tapes.read, h3, h4]; cases a <;> rfl) (by omega) hc hr
        refine this.of_eq ?_ rfl
        congr 1
        funext l
        by_cases h3l : l = 3
        · subst h3l; simp; omega
        · by_cases h4l : l = 4
          · subst h4l; simp; omega
          · simp [h3l, h4l]
      · simp only [Function.update_of_ne (show (3 : Fin 6) ≠ 4 by decide), Function.update_self]
          at hdec
        rw [show T.head 3 + (1 + d) = T.head 3 + 1 + d by omega, hdec]
        simp [lexLe]
    · refine ⟨0, by simp, (loop_stop ?_).of_eq ?_ rfl, ?_⟩
      · simp only [Tapes.read, h3, h4]
        cases a <;> cases b <;> simp_all [isBit, bs]
      · simp
      · simp only [Nat.add_zero, h3, bs_ne_one, lexLe, if_neg hab]
        cases a <;> cases b <;> simp_all

/-- Comparing the keys of the records under `A` and `B`. -/
theorem cmp_runs (T : Tapes Sym7 6) (x y : Rec) (hl : x.1.length = y.1.length)
    (PA RA PB RB : List Sym7)
    (hA : T.cells 3 = tapeOf S7 (PA ++ body x ++ RA)) (hhA : T.head 3 = PA.length + 1)
    (hB : T.cells 4 = tapeOf S7 (PB ++ body y ++ RB)) (hhB : T.head 4 = PB.length + 1) :
    ∃ d ≤ x.1.length, Runs st cmp T d
        ⟨T.cells, Function.update (Function.update T.head 3 (PA.length + 1 + d)) 4
          (PB.length + 1 + d)⟩ ∧
      decide (T.cells 3 (PA.length + 1 + d) ≠ one) = decide (val x.1 ≤ val y.1) := by
  have key : ∀ (k : List Bool) (q : List Bool) (P R : List Sym7) (p : ℕ), p ≤ k.length →
      tapeOf S7 (P ++ (enc k ++ sep :: enc q) ++ R) (P.length + 1 + p) =
        (enc k ++ [sep]).getD p blank := by
    intro k q P R p hp
    have hek : (enc k).length = k.length := by simp [enc]
    rw [tapeOf_mid7 P _ R p (by simp only [List.length_append, List.length_cons]; omega)]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_append, List.length_singleton]; omega)]
    by_cases hpk : p < k.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
    · obtain rfl : p = k.length := by omega
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp [hek]
  obtain ⟨d, hd, hr, hdec⟩ := cmp_aux x.1 y.1 hl T
    (fun p hp => by rw [hA, hhA]; exact key _ _ _ _ p hp)
    (fun p hp => by rw [hB, hhB]; exact key _ _ _ _ p hp)
  refine ⟨d, hd, by rw [hhA, hhB] at hr; exact hr, ?_⟩
  rw [hhA] at hdec; rw [hdec, lexLe_iff _ _ hl]

end IntMul.Mach.MS

-- ===== MSMerge =====


/-!
# Merge sort: merging two runs
-/

namespace IntMul.Mach.MS

open IntMul IntMul.Mach Sym7 IntMul.Mach.MSort

set_option linter.unusedSectionVars false

theorem length_encR (τ : Sym7) (r : Rec) : (encR τ r).length = (body r).length + 1 := by
  simp [encR_eq]

theorem encRun_cons_ne (r : Rec) (rs : List Rec) (h : rs ≠ []) :
    encRun (r :: rs) = encR rend r ++ encRun rs := by
  rcases rs with _ | ⟨s, rs⟩
  · exact absurd rfl h
  · rfl

theorem encRun_single (r : Rec) : encRun [r] = body r ++ [runend] := by
  simp [encRun, encR_eq]

/-- Emitting a record that does not end its run. -/
theorem take_cont_runs (i o : Fin 6) (hi2 : i ≠ 2) (hi0 : i.val ≠ 0) (T : Tapes Sym7 6) (x : Rec)
    (rest : List Rec) (hrest : rest ≠ []) (P R Q : List Sym7)
    (hci : T.cells i = tapeOf S7 (P ++ encRun (x :: rest) ++ R)) (hhi : T.head i = P.length + 1)
    (hcC : T.cells 2 = tapeOf S7 Q) (hhC : T.head 2 = Q.length + 1) :
    Runs st (take i o) T (encR rend x).length
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encR rend x)),
        Function.update (Function.update T.head i (P.length + 1 + (encR rend x).length)) 2
          (Q.length + 1 + (encR rend x).length)⟩ := by
  rw [encRun_cons_ne _ _ hrest, encR_eq] at hci
  have h1 := copyW_runs i 2 hi2 (by decide) isBody rfl T P (body x) (rend :: (encRun rest ++ R)) Q
    (by rw [hci]; simp) hhi (isBody_body x) rfl hcC hhC
  have hrd' : T.cells i (P.length + 1 + (body x).length) = rend := by
    rw [hci, show P.length + 1 + (body x).length = (P ++ body x).length + 1 by simp; omega,
      show P ++ (body x ++ [rend] ++ encRun rest) ++ R = (P ++ body x) ++ rend :: (encRun rest ++ R)
        by simp]
    exact tapeOf_get S7 _ _ _
  have hrd : (⟨Function.update T.cells 2 (tapeOf S7 (Q ++ body x)),
      Function.update (Function.update T.head i (P.length + 1 + (body x).length)) 2
        (Q.length + 1 + (body x).length)⟩ : Tapes Sym7 6).cells i
      ((Function.update (Function.update T.head i (P.length + 1 + (body x).length)) 2
        (Q.length + 1 + (body x).length)) i) = rend := by
    simp only [Function.update_of_ne hi2, Function.update_self]; exact hrd'
  have h2 := cp1_runs i 2 hi2 (by decide) _ rend hrd (by decide) (Q ++ body x) (by simp)
    (by simp; omega)
  have h3 := ite_runs_false (c := fun a => decide (a i = runend))
    (P₁ := seq (wsym 2 rend) (seq (mv i Move.right) (seq (copyRun o 2) (setFlag one))))
    (by simp [Tapes.read, Function.update_of_ne hi2]; rw [hrd']; decide) h2
  refine (seq_runs h1 h3).of_eq ?_ (by rw [length_encR])
  rw [encR_eq]
  congr 1
  · funext l; by_cases hl : l = 2
    · subst hl; simp
    · simp [hl]
  · funext l; by_cases hl : l = 2
    · subst hl; simp; omega
    · by_cases hl' : l = i
      · subst hl'; simp [hl]; omega
      · simp [hl, hl']

/-- Emitting the last record of a run, then the rest of the other run. -/
theorem take_last_runs (i o : Fin 6) (hi2 : i ≠ 2) (ho2 : o ≠ 2) (hio : i ≠ o) (hi5 : i ≠ 5)
    (ho5 : o ≠ 5) (hi0 : i.val ≠ 0) (T : Tapes Sym7 6) (x : Rec) (b : List Rec) (hb : b ≠ [])
    (P R PO RO Q F : List Sym7) (hF : F.length ≤ 1) (hF' : ∀ s ∈ F, s ≠ st)
    (hci : T.cells i = tapeOf S7 (P ++ encRun [x] ++ R)) (hhi : T.head i = P.length + 1)
    (hco : T.cells o = tapeOf S7 (PO ++ encRun b ++ RO)) (hho : T.head o = PO.length + 1)
    (hcC : T.cells 2 = tapeOf S7 Q) (hhC : T.head 2 = Q.length + 1)
    (hcF : T.cells 5 = tapeOf S7 F) (hhF : T.head 5 = 1) :
    Runs st (take i o) T ((body x).length + 3 + (encRun b).length)
      ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ encR rend x ++ encRun b))) 5
          (tapeOf S7 [one]),
        Function.update (Function.update (Function.update T.head i
          (P.length + 1 + (encR rend x).length)) o (PO.length + 1 + (encRun b).length)) 2
          (Q.length + 1 + (encR rend x).length + (encRun b).length)⟩ := by
  rw [encRun_single] at hci
  have h1 := copyW_runs i 2 hi2 (by decide) isBody rfl T P (body x) (runend :: R) Q
    (by rw [hci]; simp) hhi (isBody_body x) rfl hcC hhC
  set T1 : Tapes Sym7 6 := ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ body x)),
      Function.update (Function.update T.head i (P.length + 1 + (body x).length)) 2
        (Q.length + 1 + (body x).length)⟩ with hT1
  have hrd : T1.cells i (T1.head i) = runend := by
    simp only [hT1, Function.update_of_ne hi2, Function.update_self]
    rw [hci, show P.length + 1 + (body x).length = (P ++ body x).length + 1 by simp; omega,
      show P ++ (body x ++ [runend]) ++ R = (P ++ body x) ++ runend :: R by simp]
    exact tapeOf_get S7 _ _ _
  have h2 := wsym_runs 2 (by decide) rend (by decide) T1 (Q ++ body x) (by simp [hT1])
    (by simp [hT1]; omega)
  set T2 : Tapes Sym7 6 := ⟨Function.update T1.cells 2 (tapeOf S7 (Q ++ body x ++ [rend])),
    Function.update T1.head 2 ((Q ++ body x).length + 2)⟩ with hT2
  have h3 := mv_runs st i Move.right T2 (fun h => by cases h)
  set T3 : Tapes Sym7 6 := ⟨T2.cells, Function.update T2.head i (moveHead Move.right (T2.head i))⟩
    with hT3
  have h4 := copyRun_runs o 2 ho2 (by decide) T3 PO RO (Q ++ body x ++ [rend]) b hb
    (by simp [hT3, hT2, hT1, Function.update_of_ne ho2, hco])
    (by simp [hT3, hT2, hT1, Function.update_of_ne ho2, Function.update_of_ne (Ne.symm hio), hho])
    (by simp [hT3, hT2]) (by simp [hT3, hT2, Function.update_of_ne hi2.symm]; omega)
  set T4 : Tapes Sym7 6 := ⟨Function.update T3.cells 2 (tapeOf S7 (Q ++ body x ++ [rend] ++ encRun b)),
    Function.update (Function.update T3.head o (PO.length + 1 + (encRun b).length)) 2
      ((Q ++ body x ++ [rend]).length + 1 + (encRun b).length)⟩ with hT4
  have h5 := setFlag_runs one (by decide) T4 F hF hF'
    (by simp [hT4, hT3, hT2, hT1, hcF]) (by simp [hT4, hT3, hT2, hT1, hhF, Function.update_of_ne hi5.symm, Function.update_of_ne ho5.symm])
  have h6 := ite_runs_true (c := fun a => decide (a i = runend)) (P₂ := cp1 i 2)
    (show decide (T1.read i = runend) = true by simp [Tapes.read, hrd])
    (seq_runs h2 (seq_runs h3 (seq_runs h4 h5)))
  refine (seq_runs h1 h6).of_eq ?_ (by omega)
  simp only [hT4, hT3, hT2, hT1, encR_eq]
  congr 1
  · funext l
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · funext l
    simp only [Function.update_apply, moveHead]
    split_ifs <;> simp_all <;> omega


theorem length_body (r : Rec) : (body r).length = r.1.length + 1 + r.2.length := by
  simp [body, enc]; omega

/-- One merge step: compare, rewind, and hand over to `take`. -/
theorem mstep_dispatch (T : Tapes Sym7 6) (x y : Rec) (hl : x.1.length = y.1.length)
    (PA RA PB RB : List Sym7)
    (hA : T.cells 3 = tapeOf S7 (PA ++ body x ++ RA)) (hhA : T.head 3 = PA.length + 1)
    (hB : T.cells 4 = tapeOf S7 (PB ++ body y ++ RB)) (hhB : T.head 4 = PB.length + 1)
    (hPA : isBody (T.cells 3 PA.length) = false) (hPB : isBody (T.cells 4 PB.length) = false) :
    ∃ d ≤ x.1.length,
      (decide (val x.1 ≤ val y.1) = true → ∀ t T', Runs st (take 3 4) T t T' →
        Runs st mstep T (3 * d + 4 + t) T') ∧
      (decide (val x.1 ≤ val y.1) = false → ∀ t T', Runs st (take 4 3) T t T' →
        Runs st mstep T (3 * d + 4 + t) T') := by
  obtain ⟨d, hd, hr, hdec⟩ := cmp_runs T x y hl PA RA PB RB hA hhA hB hhB
  set Tc : Tapes Sym7 6 := ⟨T.cells, Function.update (Function.update T.head 3 (PA.length + 1 + d)) 4
    (PB.length + 1 + d)⟩ with hTc
  have r3 := rewRec_runs 3 Tc PA (body x) RA d (by rw [length_body]; omega) (isBody_body x) hPA hA
    (by simp [hTc])
  have r4 := rewRec_runs 4 ⟨Tc.cells, Function.update Tc.head 3 (PA.length + 1)⟩ PB (body y) RB d
    (by rw [length_body]; omega) (isBody_body y) hPB hB (by simp [hTc])
  have eT : (⟨Tc.cells, Function.update (Function.update Tc.head 3 (PA.length + 1)) 4 (PB.length + 1)⟩ :
      Tapes Sym7 6) = T := by
    cases T with
    | mk c h =>
      simp only [hTc, Tapes.mk.injEq, true_and]
      funext l
      simp only [Function.update_apply]
      split_ifs with h1 h2 h3 <;> simp_all
  rw [eT] at r4
  have hread : Tc.read 3 = T.cells 3 (PA.length + 1 + d) := by simp [hTc, Tapes.read]
  refine ⟨d, hd, fun hle t T' ht => ?_, fun hle t T' ht => ?_⟩
  · have := seq_runs hr (ite_runs_true (c := fun a => decide (a 3 ≠ one))
      (P₂ := seq (rewRec 3) (seq (rewRec 4) (take 4 3)))
      (by simp only [hread]; rw [hdec, hle]) (seq_runs r3 (seq_runs r4 ht)))
    exact this.of_eq rfl (by omega)
  · have := seq_runs hr (ite_runs_false (c := fun a => decide (a 3 ≠ one))
      (P₁ := seq (rewRec 3) (seq (rewRec 4) (take 3 4)))
      (by simp only [hread]; rw [hdec, hle]) (seq_runs r3 (seq_runs r4 ht)))
    exact this.of_eq rfl (by omega)


/-! ## The merge loop -/

/-- The record order. -/
def le7 (r s : Rec) : Bool := decide (val r.1 ≤ val s.1)

theorem encRun_cons_body (x : Rec) (a : List Rec) :
    encRun (x :: a) = body x ++ ((if a = [] then runend else rend) :: encRun a) := by
  rcases a with _ | ⟨y, a⟩
  · simp [encRun, encR_eq]
  · simp [encRun, encR_eq]

theorem length_encRun_cons (x : Rec) (a : List Rec) :
    (encRun (x :: a)).length = (body x).length + 1 + (encRun a).length := by
  rw [encRun_cons_body]; simp; omega

theorem merge_ne_nil (a b : List Rec) (h : a ≠ [] ∨ b ≠ []) : List.merge a b le7 ≠ [] := by
  intro e
  have := congrArg List.length e
  rw [List.length_merge, List.length_nil] at this
  rcases h with h | h
  · exact h (List.eq_nil_of_length_eq_zero (by omega))
  · exact h (List.eq_nil_of_length_eq_zero (by omega))

/-- What a finished merge loop leaves behind. -/
def MergeOut (T T' : Tapes Sym7 6) (Q PA PB : List Sym7) (a b : List Rec) : Prop :=
  T'.cells 2 = tapeOf S7 (Q ++ encRun (List.merge a b le7)) ∧
  T'.head 2 = Q.length + 1 + (encRun (List.merge a b le7)).length ∧
  T'.head 3 = PA.length + 1 + (encRun a).length ∧
  T'.head 4 = PB.length + 1 + (encRun b).length ∧
  T'.cells 5 = tapeOf S7 [one] ∧ T'.head 5 = 1 ∧
  (∀ l : Fin 6, l ≠ 2 → l ≠ 5 → T'.cells l = T.cells l) ∧
  (∀ l : Fin 6, l.val < 2 → T'.head l = T.head l)

def flagc (a : Fin 6 → Sym7) : Bool := decide (a 5 ≠ one)

theorem tapeOf_at_len (P W : List Sym7) (s : Sym7) :
    tapeOf S7 (P ++ s :: W) (P.length + 1) = s := tapeOf_get S7 _ _ _

set_option maxHeartbeats 1000000 in
theorem mergeLoop_runs (ℓ : ℕ) : ∀ (n : ℕ) (a b : List Rec), a.length + b.length = n →
    a ≠ [] → b ≠ [] → (∀ r ∈ a, r.1.length = ℓ) → (∀ r ∈ b, r.1.length = ℓ) →
    ∀ (T : Tapes Sym7 6) (PA RA PB RB Q : List Sym7),
    T.cells 3 = tapeOf S7 (PA ++ encRun a ++ RA) → T.head 3 = PA.length + 1 →
    isBody (T.cells 3 PA.length) = false →
    T.cells 4 = tapeOf S7 (PB ++ encRun b ++ RB) → T.head 4 = PB.length + 1 →
    isBody (T.cells 4 PB.length) = false →
    T.cells 2 = tapeOf S7 Q → T.head 2 = Q.length + 1 →
    T.cells 5 = tapeOf S7 [zero] → T.head 5 = 1 →
    ∃ t ≤ 5 * ((encRun a).length + (encRun b).length), ∃ T',
      Runs st (loop flagc mstep) T t T' ∧ MergeOut T T' Q PA PB a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb hla hlb T PA RA PB RB Q hA hhA hPA hB hhB hPB hC hhC hF hhF
  obtain ⟨x, a', rfl⟩ : ∃ x a', a = x :: a' := by
    rcases a with _ | ⟨x, a'⟩
    · exact absurd rfl ha
    · exact ⟨x, a', rfl⟩
  obtain ⟨y, b', rfl⟩ : ∃ y b', b = y :: b' := by
    rcases b with _ | ⟨y, b'⟩
    · exact absurd rfl hb
    · exact ⟨y, b', rfl⟩
  have hx := hla x (by simp)
  have hy := hlb y (by simp)
  have hA' : T.cells 3 = tapeOf S7 (PA ++ body x ++
      (((if a' = [] then runend else rend) :: encRun a') ++ RA)) := by
    rw [hA, encRun_cons_body]; simp
  have hB' : T.cells 4 = tapeOf S7 (PB ++ body y ++
      (((if b' = [] then runend else rend) :: encRun b') ++ RB)) := by
    rw [hB, encRun_cons_body]; simp
  obtain ⟨d, hd, hdA, hdB⟩ := mstep_dispatch T x y (by omega) PA _ PB _ hA' hhA hB' hhB hPA hPB
  have hflag : flagc T.read = true := by simp [flagc, Tapes.read, hF, hhF, tapeOf]
  have lbx := length_body x
  have lby := length_body y
  have lex := length_encRun_cons x a'
  have ley := length_encRun_cons y b'
  by_cases hle : le7 x y = true
  · have hm : List.merge (x :: a') (y :: b') le7 = x :: List.merge a' (y :: b') le7 :=
      List.cons_merge_cons_pos le7 _ _ hle
    by_cases ha' : a' = []
    · subst ha'
      have ht := take_last_runs 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) T x (y :: b') (by simp) PA RA PB RB Q [zero] (by simp) (by simp) hA hhA hB hhB
        hC hhC hF hhF
      have hr := hdA hle _ _ ht
      set T' : Tapes Sym7 6 := _ with hT'
      refine ⟨_, ?_, T', loop_iter hflag (by omega) hr (loop_stop ?_), ?_⟩
      · have : (encRun [x]).length = (body x).length + 1 := by rw [encRun_single]; simp
        omega
      · simp [hT', flagc, Tapes.read, tapeOf, hhF]
      · simp only [MergeOut, hT', hm, List.nil_merge]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [encRun_cons_ne x (y :: b') (by simp)]
        · simp [encRun_cons_ne x (y :: b') (by simp)]; omega
        · simp [encRun, length_encR]
        · simp
        · simp
        · simp [hhF]
        · intro l h2 h5; simp [h2, h5]
        · intro l hl
          have h2 : l ≠ 2 := by intro e; subst e; simp at hl
          have h3 : l ≠ 3 := by intro e; subst e; simp at hl
          have h4 : l ≠ 4 := by intro e; subst e; simp at hl
          simp [h2, h3, h4]
    · have ht := take_cont_runs 3 4 (by decide) (by decide) T x a' ha' PA RA Q hA hhA hC hhC
      set T1 : Tapes Sym7 6 := ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encR rend x)),
        Function.update (Function.update T.head 3 (PA.length + 1 + (encR rend x).length)) 2
          (Q.length + 1 + (encR rend x).length)⟩ with hT1
      have hc3 : T1.cells 3 = tapeOf S7 ((PA ++ encR rend x) ++ encRun a' ++ RA) := by
        simp only [hT1, Function.update_of_ne (show (3 : Fin 6) ≠ 2 by decide), hA,
          encRun_cons_ne x a' ha']
        simp
      obtain ⟨t', ht', T', hr', hout⟩ := ih (a'.length + (y :: b').length) (by simp only [List.length_cons] at hn ⊢; omega)
        a' (y :: b') rfl ha' (by simp) (fun r hr => hla r (by simp [hr])) hlb T1
        (PA ++ encR rend x) RA PB RB (Q ++ encR rend x) hc3
        (by simp only [hT1, Function.update_of_ne (show (3:Fin 6) ≠ 2 by decide),
              Function.update_self, List.length_append]; omega)
        (by rw [hc3, show (PA ++ encR rend x).length = (PA ++ body x).length + 1 by
                rw [encR_eq]; simp; omega,
              show PA ++ encR rend x ++ encRun a' ++ RA = (PA ++ body x) ++ rend :: (encRun a' ++ RA) by
                rw [encR_eq]; simp, tapeOf_at_len]; rfl)
        (by simp [hT1, hB]) (by simp [hT1, hhB]) (by simp [hT1, hPB])
        (by simp [hT1]) (by simp [hT1]; omega) (by simp [hT1, hF]) (by simp [hT1, hhF])
      have hr := hdA hle _ _ ht
      refine ⟨_, ?_, T', loop_iter hflag (by rw [length_encR]; omega) hr hr', ?_⟩
      · have := length_encR rend x
        rw [length_encRun_cons x a'] at ⊢
        nlinarith
      · obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hout
        have hne := merge_ne_nil a' (y :: b') (Or.inr (by simp))
        refine ⟨?_, ?_, ?_, ?_, o5, o6, ?_, ?_⟩
        · rw [o1, hm, encRun_cons_ne _ _ hne]; simp
        · rw [o2, hm, encRun_cons_ne _ _ hne]; simp; omega
        · rw [o3, lex]; simp [length_encR]; omega
        · rw [o4]
        · intro l h2 h5; rw [o7 l h2 h5]; simp [hT1, h2]
        · intro l hl
          have h2 : l ≠ 2 := by intro e; subst e; simp at hl
          have h3 : l ≠ 3 := by intro e; subst e; simp at hl
          rw [o8 l hl]; simp [hT1, h2, h3]
  · have hle' : le7 x y = false := by simpa using hle
    have hm : List.merge (x :: a') (y :: b') le7 = y :: List.merge (x :: a') b' le7 :=
      List.cons_merge_cons_neg le7 _ _ (by simp [hle'])
    by_cases hb' : b' = []
    · subst hb'
      have ht := take_last_runs 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) T y (x :: a') (by simp) PB RB PA RA Q [zero] (by simp) (by simp) hB hhB hA hhA
        hC hhC hF hhF
      have hr := hdB hle' _ _ ht
      set T' : Tapes Sym7 6 := _ with hT'
      refine ⟨_, ?_, T', loop_iter hflag (by omega) hr (loop_stop ?_), ?_⟩
      · have : (encRun [y]).length = (body y).length + 1 := by rw [encRun_single]; simp
        omega
      · simp [hT', flagc, Tapes.read, tapeOf, hhF]
      · simp only [MergeOut, hT', hm, List.merge_right]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [encRun_cons_ne y (x :: a') (by simp)]
        · simp [encRun_cons_ne y (x :: a') (by simp)]; omega
        · simp
        · simp [encRun, length_encR]
        · simp
        · simp [hhF]
        · intro l h2 h5; simp [h2, h5]
        · intro l hl
          have h2 : l ≠ 2 := by intro e; subst e; simp at hl
          have h3 : l ≠ 3 := by intro e; subst e; simp at hl
          have h4 : l ≠ 4 := by intro e; subst e; simp at hl
          simp [h2, h3, h4]
    · have ht := take_cont_runs 4 3 (by decide) (by decide) T y b' hb' PB RB Q hB hhB hC hhC
      set T1 : Tapes Sym7 6 := ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encR rend y)),
        Function.update (Function.update T.head 4 (PB.length + 1 + (encR rend y).length)) 2
          (Q.length + 1 + (encR rend y).length)⟩ with hT1
      have hc4 : T1.cells 4 = tapeOf S7 ((PB ++ encR rend y) ++ encRun b' ++ RB) := by
        simp only [hT1, Function.update_of_ne (show (4 : Fin 6) ≠ 2 by decide), hB,
          encRun_cons_ne y b' hb']
        simp
      obtain ⟨t', ht', T', hr', hout⟩ := ih ((x :: a').length + b'.length)
        (by simp only [List.length_cons] at hn ⊢; omega)
        (x :: a') b' rfl (by simp) hb' hla (fun r hr => hlb r (by simp [hr])) T1
        PA RA (PB ++ encR rend y) RB (Q ++ encR rend y)
        (by simp [hT1, hA]) (by simp [hT1, hhA]) (by simp [hT1, hPA]) hc4
        (by simp only [hT1, Function.update_of_ne (show (4:Fin 6) ≠ 2 by decide),
              Function.update_self, List.length_append]; omega)
        (by rw [hc4, show (PB ++ encR rend y).length = (PB ++ body y).length + 1 by
                rw [encR_eq]; simp; omega,
              show PB ++ encR rend y ++ encRun b' ++ RB = (PB ++ body y) ++ rend :: (encRun b' ++ RB) by
                rw [encR_eq]; simp, tapeOf_at_len]; rfl)
        (by simp [hT1]) (by simp [hT1]; omega) (by simp [hT1, hF]) (by simp [hT1, hhF])
      have hr := hdB hle' _ _ ht
      refine ⟨_, ?_, T', loop_iter hflag (by rw [length_encR]; omega) hr hr', ?_⟩
      · have := length_encR rend y
        rw [length_encRun_cons y b'] at ⊢
        nlinarith
      · obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hout
        have hne := merge_ne_nil (x :: a') b' (Or.inl (by simp))
        refine ⟨?_, ?_, ?_, ?_, o5, o6, ?_, ?_⟩
        · rw [o1, hm, encRun_cons_ne _ _ hne]; simp
        · rw [o2, hm, encRun_cons_ne _ _ hne]; simp; omega
        · rw [o3]
        · rw [o4, ley]; simp [length_encR]; omega
        · intro l h2 h5; rw [o7 l h2 h5]; simp [hT1, h2]
        · intro l hl
          have h2 : l ≠ 2 := by intro e; subst e; simp at hl
          have h4 : l ≠ 4 := by intro e; subst e; simp at hl
          rw [o8 l hl]; simp [hT1, h2, h4]


/-! ## Merging all pairs of runs -/

def zipMerge : List (List Rec) → List (List Rec) → List (List Rec)
  | a :: as, b :: bs => List.merge a b le7 :: zipMerge as bs
  | as, [] => as
  | [], bs => bs

theorem encRuns_cons_m (a : List Rec) (As : List (List Rec)) :
    encRuns (a :: As) = encRun a ++ encRuns As := by simp [encRuns]

@[simp] theorem encRuns_nil_m : encRuns [] = [] := rfl

theorem encRun_head (a : List Rec) (ha : a ≠ []) (R : List Sym7) :
    ((encRun a ++ R).getD 0 blank ≠ blank) ∧ (encRun a ++ R).getD 0 blank ≠ st := by
  obtain ⟨x, a', rfl⟩ : ∃ x a', a = x :: a' := by
    rcases a with _ | ⟨x, a'⟩
    · exact absurd rfl ha
    · exact ⟨x, a', rfl⟩
  rw [encRun_cons_body]
  rcases x with ⟨k, p⟩
  rcases k with _ | ⟨c, k⟩
  · simp [body, enc]
  · cases c <;> simp [body, enc, bs]

theorem tapeOf_first (P W : List Sym7) : tapeOf S7 (P ++ W) (P.length + 1) = W.getD 0 blank := by
  rw [tapeOf_succ, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem encRun_last_runend (a : List Rec) (ha : a ≠ []) (P R : List Sym7) :
    isBody (tapeOf S7 (P ++ encRun a ++ R) (P ++ encRun a).length) = false := by
  obtain ⟨B, hB, -⟩ := encRun_split a ha
  rw [hB, show (P ++ (B ++ [runend])).length = (P ++ B).length + 1 by simp; omega,
    show P ++ (B ++ [runend]) ++ R = (P ++ B) ++ runend :: R by simp, tapeOf_at_len]
  rfl

theorem length_encRuns_cons (a : List Rec) (As : List (List Rec)) :
    (encRuns (a :: As)).length = (encRun a).length + (encRuns As).length := by
  rw [encRuns_cons_m]; simp

set_option maxHeartbeats 1000000 in
theorem mergeAll_runs (ℓ : ℕ) : ∀ (As Bs : List (List Rec)), Bs.length ≤ As.length →
    As.length ≤ Bs.length + 1 → (∀ a ∈ As, a ≠ []) → (∀ b ∈ Bs, b ≠ []) →
    (∀ a ∈ As, ∀ r ∈ a, r.1.length = ℓ) → (∀ b ∈ Bs, ∀ r ∈ b, r.1.length = ℓ) →
    ∀ (T : Tapes Sym7 6) (PA PB Q F : List Sym7),
    T.cells 3 = tapeOf S7 (PA ++ encRuns As) → T.head 3 = PA.length + 1 →
    isBody (T.cells 3 PA.length) = false →
    T.cells 4 = tapeOf S7 (PB ++ encRuns Bs) → T.head 4 = PB.length + 1 →
    isBody (T.cells 4 PB.length) = false →
    T.cells 2 = tapeOf S7 Q → T.head 2 = Q.length + 1 →
    T.cells 5 = tapeOf S7 F → F.length ≤ 1 → (∀ s ∈ F, s ≠ st) → T.head 5 = 1 →
    ∃ t ≤ 6 * ((encRuns As).length + (encRuns Bs).length), ∃ T',
      Runs st mergeAll T t T' ∧
      T'.cells 2 = tapeOf S7 (Q ++ encRuns (zipMerge As Bs)) ∧
      T'.head 2 = Q.length + 1 + (encRuns (zipMerge As Bs)).length ∧
      T'.head 3 = PA.length + 1 + (encRuns As).length ∧
      T'.head 4 = PB.length + 1 + (encRuns Bs).length ∧
      (∃ F', T'.cells 5 = tapeOf S7 F' ∧ F'.length ≤ 1 ∧ ∀ s ∈ F', s ≠ st) ∧ T'.head 5 = 1 ∧
      (∀ l : Fin 6, l ≠ 2 → l ≠ 5 → T'.cells l = T.cells l) ∧
      (∀ l : Fin 6, l.val < 2 → T'.head l = T.head l) := by
  intro As
  induction As with
  | nil =>
    intro Bs h1 _ _ _ _ _ T PA PB Q F hA hhA _ hB hhB _ hC hhC hF hF1 hF2 hhF
    obtain rfl : Bs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h1; omega)
    refine ⟨0, by omega, T, loop_stop ?_, ?_⟩
    · simp [Tapes.read, hA, hhA]; exact tapeOf_end7 PA
    · exact ⟨by simp [hC, zipMerge], by simp [hhC, zipMerge], by simp [hhA], by simp [hhB],
        ⟨F, hF, hF1, hF2⟩, hhF, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | cons a As ih =>
    intro Bs h1 h2 hAne hBne hlA hlB T PA PB Q F hA hhA hPA hB hhB hPB hC hhC hF hF1 hF2 hhF
    have ha : a ≠ [] := hAne a (by simp)
    have hflagA : decide (T.read 3 ≠ blank) = true := by
      simp only [Tapes.read, hA, hhA, encRuns_cons_m, List.append_assoc, tapeOf_first]
      simpa using (encRun_head a ha _).1
    rcases Bs with _ | ⟨b, Bs⟩
    · -- no partner run: copy `a`
      obtain rfl : As = [] := List.eq_nil_of_length_eq_zero
        (by simp only [List.length_cons, List.length_nil] at h2; omega)
      have hcopy := copyRun_runs 3 2 (by decide) (by decide) T PA [] Q a ha
        (by rw [hA]; simp [encRuns]) hhA hC hhC
      have hpos : 0 < (encRun a).length := by
        obtain ⟨B, hB', -⟩ := encRun_split a ha; rw [hB']; simp
      have hite := ite_runs_true (c := fun a => decide (a 4 = blank))
        (P₂ := seq (setFlag zero) (loop flagc mstep))
        (by simp [Tapes.read, hB, hhB]; exact tapeOf_end7 PB) hcopy
      set T' : Tapes Sym7 6 := _ with hT'
      refine ⟨_, ?_, T', loop_iter hflagA hpos hite (loop_stop ?_), ?_⟩
      · simp [encRuns]; omega
      · have e : T.cells 3 (PA.length + 1 + (encRun a).length) = blank := by
          rw [hA, show PA ++ encRuns [a] = PA ++ encRun a by simp [encRuns],
            show PA.length + 1 + (encRun a).length = (PA ++ encRun a).length + 1 by simp; omega]
          exact tapeOf_end7 _
        simp [hT', Tapes.read, e]
      · simp only [hT', zipMerge, encRuns, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil]
        refine ⟨by simp, by simp, by simp, by simp [hhB], ⟨F, by simp [hF], hF1, hF2⟩,
          by simp [hhF], fun l h2 _ => by simp [h2], fun l hl => ?_⟩
        have h2 : l ≠ 2 := by intro e; subst e; simp at hl
        have h3 : l ≠ 3 := by intro e; subst e; simp at hl
        simp [h2, h3]
    · have hb : b ≠ [] := hBne b (by simp)
      have hlen := mergeLoop_runs ℓ _ a b rfl ha hb (hlA a (by simp)) (hlB b (by simp))
      have hset := setFlag_runs zero (by decide) T F hF1 hF2 hF hhF
      set T1 : Tapes Sym7 6 := ⟨Function.update T.cells 5 (tapeOf S7 [zero]), T.head⟩ with hT1
      obtain ⟨t1, ht1, T2, hr2, o1, o2, o3, o4, o5, o6, o7, o8⟩ := hlen T1 PA (encRuns As) PB
        (encRuns Bs) Q (by simp [hT1, hA, encRuns_cons_m]) (by simp [hT1, hhA]) (by simp [hT1, hPA])
        (by simp [hT1, hB, encRuns_cons_m]) (by simp [hT1, hhB]) (by simp [hT1, hPB])
        (by simp [hT1, hC]) (by simp [hT1, hhC]) (by simp [hT1]) (by simp [hT1, hhF])
      have hite := ite_runs_false (c := fun a => decide (a 4 = blank)) (P₁ := copyRun 3 2)
        (by
          simp only [Tapes.read, hB, hhB, encRuns_cons_m, List.append_assoc, tapeOf_first]
          simpa using (encRun_head b hb _).1)
        (seq_runs hset hr2)
      have hc3 : T2.cells 3 = tapeOf S7 ((PA ++ encRun a) ++ encRuns As) := by
        rw [o7 3 (by decide) (by decide)]; simp [hT1, hA, encRuns_cons_m]
      have hc4 : T2.cells 4 = tapeOf S7 ((PB ++ encRun b) ++ encRuns Bs) := by
        rw [o7 4 (by decide) (by decide)]; simp [hT1, hB, encRuns_cons_m]
      obtain ⟨t3, ht3, T3, hr3, p1, p2, p3, p4, p5, p6, p7, p8⟩ := ih Bs (by simp at h1 h2; omega)
        (by simp at h1 h2; omega) (fun x hx => hAne x (by simp [hx]))
        (fun x hx => hBne x (by simp [hx])) (fun x hx => hlA x (by simp [hx]))
        (fun x hx => hlB x (by simp [hx])) T2 (PA ++ encRun a) (PB ++ encRun b)
        (Q ++ encRun (List.merge a b le7)) [one] hc3 (by rw [o3]; simp; omega)
        (by rw [hc3]; exact encRun_last_runend a ha PA _) hc4 (by rw [o4]; simp; omega)
        (by rw [hc4]; exact encRun_last_runend b hb PB _) o1 (by rw [o2]; simp; omega) o5
        (by simp) (by simp) o6
      have hpos : 0 < 1 + t1 := by omega
      refine ⟨_, ?_, T3, loop_iter hflagA hpos hite hr3, ?_⟩
      · rw [length_encRuns_cons, length_encRuns_cons]
        have : 0 < (encRun a).length := by
          obtain ⟨B, hB', -⟩ := encRun_split a ha; rw [hB']; simp
        omega
      · refine ⟨?_, ?_, ?_, ?_, p5, p6, ?_, ?_⟩
        · rw [p1]; simp [zipMerge, encRuns_cons_m]
        · rw [p2]; simp [zipMerge, encRuns_cons_m]; omega
        · rw [p3, length_encRuns_cons]; simp; omega
        · rw [p4, length_encRuns_cons]; simp; omega
        · intro l h2 h5; rw [p7 l h2 h5, o7 l h2 h5]; simp [hT1, h5]
        · intro l hl; rw [p8 l hl, o8 l hl]

end IntMul.Mach.MS

-- ===== MSPhases =====


namespace IntMul.Mach.MS

open IntMul IntMul.Mach Sym7

set_option linter.unusedSectionVars false

/-! ## Letters -/

/-- The tape symbol of an input letter. -/
def letter : Option Bool → Sym7
  | none => sep
  | some b => bs b


/-! ## List identities -/

/-- The input transduction as a pure function. -/
def convL : Bool → List (Option Bool) → List Sym7
  | _, [] => []
  | s, some b :: w => bs b :: convL s w
  | s, none :: w => (if s then runend else sep) :: convL (!s) w

/-- The input word of a list of records. -/
def enc' (rs : List Rec) : List (Option Bool) :=
  joinSep (rs.flatMap fun r => [bits r.1, bits r.2])

theorem convL_length (s : Bool) (w : List (Option Bool)) : (convL s w).length = w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons x w ih => rcases x with _ | b <;> simp [convL, ih]

theorem convL_bits (s : Bool) (l : List Bool) (w : List (Option Bool)) :
    convL s (bits l ++ w) = enc l ++ convL s w := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [bits, List.map_cons, List.cons_append, convL] at ih ⊢; rw [ih]; rfl

theorem convL_bits_nil (s : Bool) (l : List Bool) : convL s (bits l) = enc l := by
  simpa [convL] using convL_bits s l []

theorem enc'_single (r : Rec) : enc' [r] = bits r.1 ++ none :: bits r.2 := by
  simp [enc', joinSep, List.intercalate_cons_cons]

theorem enc'_cons_cons (r r' : Rec) (rs : List Rec) :
    enc' (r :: r' :: rs) = bits r.1 ++ none :: bits r.2 ++ none :: enc' (r' :: rs) := by
  simp [enc', joinSep, List.intercalate_cons_cons]

theorem enc'_eq_nil (recs : List Rec) : enc' recs = [] ↔ recs = [] := by
  constructor
  · intro h
    rcases recs with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · rfl
    · rw [enc'_single] at h; simp at h
    · rw [enc'_cons_cons] at h; simp at h
  · rintro rfl; rfl

theorem convL_enc' (r : Rec) (rs : List Rec) :
    convL false (enc' (r :: rs)) ++ [runend] = encRuns ((r :: rs).map fun r => [r]) := by
  induction rs generalizing r with
  | nil =>
    rw [enc'_single, convL_bits]
    simp [convL, convL_bits, convL_bits_nil, encRuns, encRun, encR]
  | cons r' rs ih =>
    rw [enc'_cons_cons]
    rw [List.append_assoc, convL_bits]
    simp only [convL, List.cons_append, List.nil_append, convL_bits, if_false, Bool.not_false,
      if_true, Bool.not_true]
    have := ih r'
    simp only [List.map_cons, encRuns, List.flatten_cons] at this ⊢
    rw [← this]
    simp [encRun, encR]

theorem convL_enc'_map (recs : List Rec) (h : recs ≠ []) :
    convL false (enc' recs) ++ [runend] = encRuns (recs.map fun r => [r]) := by
  rcases recs with _ | ⟨r, rs⟩
  · exact absurd rfl h
  · exact convL_enc' r rs

theorem outG_bs : outG ∘ bs = letter ∘ some := by
  funext b; cases b <;> rfl

theorem output_list (R : List Rec) (hR : R ≠ []) :
    ((encRun R).dropLast).map outG = (enc' R).map letter := by
  induction R with
  | nil => exact absurd rfl hR
  | cons r rs ih =>
    rcases rs with _ | ⟨r', rs⟩
    · rw [enc'_single]
      simp [encRun, encR, enc, bits, letter, outG]
      rw [← List.cons_append, List.dropLast_concat, outG_bs]
    · rw [encRun_cons_cons, enc'_cons_cons, List.dropLast_append_of_ne_nil (by
        obtain ⟨B, hB, -⟩ := encRun_split (r' :: rs) (by simp); rw [hB]; simp)]
      rw [List.map_append, ih (by simp)]
      simp [encR, enc, bits, letter, outG, outG_bs]

/-! ## Distribution -/

def odds {α : Type*} : List α → List α
  | a :: _ :: rest => a :: odds rest
  | [a] => [a]
  | [] => []

def evens {α : Type*} : List α → List α
  | _ :: b :: rest => b :: evens rest
  | _ => []

theorem encRuns_nil : encRuns [] = [] := rfl

theorem encRuns_cons (R : List Rec) (Rs : List (List Rec)) :
    encRuns (R :: Rs) = encRun R ++ encRuns Rs := by simp [encRuns]

theorem encRun_ne_blank (rs : List Rec) : ∀ x ∈ encRun rs, x ≠ blank := by
  rcases rs with _ | ⟨r, rs⟩
  · simp [encRun]
  · obtain ⟨B, hB, hB'⟩ := encRun_split (r :: rs) (by simp)
    rw [hB]; intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h | h
    · have := hB' x h; intro e; subst e; simp [isRunBody] at this
    · subst h; decide

theorem encRun_ne_nil (rs : List Rec) (h : rs ≠ []) : encRun rs ≠ [] := by
  obtain ⟨B, hB, -⟩ := encRun_split rs h; rw [hB]; simp

theorem tapeOf_first_ne_blank (P L R : List Sym7) (hL : L ≠ []) (hb : ∀ x ∈ L, x ≠ blank) :
    tapeOf S7 (P ++ L ++ R) (P.length + 1) ≠ blank := by
  rcases L with _ | ⟨x, L⟩
  · exact absurd rfl hL
  · rw [show P ++ x :: L ++ R = P ++ x :: (L ++ R) by simp, tapeOf_at7]
    exact hb x (by simp)

theorem dist_runs : ∀ (Rs : List (List Rec)) (_ : ∀ r ∈ Rs, r ≠ []) (T : Tapes Sym7 6)
    (P QA QB : List Sym7),
    T.cells 2 = tapeOf S7 (P ++ encRuns Rs) → T.head 2 = P.length + 1 →
    T.cells 3 = tapeOf S7 QA → T.head 3 = QA.length + 1 →
    T.cells 4 = tapeOf S7 QB → T.head 4 = QB.length + 1 →
    Runs st dist T (encRuns Rs).length
      ⟨Function.update (Function.update T.cells 3 (tapeOf S7 (QA ++ encRuns (odds Rs)))) 4
          (tapeOf S7 (QB ++ encRuns (evens Rs))),
        Function.update (Function.update (Function.update T.head 2
          (P.length + 1 + (encRuns Rs).length)) 3 (QA.length + 1 + (encRuns (odds Rs)).length)) 4
          (QB.length + 1 + (encRuns (evens Rs)).length)⟩
  | [], _, T, P, QA, QB, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have h := loop_stop (st := st) (B := (seq (copyRun 2 3)
      (ite (fun a => decide (a 2 = blank)) skip (copyRun 2 4)))) (T := T)
      (c := fun a => decide (a 2 ≠ blank)) (by
        simp only [Tapes.read, hc2, hh2, encRuns_nil, List.append_nil, tapeOf_end7]; decide)
    refine h.of_eq ?_ rfl
    simp only [odds, evens, encRuns_nil, List.append_nil, List.length_nil, Nat.add_zero]
    rw [← hc3, ← hc4, ← hh2, ← hh3, ← hh4]
    simp
  | [R], hRs, T, P, QA, QB, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have hR : R ≠ [] := hRs R (by simp)
    have h1 := copyRun_runs 2 3 (by decide) (by decide) T P [] QA R hR
      (by rw [hc2, encRuns_cons, encRuns_nil]; simp) hh2 hc3 hh3
    have hb : tapeOf S7 (P ++ encRun R) (P.length + 1 + (encRun R).length) = blank := by
      rw [show P ++ encRun R = P ++ encRun R ++ [] by simp, tapeOf_after7]; rfl
    have h := loop_iter (c := fun a => decide (a 2 ≠ blank)) ?_ ?_
      (seq_runs h1 (ite_runs_true (c := fun a => decide (a 2 = blank)) (P₂ := copyRun 2 4) ?_ (skip_runs _)))
      (loop_stop ?_)
    rotate_left
    · simp only [Tapes.read, hc2, hh2, encRuns_cons, encRuns_nil]
      have := tapeOf_first_ne_blank P (encRun R) [] (encRun_ne_nil R hR) (encRun_ne_blank R)
      simpa using this
    · have := encRun_ne_nil R hR; simp only [Nat.add_zero]; exact List.length_pos_iff.mpr this
    · simp [Tapes.read, hc2, encRuns_cons, encRuns_nil, hb]
    · simp [Tapes.read, hc2, encRuns_cons, encRuns_nil, hb]
    refine h.of_eq ?_ (by simp [encRuns_cons, encRuns_nil])
    simp only [odds, evens, encRuns_cons, encRuns_nil, List.append_nil, List.length_nil,
      Nat.add_zero]
    rw [← hc4, ← hh4]
    congr 1
    · funext l; fin_cases l <;> simp
    · funext l; fin_cases l <;> simp
  | R1 :: R2 :: rest, hRs, T, P, QA, QB, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have hR1 : R1 ≠ [] := hRs R1 (by simp)
    have hR2 : R2 ≠ [] := hRs R2 (by simp)
    have hrest : ∀ r ∈ rest, r ≠ [] := fun r hr => hRs r (by simp [hr])
    have hc2' : T.cells 2 = tapeOf S7 (P ++ encRun R1 ++ encRun R2 ++ encRuns rest) := by
      rw [hc2, encRuns_cons, encRuns_cons]; simp
    have h1 := copyRun_runs 2 3 (by decide) (by decide) T P (encRun R2 ++ encRuns rest) QA R1 hR1
      (by rw [hc2']; simp) hh2 hc3 hh3
    have h2 := copyRun_runs 2 4 (by decide) (by decide)
      ⟨Function.update T.cells 3 (tapeOf S7 (QA ++ encRun R1)),
        Function.update (Function.update T.head 2 (P.length + 1 + (encRun R1).length)) 3
          (QA.length + 1 + (encRun R1).length)⟩ (P ++ encRun R1) (encRuns rest) QB R2 hR2
      (by simp [hc2']) (by simp; omega) (by simp [hc4]) (by simp [hh4])
    have h := loop_iter (c := fun a => decide (a 2 ≠ blank)) ?r1 ?pos
      (seq_runs h1 (ite_runs_false (c := fun a => decide (a 2 = blank)) (P₁ := skip) ?r2 h2))
      (dist_runs rest hrest _ (P ++ encRun R1 ++ encRun R2) (QA ++ encRun R1)
        (QB ++ encRun R2) ?a1 ?a2 ?a3 ?a4 ?a5 ?a6)
    case a1 => simp [hc2']
    case a2 => simp; omega
    case a3 => simp
    case a4 => simp; omega
    case a5 => simp
    case a6 => simp; omega
    case r1 =>
      simp only [Tapes.read, hc2', hh2]
      have := tapeOf_first_ne_blank P (encRun R1) (encRun R2 ++ encRuns rest) (encRun_ne_nil R1 hR1)
        (encRun_ne_blank R1)
      simpa [List.append_assoc] using this
    case pos => have := List.length_pos_iff.mpr (encRun_ne_nil R1 hR1); omega
    case r2 =>
      have := tapeOf_first_ne_blank (P ++ encRun R1) (encRun R2) (encRuns rest)
        (encRun_ne_nil R2 hR2) (encRun_ne_blank R2)
      simp only [Tapes.read]
      simpa [hc2', List.append_assoc, Nat.add_right_comm] using this
    refine h.of_eq ?_ (by simp [encRuns_cons]; omega)
    simp only [odds, evens, encRuns_cons, List.length_append]
    congr 1
    · funext l; fin_cases l <;> simp
    · funext l; fin_cases l <;> simp <;> omega

/-! ## Initialisation -/

theorem mvs_runs {P : Prog Sym7 6} {T T' : Tapes Sym7 6} {t : ℕ}
    (h : Runs st P ⟨T.cells, fun i => if i = 1 then T.head 1 else T.head i + 1⟩ t T') :
    Runs st (seq (mv 5 Move.right) <| seq (mv 0 Move.right) <|
      seq (mv 2 Move.right) <| seq (mv 3 Move.right) <| seq (mv 4 Move.right) P) T (5 + t) T' := by
  rw [show 5 + t = 1 + (1 + (1 + (1 + (1 + t)))) by omega]
  refine seq_runs (mv_runs st 5 Move.right T nofun) <| seq_runs (mv_runs st 0 Move.right _ nofun) <|
    seq_runs (mv_runs st 2 Move.right _ nofun) <| seq_runs (mv_runs st 3 Move.right _ nofun) <|
    seq_runs (mv_runs st 4 Move.right _ nofun) ?_
  convert h using 2
  funext i; fin_cases i <;> simp [moveHead]


theorem sst_shift {σ : Type} (f : σ → (Fin 6 → Sym7) → σ × Sym7) (r : ℕ → Fin 6 → Sym7)
    (s : σ) (m : ℕ) : sst f r s (m + 1) = sst f (fun n => r (n + 1)) (f s (r 0)).1 m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sst] at ih ⊢; rw [ih]

theorem sout_shift {σ : Type} (f : σ → (Fin 6 → Sym7) → σ × Sym7) (r : ℕ → Fin 6 → Sym7)
    (s : σ) (m : ℕ) : sout f r s (m + 1) = sout f (fun n => r (n + 1)) (f s (r 0)).1 m := by
  simp only [sout]; rw [sst_shift]

theorem ofFn_sout_convF (w : List (Option Bool)) : ∀ (s : Bool) (r : ℕ → Fin 6 → Sym7),
    (∀ m (hm : m < w.length), r m 0 = letter w[m]) →
    List.ofFn (fun m : Fin w.length => sout convF r s m) = convL s w := by
  induction w with
  | nil => intro s r _; rfl
  | cons x w ih =>
    intro s r hr
    rw [List.ofFn_succ]
    have h0 := hr 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    have htail : ∀ m (hm : m < w.length), (fun n => r (n + 1)) m 0 = letter w[m] := by
      intro m hm; have := hr (m + 1) (by simp; omega); simpa using this
    have e : ∀ i : Fin w.length, sout convF r s (i.succ : ℕ) =
        sout convF (fun n => r (n + 1)) (convF s (r 0)).1 i := by
      intro i; rw [Fin.val_succ, sout_shift]
    simp only [e]
    rw [ih _ _ htail]
    rcases x with _ | b
    · simp [sout, sst, convF, h0, letter, convL]
    · have hb : bs b ≠ sep := by cases b <;> decide
      simp [sout, sst, convF, h0, letter, convL, hb]

theorem letter_ne_blank (x : Option Bool) : letter x ≠ blank := by
  rcases x with _ | b
  · decide
  · cases b <;> decide

theorem letter_ne_st (x : Option Bool) : letter x ≠ st := by
  rcases x with _ | b
  · decide
  · cases b <;> decide

theorem conv_runs (w : List (Option Bool)) (T : Tapes Sym7 6)
    (hc0 : T.cells 0 = tapeOf S7 (w.map letter)) (hh0 : T.head 0 = 1)
    (hc2 : T.cells 2 = tapeOf S7 []) (hh2 : T.head 2 = 1) :
    Runs st conv T w.length
      ⟨Function.update T.cells 2 (tapeOf S7 (convL false w)),
        Function.update (Function.update T.head 0 (1 + w.length)) 2 (1 + w.length)⟩ := by
  set d : Fin 6 → Move := fun l => if l = 0 ∨ l = 2 then Move.right else Move.stay with hd
  have hd0 : d 0 = Move.right := by simp [hd]
  have hd2 : d 2 = Move.right := by simp [hd]
  have hr0 : ∀ m, rd T d m 0 = tapeOf S7 (w.map letter) (1 + m) := by
    intro m; simp only [rd, hd0, offs, hc0, hh0]
  have hr0' : ∀ m (hm : m < w.length), rd T d m 0 = letter w[m] := by
    intro m hm
    rw [hr0, tapeOf_one_add, List.getD_eq_getElem _ _ (by simpa using hm)]; simp
  have hr2 : ∀ m, rd T d m 2 = blank := by
    intro m; simp only [rd, hd2, offs, hc2, hh2, tapeOf_one_add]; rfl
  have h := sweep_runs st d 2 (fun a => decide (a 0 ≠ blank)) false convF T w.length
    (by decide) (by simp [hd2]) (by simp [hd2])
    (fun i p hi _ => by simp only [hd] at hi; split_ifs at hi)
    (fun m hm => by simp [hr0' m hm, letter_ne_blank])
    (by simp only [hr0, tapeOf_one_add]; rw [List.getD_eq_default _ _ (by simp)]; decide)
    (fun m _ => by rw [hr2]; decide)
    (fun m hm => by
      have := letter_ne_st w[m]; rw [← hr0' m hm] at this
      simp only [sout, convF]; split_ifs <;> simp_all)
  refine Runs.of_eq h ?_ rfl
  congr 1
  · congr 1
    funext p
    rw [hd2, dcells_right, hh2, hc2]
    have e1 : tapeOf S7 [] = tapeOf S7 ([] ++ List.replicate w.length blank ++ []) := by
      have := tapeOf_append_blanks S7 [] w.length
      simp only [List.nil_append, List.append_nil] at this ⊢; exact this.symm
    rw [e1]
    have := congrFun (tapeOf_write_right S7 [] (List.replicate w.length blank) []
      (sout convF (rd T d) false)) p
    simp only [List.length_nil, Nat.zero_add, List.length_replicate] at this
    rw [this]
    congr 2
    simp only [List.nil_append, List.append_nil]
    rw [← ofFn_sout_convF w false (rd T d) hr0']
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp
  · funext l; fin_cases l <;> simp [hd, offs, Function.update_apply, hh0, hh2] <;> omega

/-- The word on `C` after initialisation. -/
def initC (w : List (Option Bool)) : List Sym7 :=
  if w = [] then [] else convL false w ++ [runend]

theorem init_runs (w : List (Option Bool)) :
    Runs st init
      ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else tapeOf S7 [], fun _ => 0⟩
      (5 + if w = [] then 0 else w.length + 1)
      ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else if i = 2 then tapeOf S7 (initC w)
          else tapeOf S7 [],
        fun i => if i = 0 then w.length + 1 else if i = 1 then 0 else if i = 2 then
          (initC w).length + 1 else 1⟩ := by
  apply mvs_runs
  by_cases hw : w = []
  · subst hw
    simp only [if_true]
    refine ite_runs_true ?_ (skip_runs _) |>.of_eq ?_ rfl
    · simp [Tapes.read]; rfl
    · simp only [initC, if_true, List.length_nil, List.map_nil]
      congr 1
      · funext i; split_ifs <;> simp_all
      · funext i; fin_cases i <;> simp
  · simp only [if_neg hw]
    have hc := conv_runs w
      ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else tapeOf S7 [],
        fun i => if i = 1 then 0 else 0 + 1⟩ (by simp) (by simp) (by simp) (by simp)
    refine ite_runs_false ?r (seq_runs hc (wsym_runs 2 (by decide) runend (by decide) _
      (convL false w) ?c2 ?h2)) |>.of_eq ?eq ?tm
    case c2 => simp
    case h2 => simp [convL_length]; omega
    case tm => simp [hw]
    case r =>
      rcases w with _ | ⟨x, w⟩
      · exact absurd rfl hw
      · simp only [Tapes.read]
        simp [tapeOf_succ, letter_ne_blank]
    case eq =>
      simp only [initC, if_neg hw]
      congr 1
      · funext i; fin_cases i <;> simp
      · funext i; fin_cases i <;> simp [convL_length] <;> omega

theorem initC_enc' (recs : List Rec) : initC (enc' recs) = encRuns (recs.map fun r => [r]) := by
  by_cases h : recs = []
  · subst h; rfl
  · rw [initC, if_neg (by rwa [enc'_eq_nil]), convL_enc'_map recs h]

/-! ## Output -/

/-- `copy_runs` with the image condition only on the copied symbols. -/
theorem copy_runs' (i j : Fin 6) (hij : i ≠ j) (hj : j.val ≠ 0) (c : Sym7 → Bool)
    (g : Sym7 → Sym7) :
    ∀ (L P : List Sym7) (T : Tapes Sym7 6), (∀ x ∈ L, g x ≠ st) →
      (∀ p (hp : p < L.length), T.cells i (T.head i + p) = L[p]) →
      (∀ x ∈ L, c x = true) → c (T.cells i (T.head i + L.length)) = false →
      T.cells j = tapeOf S7 P → T.head j = P.length + 1 →
      Runs st (copy i j c g) T L.length
        ⟨Function.update T.cells j (tapeOf S7 (P ++ L.map g)),
          Function.update (Function.update T.head i (T.head i + L.length)) j
            (P.length + 1 + L.length)⟩ := by
  intro L
  induction L with
  | nil =>
    intro P T _ _ _ hend hcj hhj
    simp only [List.length_nil, List.map_nil, List.append_nil, Nat.add_zero]
    have e : (⟨Function.update T.cells j (tapeOf S7 P),
        Function.update (Function.update T.head i (T.head i)) j (P.length + 1)⟩ : Tapes Sym7 6) = T := by
      rw [← hcj, ← hhj]; simp
    rw [e]
    exact loop_stop (by simpa [Tapes.read] using hend)
  | cons x L ih =>
    intro P T hg hL hc hend hcj hhj
    have hx : T.cells i (T.head i) = x := by
      have := hL 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this
    have hrj : T.cells j (T.head j) = blank := by
      rw [hcj, hhj, tapeOf_succ, List.getD_eq_default _ _ le_rfl]; rfl
    have h1 := act_runs (st := st)
      (fun a => wr2 a i (a i) Move.right j (g (a i)) Move.right) T
    rw [fix_wr2 _ _ _ _ _ _ _ hij (Or.inl ⟨rfl, by simp⟩)
      (Or.inr ⟨hj, by simp [Tapes.read, hrj], by
        simp only [Tapes.read]; rw [hx]; exact hg x (by simp)⟩), write_wr2 _ _ _ _ _ _ _ hij]
      at h1
    simp only [Tapes.read, Function.update_eq_self, moveHead] at h1
    rw [hx, hcj, hhj, tapeOf_append_singleton] at h1
    have hij' : j ≠ i := Ne.symm hij
    have := ih (P ++ [g x])
      ⟨Function.update T.cells j (tapeOf S7 (P ++ [g x])),
        Function.update (Function.update T.head i (T.head i + 1)) j (P.length + 1 + 1)⟩
      (fun y hy => hg y (by simp [hy]))
      (fun p hp => by
        simp only [Function.update_apply, if_neg hij, if_neg hij']
        have := hL (p + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 p] using this)
      (fun y hy => hc y (by simp [hy]))
      (by
        simp only [Function.update_apply, if_neg hij, if_neg hij']
        simpa [Nat.add_assoc, Nat.add_comm 1 L.length] using hend)
      (by simp) (by simp)
    simp only [Function.update_self, Function.update_idem, Function.update_apply, if_neg hij',
      if_true] at this
    have h := loop_iter (c := fun a => c (a i)) (by simpa [Tapes.read, hx] using hc x (by simp))
      (by omega) h1 this
    rw [show 1 + L.length = (x :: L).length by simp [Nat.add_comm]] at h
    change Runs st (copy i j c g) _ _ _ at h
    convert h using 2
    · funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [Function.update_apply, hl]
    · funext l
      by_cases hl : l = j
      · subst hl; simp; omega
      · by_cases hl' : l = i
        · subst hl'; simp [Function.update_apply, hl]; omega
        · simp [Function.update_apply, hl, hl']

theorem output_runs (T : Tapes Sym7 6) (W : List Sym7)
    (hW : W = [] ∨ ∃ R, R ≠ [] ∧ W = encRun R)
    (hc2 : T.cells 2 = tapeOf S7 W) (hc1 : T.cells 1 = tapeOf S7 []) (hh1 : T.head 1 = 0) :
    Runs st output T (T.head 2 + 2 + (W.length - 1))
      ⟨Function.update T.cells 1 (tapeOf S7 ((W.dropLast).map outG)),
        Function.update (Function.update T.head 2 (1 + (W.length - 1))) 1
          (1 + (W.length - 1))⟩ := by
  -- shape of `W`: a body followed (if nonempty) by `runend`
  obtain ⟨B, hWB, hB, hend⟩ : ∃ B : List Sym7, W.dropLast = B ∧
      (∀ x ∈ B, x ≠ runend ∧ x ≠ blank ∧ x ≠ st) ∧ tapeOf S7 W (1 + B.length) ∈ [blank, runend] := by
    rcases hW with rfl | ⟨R, hR, rfl⟩
    · exact ⟨[], rfl, by simp, by simp; left; rfl⟩
    · obtain ⟨B, hB, hB'⟩ := encRun_split R hR
      refine ⟨B, by rw [hB, List.dropLast_concat], fun x hx => ?_, ?_⟩
      · have := hB' x hx
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [isRunBody] at this
      · rw [hB, tapeOf_one_add]; simp
  have hWst : ∀ x ∈ W, x ≠ st := by
    rcases hW with rfl | ⟨R, -, rfl⟩
    · simp
    · exact encRun_ne_st R
  have hlen : W.length - 1 = B.length := by rw [← hWB, List.length_dropLast]
  rw [hWB, hlen]
  have h1 := rewind_runs 2 T W hWst hc2
  have h2 := (mv_runs st 1 Move.right ⟨T.cells, Function.update T.head 2 1⟩
    (fun h => by cases h)).of_eq
    (T'' := ⟨T.cells, Function.update (Function.update T.head 2 1) 1 1⟩) (by simp [moveHead, hh1]) rfl
  have h3 := copy_runs' 2 1 (by decide) (by decide) (fun s => decide (s ≠ runend ∧ s ≠ blank))
    outG B [] ⟨T.cells, Function.update (Function.update T.head 2 1) 1 1⟩ (fun x hx => by have := (hB x hx).2.2; cases x <;> simp_all [outG])
    (fun p hp => by
      simp only [Function.update_apply]
      simp only [show (2 : Fin 6) ≠ 1 by decide, if_false, if_true]
      subst hWB
      rw [hc2, Nat.add_comm, tapeOf_succ, List.getD_eq_getElem _ _ (by simp at hp ⊢; omega),
        List.getElem_dropLast])
    (fun x hx => by have := hB x hx; simp [this.1, this.2.1])
    (by
      simp only [Function.update_apply]
      simp only [show (2 : Fin 6) ≠ 1 by decide, if_false, if_true]
      rw [hc2]
      simp at hend
      rcases hend with h | h <;> simp [h])
    (by simp [hc1]) (by simp)
  refine (seq_runs h1 (seq_runs h2 h3)).of_eq ?_ (by omega)
  simp only [List.nil_append, List.length_nil, Function.update_idem]
  congr 1
  funext l; fin_cases l <;> simp <;> omega

/-! ## The compiler transfer -/

theorem compile_haltsWithOutputW (P : Prog Sym7 6) (w v : List (Option Bool)) (t : ℕ)
    (T' : Tapes Sym7 6)
    (h : Runs S7.st P ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else tapeOf S7 [],
      fun _ => 0⟩ t T')
    (hout : T'.cells 1 = tapeOf S7 (v.map letter)) :
    (compile S7 hk6 P).HaltsWithOutputW w (t + 1) v := by
  have hl : (compile S7 hk6 P).letterSym = letter := by
    funext x; rcases x with _ | b
    · rfl
    · cases b <;> rfl
  have hi : (compile S7 hk6 P).initCfgW w = toCfg S7 hk6 P (some P.q0)
      ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else tapeOf S7 [], fun _ => 0⟩ := by
    simp only [MultitapeTM.initCfgW, toCfg, hl]
    congr 1
  unfold MultitapeTM.HaltsWithOutputW
  rw [hi, compile_halts S7 hk6 P h]
  refine ⟨rfl, ?_⟩
  simp only [toCfg]
  rw [show (compile S7 hk6 P).outTape = (1 : Fin 6) from rfl, hout, hl]
  funext p
  cases p <;> rfl

end IntMul.Mach.MS

-- ===== MSMain =====


/-!
# Merge sort: passes, the main loop and the final bound
-/

namespace IntMul.Mach.MS
open IntMul IntMul.Mach Sym7 IntMul.Mach.MSort
set_option linter.unusedSectionVars false
variable {α : Type*}

/-! ## List bookkeeping -/

theorem zipMerge_odds_evens : ∀ Rs : List (List Rec),
    zipMerge (odds Rs) (evens Rs) = mergePairs le7 Rs
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    simp only [odds, evens, zipMerge, mergePairs]
    rw [zipMerge_odds_evens rest]

theorem odds_evens_len : ∀ Rs : List α,
    (evens Rs).length ≤ (odds Rs).length ∧ (odds Rs).length ≤ (evens Rs).length + 1
  | [] => by simp [odds, evens]
  | [a] => by simp [odds, evens]
  | a :: b :: rest => by
    have := odds_evens_len rest
    simp only [odds, evens, List.length_cons]; omega

theorem mem_odds : ∀ {Rs : List α} {x : α}, x ∈ odds Rs → x ∈ Rs
  | [], _, h => by simp [odds] at h
  | [a], _, h => by simpa [odds] using h
  | a :: b :: rest, x, h => by
    simp only [odds, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · simp [mem_odds h]

theorem mem_evens : ∀ {Rs : List α} {x : α}, x ∈ evens Rs → x ∈ Rs
  | [], _, h => by simp [evens] at h
  | [a], _, h => by simp [evens] at h
  | a :: b :: rest, x, h => by
    simp only [evens, List.mem_cons] at h
    rcases h with h | h
    · simp [h]
    · simp [mem_evens h]

theorem encRuns_odds_evens : ∀ Rs : List (List Rec),
    (encRuns (odds Rs)).length + (encRuns (evens Rs)).length = (encRuns Rs).length
  | [] => rfl
  | [a] => by simp [odds, evens, encRuns]
  | a :: b :: rest => by
    have := encRuns_odds_evens rest
    simp only [odds, evens, encRuns_cons, List.length_append]; omega

def recLen (r : Rec) : ℕ := (body r).length + 1

theorem length_encRun (a : List Rec) : (encRun a).length = (a.map recLen).sum := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    rw [length_encRun_cons, ih]
    rcases a with _ | ⟨y, a⟩
    · simp [encRun, recLen]
    · simp [recLen]

theorem length_encRuns (Rs : List (List Rec)) :
    (encRuns Rs).length = (Rs.flatten.map recLen).sum := by
  induction Rs with
  | nil => rfl
  | cons a Rs ih => rw [encRuns_cons, List.length_append, length_encRun, ih]; simp

theorem length_encRuns_ms (cs : List (List Rec)) :
    (encRuns (cs.map (·.mergeSort le7))).length = (cs.flatten.map recLen).sum := by
  rw [length_encRuns]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.sum_append] at ih ⊢
    rw [ih, ((List.mergeSort_perm c le7).map recLen).sum_eq]

theorem le7_trans : ∀ a b c : Rec, le7 a b → le7 b c → le7 a c := recLe_trans
theorem le7_total : ∀ a b : Rec, le7 a b || le7 b a := recLe_total

theorem mergePairs_ms (cs : List (List Rec)) :
    mergePairs le7 (cs.map (·.mergeSort le7)) = (pairUp cs).map (·.mergeSort le7) :=
  mergePairs_map le7 le7_trans le7_total cs

theorem mem_pairUp_ne : ∀ (cs : List (List Rec)), (∀ c ∈ cs, c ≠ []) → ∀ c ∈ pairUp cs, c ≠ []
  | [], _, c, h => by simp [pairUp] at h
  | [a], hc, c, h => by simp [pairUp] at h; subst h; exact hc _ (by simp)
  | a :: b :: rest, hc, c, h => by
    simp only [pairUp, List.mem_cons] at h
    rcases h with h | h
    · subst h; simp [hc a (by simp)]
    · exact mem_pairUp_ne rest (fun c hc' => hc c (by simp [hc'])) c h

theorem ms_ne (c : List Rec) (h : c ≠ []) : c.mergeSort le7 ≠ [] := by
  intro e; have := congrArg List.length e; simp at this; exact h this

theorem mem_flatten_ms {cs : List (List Rec)} {a : List Rec} {r : Rec}
    (ha : a ∈ cs.map (·.mergeSort le7)) (hr : r ∈ a) : r ∈ cs.flatten := by
  simp only [List.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  exact List.mem_flatten.mpr ⟨c, hc, (List.mem_mergeSort).mp hr⟩


theorem encRuns_ne_st (Rs : List (List Rec)) : ∀ x ∈ encRuns Rs, x ≠ st := by
  intro x hx
  simp only [encRuns, List.mem_flatten, List.mem_map] at hx
  obtain ⟨_, ⟨a, -, rfl⟩, hx⟩ := hx
  exact encRun_ne_st a x hx

def MSR (cs : List (List Rec)) : List (List Rec) := cs.map (fun c => c.mergeSort le7)

/-- The state at the head of the main loop. -/
def Inv (T : Tapes Sym7 6) (cs : List (List Rec)) : Prop :=
  T.cells 1 = tapeOf S7 [] ∧ T.head 1 = 0 ∧
  T.cells 2 = tapeOf S7 (encRuns (MSR cs)) ∧ T.head 2 = (encRuns (MSR cs)).length + 1 ∧
  T.cells 3 = tapeOf S7 (encRuns (odds (MSR cs))) ∧ T.head 3 = 1 ∧
  T.cells 4 = tapeOf S7 (encRuns (evens (MSR cs))) ∧ T.head 4 = 1 ∧
  (∃ F, T.cells 5 = tapeOf S7 F ∧ F.length ≤ 1 ∧ ∀ s ∈ F, s ≠ st) ∧ T.head 5 = 1

theorem MSR_ne (cs : List (List Rec)) (hne : ∀ c ∈ cs, c ≠ []) : ∀ r ∈ MSR cs, r ≠ [] := by
  intro r hr
  simp only [MSR, List.mem_map] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  exact ms_ne c (hne c hc)

set_option maxHeartbeats 2000000 in
theorem pass_runs (ℓ : ℕ) (cs : List (List Rec)) (hne : ∀ c ∈ cs, c ≠ [])
    (hl : ∀ r ∈ cs.flatten, r.1.length = ℓ) (T : Tapes Sym7 6) (hI : Inv T cs) :
    ∃ t ≤ 12 * (cs.flatten.map recLen).sum + 12, ∃ T',
      Runs st pass T t T' ∧ Inv T' (pairUp cs) := by
  obtain ⟨c1, h1, c2, h2, c3, h3, c4, h4, ⟨F, c5, hF1, hF2⟩, h5⟩ := hI
  have hL : (encRuns (MSR cs)).length = (cs.flatten.map recLen).sum := length_encRuns_ms cs
  have hL' : (encRuns (MSR (pairUp cs))).length = (cs.flatten.map recLen).sum := by
    rw [← flatten_pairUp cs]; exact length_encRuns_ms (pairUp cs)
  have hmp : mergePairs le7 (MSR cs) = MSR (pairUp cs) := mergePairs_ms cs
  have hoe := encRuns_odds_evens (MSR cs)
  have hRne := MSR_ne cs hne
  have hRne' := MSR_ne (pairUp cs) (mem_pairUp_ne cs hne)
  have hlR : ∀ a ∈ MSR cs, ∀ r ∈ a, r.1.length = ℓ := fun a ha r hr => hl r (mem_flatten_ms ha hr)
  -- a. wipe `C`
  have ra := wipe_runs 2 (by decide) T _ (encRuns_ne_st _) c2 h2
  set Ta : Tapes Sym7 6 := ⟨Function.update T.cells 2 (tapeOf S7 []), Function.update T.head 2 1⟩
    with hTa
  -- b. merge all pairs
  obtain ⟨tb, htb, Tb, rb, p1, p2, p3, p4, ⟨F', p5a, p5b, p5c⟩, p6, p7, p8⟩ :=
    mergeAll_runs ℓ (odds (MSR cs)) (evens (MSR cs)) (odds_evens_len _).1 (odds_evens_len _).2
      (fun a ha => hRne a (mem_odds ha)) (fun a ha => hRne a (mem_evens ha))
      (fun a ha => hlR a (mem_odds ha)) (fun a ha => hlR a (mem_evens ha))
      Ta [] [] [] F (by simp [hTa, c3]) (by simp [hTa, h3]) (by simp [hTa, c3, tapeOf]; rfl)
      (by simp [hTa, c4]) (by simp [hTa, h4]) (by simp [hTa, c4, tapeOf]; rfl)
      (by simp [hTa]) (by simp [hTa]) (by simp [hTa, c5]) hF1 hF2 (by simp [hTa, h5])
  rw [zipMerge_odds_evens, hmp] at p1 p2
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at p1 p2 p3 p4
  -- c, d. wipe `A` and `B`
  have rc := wipe_runs 3 (by decide) Tb _ (encRuns_ne_st (odds (MSR cs)))
    (by rw [p7 3 (by decide) (by decide)]; simp [hTa, c3]) (by rw [p3]; omega)
  set Tc : Tapes Sym7 6 := ⟨Function.update Tb.cells 3 (tapeOf S7 []), Function.update Tb.head 3 1⟩
    with hTc
  have rd := wipe_runs 4 (by decide) Tc _ (encRuns_ne_st (evens (MSR cs)))
    (by simp [hTc]; rw [p7 4 (by decide) (by decide)]; simp [hTa, c4]) (by simp [hTc]; rw [p4]; omega)
  set Td : Tapes Sym7 6 := ⟨Function.update Tc.cells 4 (tapeOf S7 []), Function.update Tc.head 4 1⟩
    with hTd
  -- e. rewind `C`
  have re := rewind_runs 2 Td _ (encRuns_ne_st (MSR (pairUp cs))) (by simp [hTd, hTc, p1])
  set Te : Tapes Sym7 6 := ⟨Td.cells, Function.update Td.head 2 1⟩ with hTe
  -- f. distribute
  have rf := dist_runs (MSR (pairUp cs)) hRne' Te [] [] [] (by simp [hTe, hTd, hTc, p1])
    (by simp [hTe]) (by simp [hTe, hTd, hTc]) (by simp [hTe, hTd, hTc])
    (by simp [hTe, hTd, hTc]) (by simp [hTe, hTd, hTc])
  set Tf : Tapes Sym7 6 := ⟨Function.update (Function.update Te.cells 3
      (tapeOf S7 ([] ++ encRuns (odds (MSR (pairUp cs)))))) 4
      (tapeOf S7 ([] ++ encRuns (evens (MSR (pairUp cs))))),
    Function.update (Function.update (Function.update Te.head 2
      (([] : List Sym7).length + 1 + (encRuns (MSR (pairUp cs))).length)) 3
      (([] : List Sym7).length + 1 + (encRuns (odds (MSR (pairUp cs)))).length)) 4
      (([] : List Sym7).length + 1 + (encRuns (evens (MSR (pairUp cs)))).length)⟩ with hTf
  -- g. rewind `A` and `B`
  have rg := rewind_runs 3 Tf _ (encRuns_ne_st (odds (MSR (pairUp cs)))) (by simp [hTf])
  set Tg : Tapes Sym7 6 := ⟨Tf.cells, Function.update Tf.head 3 1⟩ with hTg
  have rh := rewind_runs 4 Tg _ (encRuns_ne_st (evens (MSR (pairUp cs)))) (by simp [hTg, hTf])
  have hoe' := encRuns_odds_evens (MSR (pairUp cs))
  refine ⟨_, ?_, _, seq_runs ra (seq_runs rb (seq_runs rc (seq_runs rd (seq_runs re (seq_runs rf
    (seq_runs rg rh)))))), ?_⟩
  · have e1 : Td.head 2 = (encRuns (MSR (pairUp cs))).length + 1 := by simp [hTd, hTc, p2]; omega
    have e2 : Tf.head 3 = (encRuns (odds (MSR (pairUp cs)))).length + 1 := by simp [hTf]; omega
    have e3 : Tg.head 4 = (encRuns (evens (MSR (pairUp cs)))).length + 1 := by simp [hTg, hTf]; omega
    rw [e1, e2, e3]
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨F', ?_, p5b, p5c⟩, ?_⟩
    · simp [hTg, hTf, hTe, hTd, hTc]; rw [p7 1 (by decide) (by decide)]; simp [hTa, c1]
    · simp [hTg, hTf, hTe, hTd, hTc]; rw [p8 1 (by decide)]; simp [hTa, h1]
    · simp [hTg, hTf, hTe, hTd, hTc, p1]
    · simp [hTg, hTf, hTe, hTd, hTc]; omega
    · simp [hTg, hTf]
    · simp [hTg, hTf]
    · simp [hTg, hTf]
    · simp [hTg, hTf]
    · simp [hTg, hTf, hTe, hTd, hTc, p5a]
    · simp [hTg, hTf, hTe, hTd, hTc, p6]


def bnot (a : Fin 6 → Sym7) : Bool := decide (a 4 ≠ blank)

theorem evens_ne_nil : ∀ (Rs : List α), 2 ≤ Rs.length → evens Rs ≠ []
  | a :: b :: rest, _ => by simp [evens]

theorem evens_one (a : α) : evens [a] = [] := rfl

theorem mainLoop_runs (ℓ : ℕ) : ∀ (k : ℕ) (cs : List (List Rec)), cs.length = k → 1 ≤ k →
    (∀ c ∈ cs, c ≠ []) → (∀ r ∈ cs.flatten, r.1.length = ℓ) → ∀ T, Inv T cs →
    ∃ t ≤ Nat.clog 2 k * (12 * (cs.flatten.map recLen).sum + 12), ∃ T',
      Runs st (loop bnot pass) T t T' ∧
      T'.cells 1 = tapeOf S7 [] ∧ T'.head 1 = 0 ∧
      T'.cells 2 = tapeOf S7 (encRun (cs.flatten.mergeSort le7)) ∧
      T'.head 2 = (cs.flatten.map recLen).sum + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro cs hk h1 hne hl T hI
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
      rcases cs with _ | ⟨c, _ | ⟨d, cs⟩⟩
      · simp at hk
      · exact ⟨c, rfl⟩
      · simp at hk
    obtain ⟨c1, h1', c2, h2', c3, h3', c4, h4', -, -⟩ := hI
    refine ⟨0, by simp, T, loop_stop ?_, c1, h1', ?_, ?_⟩
    · simp [bnot, Tapes.read, c4, h4', MSR, evens_one, encRuns, tapeOf]; rfl
    · rw [c2]; simp [MSR, encRuns]
    · rw [h2']; simp [MSR, encRuns, length_encRun]
      rw [((List.mergeSort_perm c le7).map recLen).sum_eq]
  · have hk2 : 2 ≤ k := by omega
    have hcond : bnot T.read = true := by
      obtain ⟨-, -, -, -, -, -, c4, h4', -, -⟩ := hI
      have hev := evens_ne_nil (MSR cs) (by simp [MSR]; omega)
      obtain ⟨a, Rs, he⟩ := List.exists_cons_of_ne_nil hev
      have ha : a ≠ [] := MSR_ne cs hne a (mem_evens (by rw [he]; simp))
      have := tapeOf_first_ne_blank [] (encRun a) (encRuns Rs) (encRun_ne_nil a ha)
        (encRun_ne_blank a)
      simp only [bnot, Tapes.read, c4, h4', he, encRuns_cons]
      simpa using this
    obtain ⟨t1, ht1, T1, r1, hI1⟩ := pass_runs ℓ cs hne hl T hI
    have hlen : (pairUp cs).length = (k + 1) / 2 := by rw [length_pairUp, hk]
    obtain ⟨t2, ht2, T2, r2, o1, o2, o3, o4⟩ := ih ((k + 1) / 2) (by omega) (pairUp cs) hlen
      (by omega) (mem_pairUp_ne cs hne) (by rw [flatten_pairUp]; exact hl) T1 hI1
    rw [flatten_pairUp] at ht2 o3 o4
    have hpos : 0 < t1 := by
      rcases Nat.eq_zero_or_pos t1 with h | h
      · subst h
        -- `pass` takes at least the two steps of `wipe 2`
        exfalso
        cases r1 with
        | done h0 => simp [pass, wipe, seq, mv, act] at h0
      · exact h
    refine ⟨t1 + t2, ?_, T2, loop_iter hcond hpos r1 r2, o1, o2, o3, o4⟩
    rw [Nat.clog_of_two_le (by norm_num) hk2, show k + 2 - 1 = k + 1 by omega]
    nlinarith


theorem mainLoop0_runs (ℓ : ℕ) (cs : List (List Rec)) (hne : ∀ c ∈ cs, c ≠ [])
    (hl : ∀ r ∈ cs.flatten, r.1.length = ℓ) (T : Tapes Sym7 6) (hI : Inv T cs) :
    ∃ t ≤ Nat.clog 2 cs.length * (12 * (cs.flatten.map recLen).sum + 12), ∃ T',
      Runs st (loop bnot pass) T t T' ∧
      T'.cells 1 = tapeOf S7 [] ∧ T'.head 1 = 0 ∧
      T'.cells 2 = tapeOf S7 (encRun (cs.flatten.mergeSort le7)) ∧
      T'.head 2 = (cs.flatten.map recLen).sum + 1 := by
  rcases cs with _ | ⟨c, cs⟩
  · obtain ⟨c1, h1, c2, h2, c3, h3, c4, h4, -, -⟩ := hI
    refine ⟨0, by simp, T, loop_stop ?_, c1, h1, ?_, ?_⟩
    · simp [bnot, Tapes.read, c4, h4, MSR, evens, encRuns, tapeOf]; rfl
    · rw [c2]; simp [MSR, encRuns, encRun]
    · rw [h2]; simp [MSR, encRuns]
  · exact mainLoop_runs ℓ _ (c :: cs) rfl (by simp) hne hl T hI

theorem MSR_singletons (recs : List Rec) : MSR (recs.map fun r => [r]) = recs.map fun r => [r] :=
  mergeSort_of_singleton_chunks le7 recs

theorem flatten_singletons (recs : List Rec) : (recs.map fun r => [r]).flatten = recs := by
  induction recs <;> simp_all

theorem recLen_sum (recs : List Rec) :
    (encRuns (recs.map fun r => [r])).length = (recs.map recLen).sum := by
  have := length_encRuns (recs.map fun r => [r])
  rw [this, flatten_singletons]

set_option maxHeartbeats 2000000 in
theorem main_runs (ℓ q : ℕ) (recs : List Rec) (hrec : ∀ r ∈ recs, r.1.length = ℓ ∧ r.2.length = q) :
    ∃ t ≤ 30 * ((enc' recs).length + 1) * (Nat.clog 2 recs.length + 1), ∃ T',
      Runs st main ⟨fun i => if i = 0 then tapeOf S7 ((enc' recs).map letter) else tapeOf S7 [],
        fun _ => 0⟩ t T' ∧
      T'.cells 1 = tapeOf S7 ((enc' (recs.mergeSort le7)).map letter) := by
  set w := enc' recs with hw
  set cs : List (List Rec) := recs.map fun r => [r] with hcs
  have hC : initC w = encRuns (MSR cs) := by rw [hw, initC_enc', MSR_singletons]
  have hL : (initC w).length ≤ w.length + 1 := by
    simp only [initC]; split
    · simp
    · simp [convL_length]
  have hflat : cs.flatten = recs := flatten_singletons recs
  have hLsum : (cs.flatten.map recLen).sum = (initC w).length := by
    rw [hC, MSR_singletons, recLen_sum, hflat]
  have hne : ∀ c ∈ cs, c ≠ [] := by
    intro c hc; simp only [hcs, List.mem_map] at hc; obtain ⟨r, -, rfl⟩ := hc; simp
  have hl : ∀ r ∈ cs.flatten, r.1.length = ℓ := by rw [hflat]; exact fun r hr => (hrec r hr).1
  have hRne := MSR_ne cs hne
  -- init
  have r1 := init_runs w
  set T1 : Tapes Sym7 6 := ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else if i = 2 then
      tapeOf S7 (initC w) else tapeOf S7 [],
    fun i => if i = 0 then w.length + 1 else if i = 1 then 0 else if i = 2 then
      (initC w).length + 1 else 1⟩ with hT1
  have r2 := rewind_runs 2 T1 _ (encRuns_ne_st (MSR cs)) (by simp [hT1, hC])
  set T2 : Tapes Sym7 6 := ⟨T1.cells, Function.update T1.head 2 1⟩ with hT2
  have r3 := dist_runs (MSR cs) hRne T2 [] [] [] (by simp [hT2, hT1, hC]) (by simp [hT2])
    (by simp [hT2, hT1]) (by simp [hT2, hT1]) (by simp [hT2, hT1]) (by simp [hT2, hT1])
  set T3 : Tapes Sym7 6 := ⟨Function.update (Function.update T2.cells 3
      (tapeOf S7 ([] ++ encRuns (odds (MSR cs))))) 4
      (tapeOf S7 ([] ++ encRuns (evens (MSR cs)))),
    Function.update (Function.update (Function.update T2.head 2
      (([] : List Sym7).length + 1 + (encRuns (MSR cs)).length)) 3
      (([] : List Sym7).length + 1 + (encRuns (odds (MSR cs))).length)) 4
      (([] : List Sym7).length + 1 + (encRuns (evens (MSR cs))).length)⟩ with hT3
  have r4 := rewind_runs 3 T3 _ (encRuns_ne_st (odds (MSR cs))) (by simp [hT3])
  set T4 : Tapes Sym7 6 := ⟨T3.cells, Function.update T3.head 3 1⟩ with hT4
  have r5 := rewind_runs 4 T4 _ (encRuns_ne_st (evens (MSR cs))) (by simp [hT4, hT3])
  set T5 : Tapes Sym7 6 := ⟨T4.cells, Function.update T4.head 4 1⟩ with hT5
  have hI : Inv T5 cs := by
    refine ⟨by simp [hT5, hT4, hT3, hT2, hT1], by simp [hT5, hT4, hT3, hT2, hT1],
      by simp [hT5, hT4, hT3, hT2, hT1, hC], by simp [hT5, hT4, hT3, hT2]; omega,
      by simp [hT5, hT4, hT3], by simp [hT5, hT4], by simp [hT5, hT4, hT3], by simp [hT5],
      ⟨[], by simp [hT5, hT4, hT3, hT2, hT1], by simp, by simp⟩, by simp [hT5, hT4, hT3, hT2, hT1]⟩
  obtain ⟨t6, ht6, T6, r6, o1, o2, o3, o4⟩ := mainLoop0_runs ℓ cs hne hl T5 hI
  rw [hflat] at o3
  have r7 := output_runs T6 (encRun (recs.mergeSort le7))
    (by
      by_cases h : recs = []
      · left; subst h; simp [encRun]
      · right; exact ⟨_, ms_ne recs h, rfl⟩) o3 o1 o2
  have hoe := encRuns_odds_evens (MSR cs)
  have hlenMS : (encRun (recs.mergeSort le7)).length = (cs.flatten.map recLen).sum := by
    rw [length_encRun, hflat, ((List.mergeSort_perm recs le7).map recLen).sum_eq]
  have hlenC : (encRuns (MSR cs)).length = (initC w).length := by rw [hC]
  refine ⟨_, ?_, _, seq_runs r1 (seq_runs r2 (seq_runs r3 (seq_runs r4 (seq_runs r5
    (seq_runs r6 r7))))), ?_⟩
  · have e1 : T1.head 2 = (initC w).length + 1 := by simp [hT1]
    have e2 : T3.head 3 = (encRuns (odds (MSR cs))).length + 1 := by simp [hT3]; omega
    have e3 : T4.head 4 = (encRuns (evens (MSR cs))).length + 1 := by simp [hT4, hT3]; omega
    have hcl : cs.length = recs.length := by simp [hcs]
    rw [e1, e2, e3, o4, hlenMS]
    rw [hLsum, hcl] at ht6
    have hite : (if w = [] then 0 else w.length + 1) ≤ w.length + 1 := by split <;> omega
    rw [hLsum]
    generalize (if w = [] then 0 else w.length + 1) = I at hite ⊢
    generalize Nat.clog 2 recs.length = K at ht6 ⊢
    generalize (initC w).length = L at *
    generalize w.length = N at *
    have hsub : L - 1 ≤ L := Nat.sub_le _ _
    generalize L - 1 = L' at *
    have hKL := Nat.mul_le_mul_left K hL
    nlinarith
  · simp only [Function.update_self]
    by_cases h : recs = []
    · subst h; simp [encRun, enc', joinSep]
    · rw [output_list _ (ms_ne recs h)]

end IntMul.Mach.MS

-- ===== TDefs =====


/-!
# Matrix transposition on six tapes

Same alphabet and tape roles as the merge sort machine.  An entry `e` is stored as `enc e ++ [sep]`,
a cell (a list of entries) is followed by `rend`, and a block (a list of cells) by `runend`.

* `m ≤ k`: *riffle*.  Start with one block per row, one singleton cell per entry; each pass merges
  adjacent blocks cell by cell.  After `⌈log₂ m⌉` passes one block remains: the transpose.
* `k < m`: *unriffle*.  Start with one block whose cells are the rows; each pass replaces the block
  list `G` by `G.map (·.map odds) ++ G.map (·.map evens)`.  After `⌈log₂ k⌉` passes block `j` holds
  column `j`.
-/

namespace IntMul.Mach.TP

open IntMul IntMul.Mach IntMul.Mach.MS Sym7

set_option linter.unusedSectionVars false

/-! ## Encodings -/

abbrev Ent := List Bool

def encE (e : Ent) : List Sym7 := enc e ++ [sep]

def encC (c : List Ent) : List Sym7 := c.flatMap encE ++ [rend]

def encB (b : List (List Ent)) : List Sym7 := b.flatMap encC ++ [runend]

def encBs (bs : List (List (List Ent))) : List Sym7 := bs.flatMap encB

/-- The input/output word format: entries joined by `#`, rows joined by `##`. -/
def encIn (rows : List (List Ent)) : List (Option Bool) :=
  List.intercalate [none, none] (rows.map fun r => joinSep (r.map bits))

/-- The `k` columns of a list of rows. -/
def cols (k : ℕ) (rows : List (List Ent)) : List (List Ent) :=
  (List.range k).map fun j => rows.map fun r => r.getD j []

/-- The shape hypotheses: `m` rows of `k` entries of `ℓ` bits, all positive. -/
def Shape (m k ℓ : ℕ) (rows : List (List Ent)) : Prop :=
  rows.length = m ∧ 1 ≤ m ∧ 1 ≤ k ∧ 1 ≤ ℓ ∧ ∀ r ∈ rows, r.length = k ∧ ∀ e ∈ r, e.length = ℓ

/-- The final unriffle state: column `j` as one-entry cells, then `z` blocks of empty cells. -/
def ufinal (m k z : ℕ) (rows : List (List Ent)) : List (List (List Ent)) :=
  (cols k rows).map (fun c => c.map fun e => [e]) ++ List.replicate z (List.replicate m [])

/-! ## Programs -/

def notBlank : Sym7 → Bool
  | blank => false
  | _ => true

/-- Move tape `i` one cell right when the scanned symbol is `s`. -/
def skipIf (i : Fin 6) (s : Sym7) : Prog Sym7 6 := ite (fun a => decide (a i = s)) (mv i Move.right) skip

/-- Riffle one pair of blocks under `A` and `B` onto `C`. -/
def rcell : Prog Sym7 6 :=
  seq (copy 3 2 isBody id) (seq (copy 4 2 isBody id) (seq (cp1 3 2) (mv 4 Move.right)))

def rpair : Prog Sym7 6 :=
  ite (fun a => decide (a 4 = blank)) (copyRun 3 2)
    (seq (loop (fun a => decide (a 3 ≠ runend)) rcell) (seq (cp1 3 2) (mv 4 Move.right)))

def rall : Prog Sym7 6 := loop (fun a => decide (a 3 ≠ blank)) rpair

def rpass : Prog Sym7 6 :=
  seq (wipe 2) <| seq rall <| seq (wipe 3) <| seq (wipe 4) <| seq (rewind 2) <|
  seq dist <| seq (rewind 3) (rewind 4)

/-- Input to riffle form: `a#b##c` ↦ `a sep rend b sep rend runend c sep rend runend`. -/
def rconvStep : Prog Sym7 6 :=
  seq (copy 0 2 isBit id) <| seq (wsym 2 sep) <| seq (wsym 2 rend) <|
  ite (fun a => decide (a 0 = sep))
    (seq (mv 0 Move.right) (ite (fun a => decide (a 0 = sep)) (seq (mv 0 Move.right) (wsym 2 runend)) skip))
    (wsym 2 runend)

def rmain : Prog Sym7 6 :=
  seq (loop (fun a => decide (a 0 ≠ blank)) rconvStep) <| seq (rewind 2) <| seq dist <|
  seq (rewind 3) <| seq (rewind 4) (loop (fun a => decide (a 4 ≠ blank)) rpass)

/-- Toggle the parity flag on tape `4`. -/
def tog : Prog Sym7 6 := act (fun a => wr1 a 4 (if a 4 = zero then one else zero) Move.stay)

/-- One entry: copy it to `A` if the parity flag is `p`, otherwise skip it. -/
def uent (p : Sym7) : Prog Sym7 6 :=
  seq (ite (fun a => decide (a 4 = p)) (seq (copy 2 3 isBit id) (cp1 2 3))
    (seq (scanR 2 isBit) (mv 2 Move.right))) tog

def uchunk (p : Sym7) : Prog Sym7 6 :=
  seq (act (fun a => wr1 a 4 zero Move.stay)) <|
  seq (loop (fun a => decide (a 2 ≠ rend)) (uent p)) (cp1 2 3)

def ublock (p : Sym7) : Prog Sym7 6 :=
  seq (loop (fun a => decide (a 2 ≠ runend)) (uchunk p)) (cp1 2 3)

def usweep (p : Sym7) : Prog Sym7 6 := loop (fun a => decide (a 2 ≠ blank)) (ublock p)

/-- Whether the first cell of `C` has at least two entries; result on the flag tape. -/
def ucheck : Prog Sym7 6 :=
  seq (scanR 2 isBit) <| seq (mv 2 Move.right) <|
  seq (act (fun a => wr1 a 5 (if a 2 = rend then zero else one) Move.stay)) (rewind 2)

def upass : Prog Sym7 6 :=
  seq (usweep zero) <| seq (rewind 2) <| seq (usweep one) <| seq (wipe 2) <| seq (rewind 3) <|
  seq (copy 3 2 notBlank id) <| seq (wipe 3) <| seq (rewind 2) ucheck

/-- Input to unriffle form: `a#b##c` ↦ `a sep b sep rend c sep rend runend`. -/
def uconvStep : Prog Sym7 6 :=
  seq (copy 0 2 isBit id) <| seq (wsym 2 sep) <|
  ite (fun a => decide (a 0 = sep))
    (seq (mv 0 Move.right) (ite (fun a => decide (a 0 = sep)) (seq (mv 0 Move.right) (wsym 2 rend)) skip))
    (wsym 2 rend)

def umain : Prog Sym7 6 :=
  seq (loop (fun a => decide (a 0 ≠ blank)) uconvStep) <| seq (wsym 2 runend) <| seq (rewind 2) <|
  seq ucheck (loop (fun a => decide (a 5 = one)) upass)

/-! ## Choosing the algorithm and output -/

/-- Skip one input row, putting a mark on tape `i` per entry. -/
def rowMarks (i : Fin 6) : Prog Sym7 6 :=
  loop (fun a => isBit (a 0)) (seq (scanR 0 isBit) (seq (wsym i one) (skipIf 0 sep)))

/-- Flag `one` iff `m ≤ k`; tapes `3`, `4` blank, input head on cell `1`. -/
def decideP : Prog Sym7 6 :=
  seq (rowMarks 3) <| seq (rewind 0) <|
  seq (loop (fun a => decide (a 0 ≠ blank))
    (seq (wsym 4 one) (seq (loop (fun a => isBit (a 0)) (seq (scanR 0 isBit) (skipIf 0 sep)))
      (skipIf 0 sep)))) <|
  seq (rewind 0) <| seq (rewind 3) <| seq (rewind 4) <|
  seq (loop (fun a => decide (a 3 ≠ blank) && decide (a 4 ≠ blank))
    (act (fun a => wr2 a 3 (a 3) Move.right 4 (a 4) Move.right))) <|
  seq (act (fun a => wr1 a 5 (if a 4 = blank then one else zero) Move.stay)) <|
  seq (scanR 3 notBlank) <| seq (scanR 4 notBlank) <| seq (wipe 3) (wipe 4)

/-- Final form to output.  `u = false` (riffle): one block, cells joined by `##`.
`u = true` (unriffle): blocks of one-entry cells, blocks joined by `##`. -/
def outStep (u : Bool) : Prog Sym7 6 :=
  seq (copy 2 1 isBit id) <| seq (mv 2 Move.right) <|
  seq (if u then mv 2 Move.right else skip) <|
  ite (fun a => decide (a 2 = if u then runend else rend))
    (seq (mv 2 Move.right) (ite (fun a => isBit (a 2)) (seq (wsym 1 sep) (wsym 1 sep)) skip))
    (wsym 1 sep)

def toutput (u : Bool) : Prog Sym7 6 :=
  seq (rewind 2) (seq (mv 1 Move.right) (loop (fun a => isBit (a 2)) (outStep u)))

def tinit : Prog Sym7 6 :=
  seq (mv 5 Move.right) <| seq (mv 0 Move.right) <|
  seq (mv 2 Move.right) <| seq (mv 3 Move.right) (mv 4 Move.right)

def tmain : Prog Sym7 6 :=
  seq tinit <| seq decideP <|
  ite (fun a => decide (a 5 = one)) (seq rmain (toutput false)) (seq umain (toutput true))

/-- Tapes after `tinit`: input on tape `0`, everything else blank, heads on cell `1` except the
output head. -/
def T0 (w : List (Option Bool)) : Tapes Sym7 6 :=
  ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else tapeOf S7 [], fun i => if i = 1 then 0 else 1⟩

/-- `T0` with the flag tape holding `F`. -/
def TF (w : List (Option Bool)) (F : Sym7) : Tapes Sym7 6 :=
  ⟨Function.update (T0 w).cells 5 (tapeOf S7 [F]), (T0 w).head⟩

def TM6 : MultitapeTM := compile S7 hk6 tmain

end IntMul.Mach.TP

-- ===== TMath =====


namespace IntMul.Mach.TP

open IntMul IntMul.Mach IntMul.Mach.MS Sym7

theorem enc_rows (m k : ℕ) (A : Fin m → Fin k → List Bool) :
    List.intercalate [none, none] (List.ofFn fun i => joinSep (List.ofFn fun j => bits (A i j))) =
      encIn (List.ofFn fun i => List.ofFn fun j => A i j) := by
  simp [encIn, List.map_ofFn, Function.comp_def]

theorem tm_cols_ofFn (m k : ℕ) (A : Fin m → Fin k → List Bool) :
    cols k (List.ofFn fun i => List.ofFn fun j => A i j) =
      List.ofFn fun j => List.ofFn fun i => A i j := by
  apply List.ext_getElem
  · simp [cols]
  · intro n h1 h2
    simp only [cols, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    apply List.ext_getElem
    · simp
    · intro p q1 q2
      simp only [List.getElem_map, List.getElem_ofFn] at *
      have hn : n < k := by simpa [cols] using h1
      rw [List.getD_eq_getElem _ _ (by simpa using hn)]
      simp

theorem enc_cols (m k : ℕ) (A : Fin m → Fin k → List Bool) :
    List.intercalate [none, none] (List.ofFn fun j => joinSep (List.ofFn fun i => bits (A i j))) =
      encIn (cols k (List.ofFn fun i => List.ofFn fun j => A i j)) := by
  rw [tm_cols_ofFn]
  simp [encIn, List.map_ofFn, Function.comp_def]

theorem shape_ofFn (m k ℓ : ℕ) (A : Fin m → Fin k → List Bool) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hl : 1 ≤ ℓ) (hA : ∀ i j, (A i j).length = ℓ) :
    Shape m k ℓ (List.ofFn fun i => List.ofFn fun j => A i j) := by
  refine ⟨by simp, hm, hk, hl, ?_⟩
  intro r hr
  simp only [List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  refine ⟨by simp, ?_⟩
  intro e he
  simp only [List.mem_ofFn] at he
  obtain ⟨j, rfl⟩ := he
  exact hA i j

theorem cols_shape (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) :
    cols k rows ≠ [] ∧ ∀ c ∈ cols k rows, c ≠ [] ∧ ∀ e ∈ c, e ≠ [] := by
  obtain ⟨hlen, hm, hk, hl, hr⟩ := hs
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg List.length h
    simp [cols] at this
    omega
  · intro c hc
    simp only [cols, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    refine ⟨?_, ?_⟩
    · intro h
      have := congrArg List.length h
      simp only [List.length_map, List.length_nil] at this
      omega
    · intro e he
      simp only [List.mem_map] at he
      obtain ⟨r, hr', rfl⟩ := he
      obtain ⟨hrk, hre⟩ := hr r hr'
      have hjr : j < r.length := by omega
      rw [List.getD_eq_getElem _ _ hjr]
      intro h
      have := hre _ (List.getElem_mem hjr)
      rw [h] at this
      simp at this
      omega

end IntMul.Mach.TP

-- ===== TIO =====


namespace IntMul.Mach.TP

open IntMul IntMul.Mach IntMul.Mach.MS Sym7

set_option linter.unusedSectionVars false

/-! ## Words -/

def tio_row (r : List Ent) : List Sym7 := List.intercalate [sep] (r.map enc)

def tio_rowsW : List (List Ent) → List Sym7
  | [] => []
  | [r] => tio_row r
  | r :: rs => tio_row r ++ sep :: sep :: tio_rowsW rs

theorem tio_bits_letter (e : Ent) : (bits e).map letter = enc e := by
  simp [bits, enc, Function.comp_def, letter]

theorem tio_row_cons (e : Ent) (es : List Ent) :
    tio_row (e :: es) = enc e ++ es.flatMap (fun e' => sep :: enc e') := by
  induction es generalizing e with
  | nil => simp [tio_row]
  | cons e' es ih =>
    have := ih e'
    simp only [tio_row, List.map_cons] at this ⊢
    rw [List.intercalate_cons_cons, this]
    simp

theorem tio_joinSep (r : List Ent) : (joinSep (r.map bits)).map letter = tio_row r := by
  induction r with
  | nil => rfl
  | cons e es ih =>
    rcases es with _ | ⟨e', es⟩
    · simp [joinSep, tio_row, tio_bits_letter]
    · simp only [joinSep, List.map_cons] at ih ⊢
      rw [List.intercalate_cons_cons, List.map_append, List.map_append, ih]
      simp [tio_row, List.intercalate_cons_cons, tio_bits_letter, letter]

theorem tio_encIn (rows : List (List Ent)) : (encIn rows).map letter = tio_rowsW rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rcases rs with _ | ⟨r', rs⟩
    · simp [encIn, tio_rowsW, tio_joinSep]
    · simp only [encIn, List.map_cons] at ih ⊢
      rw [List.intercalate_cons_cons, List.map_append, List.map_append, ih, tio_joinSep]
      simp [tio_rowsW, letter]

/-! ## Initialisation -/

theorem tinit_runs (w : List (Option Bool)) :
    Runs st tinit ⟨fun i => if i = 0 then tapeOf S7 (w.map letter) else tapeOf S7 [], fun _ => 0⟩
      5 (T0 w) := by
  refine seq_runs (mv_runs st 5 Move.right _ nofun) <| seq_runs (mv_runs st 0 Move.right _ nofun) <|
    seq_runs (mv_runs st 2 Move.right _ nofun) <| seq_runs (mv_runs st 3 Move.right _ nofun) <|
    (mv_runs st 4 Move.right _ nofun) |>.of_eq ?_ rfl
  simp only [T0]
  congr 1
  funext i; fin_cases i <;> simp [moveHead]

/-! ## Output -/

def tio_term (u : Bool) : Sym7 := if u then runend else rend

def tio_unit (u : Bool) (e : Ent) : List Sym7 := enc e ++ sep :: (if u then [rend] else [])

def tio_word (u : Bool) (e0 : Ent) (rest : List (Bool × Ent)) : List Sym7 :=
  tio_unit u e0 ++ rest.flatMap (fun p => (if p.1 then [tio_term u] else []) ++ tio_unit u p.2)

def tio_out (e0 : Ent) (rest : List (Bool × Ent)) : List Sym7 :=
  enc e0 ++ rest.flatMap (fun p => (if p.1 then [sep, sep] else [sep]) ++ enc p.2)

/-- The facts about tapes `1` and `2` that `outStep` uses. -/
def tio_O (T : Tapes Sym7 6) (c2 : ℕ → Sym7) (h2 : ℕ) (Q : List Sym7) : Prop :=
  T.cells 2 = c2 ∧ T.head 2 = h2 ∧ T.cells 1 = tapeOf S7 Q ∧ T.head 1 = Q.length + 1

theorem tio_enc_bit (e : Ent) : ∀ x ∈ enc e, isBit x = true := by
  intro x hx; simp only [enc, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx; cases b <;> rfl

theorem tio_enc_length (e : Ent) : (enc e).length = e.length := by simp [enc]

theorem tio_O_copy (T : Tapes Sym7 6) (P R Q : List Sym7) (e : Ent)
    (hR : isBit (R.getD 0 blank) = false)
    (hT : tio_O T (tapeOf S7 (P ++ enc e ++ R)) (P.length + 1) Q) :
    ∃ T', Runs st (copy 2 1 isBit id) T e.length T' ∧
      tio_O T' (tapeOf S7 (P ++ enc e ++ R)) (P.length + 1 + e.length) (Q ++ enc e) := by
  obtain ⟨h1, h2, h3, h4⟩ := hT
  have h := copyW_runs 2 1 (by decide) (by decide) isBit rfl T P (enc e) R Q h1 h2
    (tio_enc_bit e) hR h3 h4
  rw [tio_enc_length] at h
  refine ⟨_, h, ?_, ?_, ?_, ?_⟩ <;> simp [h1, tio_enc_length]; omega

theorem tio_O_mv (T : Tapes Sym7 6) (c2 : ℕ → Sym7) (h2 : ℕ) (Q : List Sym7)
    (hT : tio_O T c2 h2 Q) :
    ∃ T', Runs st (mv 2 Move.right) T 1 T' ∧ tio_O T' c2 (h2 + 1) Q := by
  obtain ⟨h1, h2', h3, h4⟩ := hT
  refine ⟨_, mv_runs st 2 Move.right T nofun, ?_, ?_, ?_, ?_⟩ <;> simp [h1, h2', h3, h4, moveHead]

theorem tio_O_mvu (u : Bool) (T : Tapes Sym7 6) (c2 : ℕ → Sym7) (h2 : ℕ) (Q : List Sym7)
    (hT : tio_O T c2 h2 Q) :
    ∃ T', Runs st (if u then mv 2 Move.right else skip) T (if u then 1 else 0) T' ∧
      tio_O T' c2 (h2 + if u then 1 else 0) Q := by
  cases u
  · exact ⟨T, skip_runs T, by simpa using hT⟩
  · simpa using tio_O_mv T c2 h2 Q hT

theorem tio_O_sep (T : Tapes Sym7 6) (c2 : ℕ → Sym7) (h2 : ℕ) (Q : List Sym7)
    (hT : tio_O T c2 h2 Q) :
    ∃ T', Runs st (wsym 1 sep) T 1 T' ∧ tio_O T' c2 h2 (Q ++ [sep]) := by
  obtain ⟨h1, h2', h3, h4⟩ := hT
  refine ⟨_, wsym_runs 1 (by decide) sep (by decide) T Q h3 h4, ?_, ?_, ?_, ?_⟩ <;>
    simp [h1, h2']

theorem tio_O_read (T : Tapes Sym7 6) (c2 : ℕ → Sym7) (h2 : ℕ) (Q : List Sym7)
    (hT : tio_O T c2 h2 Q) : T.read 2 = c2 h2 := by
  obtain ⟨h1, h2', -, -⟩ := hT; simp [Tapes.read, h1, h2']

theorem tio_unit_length (u : Bool) (e : Ent) :
    (tio_unit u e).length = e.length + 1 + if u then 1 else 0 := by
  cases u <;> simp [tio_unit, tio_enc_length]

theorem tio_O_pre (u : Bool) (K : Prog Sym7 6) (T : Tapes Sym7 6) (P X Q : List Sym7) (e : Ent)
    (Φ : ℕ → Tapes Sym7 6 → Prop)
    (hT : tio_O T (tapeOf S7 (P ++ tio_unit u e ++ X)) (P.length + 1) Q)
    (hK : ∀ T3, tio_O T3 (tapeOf S7 (P ++ tio_unit u e ++ X)) (P.length + 1 + (tio_unit u e).length)
      (Q ++ enc e) → ∃ s T', Runs st K T3 s T' ∧ Φ s T') :
    ∃ s T', Runs st (seq (copy 2 1 isBit id) (seq (mv 2 Move.right)
      (seq (if u then mv 2 Move.right else skip) K))) T (e.length + 1 + (if u then 1 else 0) + s) T'
      ∧ Φ s T' := by
  have e1 : P ++ tio_unit u e ++ X = P ++ enc e ++ (sep :: ((if u then [rend] else []) ++ X)) := by
    simp [tio_unit]
  rw [e1] at hT
  obtain ⟨T1, r1, o1⟩ := tio_O_copy T P _ Q e rfl hT
  obtain ⟨T2, r2, o2⟩ := tio_O_mv T1 _ _ _ o1
  obtain ⟨T3, r3, o3⟩ := tio_O_mvu u T2 _ _ _ o2
  rw [← e1] at o3
  have hl : P.length + 1 + e.length + 1 + (if u then 1 else 0) =
      P.length + 1 + (tio_unit u e).length := by rw [tio_unit_length]; omega
  rw [hl] at o3
  obtain ⟨s, T', r4, o4⟩ := hK T3 o3
  exact ⟨s, T', (seq_runs r1 (seq_runs r2 (seq_runs r3 r4))).of_eq rfl (by omega), o4⟩

theorem tio_read_enc (A B : List Sym7) (b : Bool) (e : Ent) :
    tapeOf S7 (A ++ enc (b :: e) ++ B) (A.length + 1) = bs b := by
  have : A ++ enc (b :: e) ++ B = A ++ bs b :: (enc e ++ B) := by simp [enc]
  rw [this, tapeOf_at7]

theorem tio_bs_bit (b : Bool) : isBit (bs b) = true := by cases b <;> rfl

theorem tio_bs_ne (u : Bool) (b : Bool) : bs b ≠ tio_term u := by
  cases u <;> cases b <;> decide

def tio_K (u : Bool) : Prog Sym7 6 :=
  ite (fun a => decide (a 2 = if u then runend else rend))
    (seq (mv 2 Move.right) (ite (fun a => isBit (a 2)) (seq (wsym 1 sep) (wsym 1 sep)) skip))
    (wsym 1 sep)

theorem tio_outStep (u : Bool) : outStep u = seq (copy 2 1 isBit id) (seq (mv 2 Move.right)
    (seq (if u then mv 2 Move.right else skip) (tio_K u))) := rfl

theorem tio_oloop (u : Bool) : ∀ (rest : List (Bool × Ent)) (e0 : Ent) (T : Tapes Sym7 6)
    (P R Q : List Sym7), e0 ≠ [] → (∀ p ∈ rest, p.2 ≠ []) → isBit (R.getD 0 blank) = false →
    tio_O T (tapeOf S7 (P ++ tio_word u e0 rest ++ tio_term u :: R)) (P.length + 1) Q →
    ∃ t ≤ 4 * ((tio_word u e0 rest).length + 1), ∃ T',
      Runs st (loop (fun a => isBit (a 2)) (outStep u)) T t T' ∧
      T'.cells 1 = tapeOf S7 (Q ++ tio_out e0 rest) := by
  intro rest
  induction rest with
  | nil =>
    intro e0 T P R Q he0 _ hR hT
    obtain ⟨b, e, rfl⟩ : ∃ b e, e0 = b :: e := by
      rcases e0 with _ | ⟨b, e⟩
      · exact absurd rfl he0
      · exact ⟨b, e, rfl⟩
    have hw : tio_word u (b :: e) [] = tio_unit u (b :: e) := by simp [tio_word]
    rw [hw] at hT ⊢
    have hc : isBit (T.read 2) = true := by
      rw [tio_O_read T _ _ _ hT]
      simp only [tio_unit, List.append_assoc]
      rw [← List.append_assoc, tio_read_enc]; exact tio_bs_bit b
    obtain ⟨s, T', r, rfl, o1, o2⟩ := tio_O_pre u (tio_K u) T P (tio_term u :: R) Q (b :: e)
      (fun s T' => s = 1 ∧ T'.cells 1 = tapeOf S7 (Q ++ enc (b :: e)) ∧
        isBit (T'.read 2) = false) hT (by
        intro T3 o3
        have rd3 := tio_O_read T3 _ _ _ o3
        rw [show P ++ tio_unit u (b :: e) ++ tio_term u :: R =
          (P ++ tio_unit u (b :: e)) ++ tio_term u :: R by rfl,
          show P.length + 1 + (tio_unit u (b :: e)).length = (P ++ tio_unit u (b :: e)).length + 1
          by simp; omega, tapeOf_at7] at rd3
        obtain ⟨T4, r4, o4⟩ := tio_O_mv T3 _ _ _ o3
        have rd4 := tio_O_read T4 _ _ _ o4
        rw [show P ++ tio_unit u (b :: e) ++ tio_term u :: R =
          (P ++ tio_unit u (b :: e)) ++ [tio_term u] ++ R by simp,
          show P.length + 1 + (tio_unit u (b :: e)).length + 1 =
            (P ++ tio_unit u (b :: e)).length + 1 + [tio_term u].length by simp; omega,
          tapeOf_after7] at rd4
        refine ⟨1, T4, ite_runs_true (by rw [rd3]; cases u <;> rfl) ?_, rfl, o4.2.2.1, ?_⟩
        · exact (seq_runs r4 (ite_runs_false (by rw [rd4]; exact hR) (skip_runs _))).of_eq rfl rfl
        · rw [Tapes.read] at rd4 ⊢; rw [rd4]; exact hR)
    rw [← tio_outStep] at r
    refine ⟨_, ?_, T', loop_iter hc (by omega) r (loop_stop o2), by simpa [tio_out] using o1⟩
    rw [tio_unit_length]; omega
  | cons p rest ih =>
    intro e0 T P R Q he0 hrest hR hT
    obtain ⟨g, e1⟩ := p
    obtain ⟨b, e, rfl⟩ : ∃ b e, e0 = b :: e := by
      rcases e0 with _ | ⟨b, e⟩
      · exact absurd rfl he0
      · exact ⟨b, e, rfl⟩
    have he1 : e1 ≠ [] := hrest (g, e1) (by simp)
    obtain ⟨b1, e1', rfl⟩ : ∃ b e, e1 = b :: e := by
      rcases e1 with _ | ⟨b, e⟩
      · exact absurd rfl he1
      · exact ⟨b, e, rfl⟩
    have hrest' : ∀ p ∈ rest, p.2 ≠ [] := fun p hp => hrest p (by simp [hp])
    have hc : isBit (T.read 2) = true := by
      rw [tio_O_read T _ _ _ hT]
      simp only [tio_word, tio_unit, List.append_assoc]
      rw [← List.append_assoc, tio_read_enc]; exact tio_bs_bit b
    cases g
    · -- same cell
      have hw : tio_word u (b :: e) ((false, b1 :: e1') :: rest) =
          tio_unit u (b :: e) ++ tio_word u (b1 :: e1') rest := by simp [tio_word]
      rw [hw] at hT ⊢
      rw [show P ++ (tio_unit u (b :: e) ++ tio_word u (b1 :: e1') rest) ++ tio_term u :: R =
        P ++ tio_unit u (b :: e) ++ (tio_word u (b1 :: e1') rest ++ tio_term u :: R) by simp] at hT
      obtain ⟨s, T6, r, rfl, o6⟩ := tio_O_pre u (tio_K u) T P _ Q (b :: e)
        (fun s T' => s = 1 ∧ tio_O T' (tapeOf S7 (P ++ tio_unit u (b :: e) ++
          (tio_word u (b1 :: e1') rest ++ tio_term u :: R)))
          ((P ++ tio_unit u (b :: e)).length + 1) (Q ++ enc (b :: e) ++ [sep])) hT (by
          intro T3 o3
          have rd3 := tio_O_read T3 _ _ _ o3
          rw [show P ++ tio_unit u (b :: e) ++ (tio_word u (b1 :: e1') rest ++ tio_term u :: R) =
            (P ++ tio_unit u (b :: e)) ++ enc (b1 :: e1') ++
              ((sep :: if u then [rend] else []) ++
                (rest.flatMap (fun p => (if p.1 then [tio_term u] else []) ++ tio_unit u p.2)) ++
                tio_term u :: R) by simp [tio_word, tio_unit],
            show P.length + 1 + (tio_unit u (b :: e)).length = (P ++ tio_unit u (b :: e)).length + 1
            by simp; omega, tio_read_enc] at rd3
          obtain ⟨T4, r4, o4⟩ := tio_O_sep T3 _ _ _ o3
          refine ⟨1, T4, ite_runs_false (by rw [rd3]; have := tio_bs_ne u b1; cases u <;>
            simpa [tio_term] using this) r4, rfl, ?_⟩
          rw [show (P ++ tio_unit u (b :: e)).length + 1 = P.length + 1 + (tio_unit u (b :: e)).length
            by simp; omega]
          exact o4)
      rw [← tio_outStep] at r
      rw [show P ++ tio_unit u (b :: e) ++ (tio_word u (b1 :: e1') rest ++ tio_term u :: R) =
        (P ++ tio_unit u (b :: e)) ++ tio_word u (b1 :: e1') rest ++ tio_term u :: R by simp] at o6
      obtain ⟨t', ht', T', r', o'⟩ := ih (b1 :: e1') T6 _ R _ (by simp) hrest' hR o6
      refine ⟨_, ?_, T', loop_iter hc (by omega) r r', ?_⟩
      · simp only [List.length_append, tio_unit_length] at ht' ⊢; omega
      · rw [o']; simp [tio_out]
    · -- next cell
      have hw : tio_word u (b :: e) ((true, b1 :: e1') :: rest) =
          tio_unit u (b :: e) ++ tio_term u :: tio_word u (b1 :: e1') rest := by simp [tio_word]
      rw [hw] at hT ⊢
      rw [show P ++ (tio_unit u (b :: e) ++ tio_term u :: tio_word u (b1 :: e1') rest) ++
          tio_term u :: R =
        P ++ tio_unit u (b :: e) ++ (tio_term u :: tio_word u (b1 :: e1') rest ++ tio_term u :: R)
        by simp] at hT
      obtain ⟨s, T6, r, rfl, o6⟩ := tio_O_pre u (tio_K u) T P _ Q (b :: e)
        (fun s T' => s = 3 ∧ tio_O T' (tapeOf S7 (P ++ tio_unit u (b :: e) ++
          (tio_term u :: tio_word u (b1 :: e1') rest ++ tio_term u :: R)))
          ((P ++ tio_unit u (b :: e) ++ [tio_term u]).length + 1)
          (Q ++ enc (b :: e) ++ [sep] ++ [sep])) hT (by
          intro T3 o3
          have rd3 := tio_O_read T3 _ _ _ o3
          rw [show P ++ tio_unit u (b :: e) ++
              (tio_term u :: tio_word u (b1 :: e1') rest ++ tio_term u :: R) =
            (P ++ tio_unit u (b :: e)) ++ tio_term u :: (tio_word u (b1 :: e1') rest ++
              tio_term u :: R) by simp,
            show P.length + 1 + (tio_unit u (b :: e)).length = (P ++ tio_unit u (b :: e)).length + 1
            by simp; omega, tapeOf_at7] at rd3
          obtain ⟨T4, r4, o4⟩ := tio_O_mv T3 _ _ _ o3
          have rd4 := tio_O_read T4 _ _ _ o4
          rw [show P ++ tio_unit u (b :: e) ++
              (tio_term u :: tio_word u (b1 :: e1') rest ++ tio_term u :: R) =
            (P ++ tio_unit u (b :: e) ++ [tio_term u]) ++ enc (b1 :: e1') ++
              ((sep :: if u then [rend] else []) ++
                (rest.flatMap (fun p => (if p.1 then [tio_term u] else []) ++ tio_unit u p.2)) ++
                tio_term u :: R) by simp [tio_word, tio_unit],
            show P.length + 1 + (tio_unit u (b :: e)).length + 1 =
              (P ++ tio_unit u (b :: e) ++ [tio_term u]).length + 1 by simp; omega, tio_read_enc] at rd4
          obtain ⟨T5, r5, o5⟩ := tio_O_sep T4 _ _ _ o4
          obtain ⟨T6, r6, o6⟩ := tio_O_sep T5 _ _ _ o5
          refine ⟨3, T6, ite_runs_true (by rw [rd3]; cases u <;> rfl)
            (seq_runs r4 (ite_runs_true (by rw [rd4]; exact tio_bs_bit b1) (seq_runs r5 r6))), rfl,
            ?_⟩
          rw [show (P ++ tio_unit u (b :: e) ++ [tio_term u]).length + 1 =
            P.length + 1 + (tio_unit u (b :: e)).length + 1 by simp; omega]
          exact o6)
      rw [← tio_outStep] at r
      rw [show P ++ tio_unit u (b :: e) ++
          (tio_term u :: tio_word u (b1 :: e1') rest ++ tio_term u :: R) =
        (P ++ tio_unit u (b :: e) ++ [tio_term u]) ++ tio_word u (b1 :: e1') rest ++ tio_term u :: R
        by simp] at o6
      obtain ⟨t', ht', T', r', o'⟩ := ih (b1 :: e1') T6 _ R _ (by simp) hrest' hR o6
      refine ⟨_, ?_, T', loop_iter hc (by omega) r r', ?_⟩
      · simp only [List.length_append, List.length_cons, tio_unit_length] at ht' ⊢; omega
      · rw [o']; simp [tio_out]

theorem tio_cell (u : Bool) (e : Ent) (es : List Ent) :
    (e :: es).flatMap (tio_unit u) = tio_word u e (es.map fun e' => (false, e')) ∧
      tio_row (e :: es) = tio_out e (es.map fun e' => (false, e')) := by
  refine ⟨?_, ?_⟩
  · simp [tio_word, List.flatMap_map]
  · rw [tio_row_cons]; simp [tio_out, List.flatMap_map]

theorem tio_cells (u : Bool) : ∀ xs : List (List Ent), xs ≠ [] →
    (∀ c ∈ xs, c ≠ [] ∧ ∀ e ∈ c, e ≠ []) → ∃ e0 rest, e0 ≠ [] ∧ (∀ p ∈ rest, p.2 ≠ []) ∧
      xs.flatMap (fun c => c.flatMap (tio_unit u) ++ [tio_term u]) =
        tio_word u e0 rest ++ [tio_term u] ∧ tio_rowsW xs = tio_out e0 rest
  | [], h, _ => absurd rfl h
  | [c], _, hc => by
    obtain ⟨hc0, hce⟩ := hc c (by simp)
    obtain ⟨e, es, rfl⟩ : ∃ e es, c = e :: es := by
      rcases c with _ | ⟨e, es⟩
      · exact absurd rfl hc0
      · exact ⟨e, es, rfl⟩
    obtain ⟨h1, h2⟩ := tio_cell u e es
    refine ⟨e, es.map fun e' => (false, e'), hce e (by simp), ?_, ?_, ?_⟩
    · intro p hp; simp only [List.mem_map] at hp
      obtain ⟨e', he', rfl⟩ := hp; exact hce e' (by simp [he'])
    · simp [h1]
    · simp [tio_rowsW, h2]
  | c :: c' :: xs, _, hc => by
    obtain ⟨e1, rest1, he1, hr1, hw1, ho1⟩ := tio_cells u (c' :: xs) (by simp)
      (fun d hd => hc d (by simp_all))
    obtain ⟨hc0, hce⟩ := hc c (by simp)
    obtain ⟨e, es, rfl⟩ : ∃ e es, c = e :: es := by
      rcases c with _ | ⟨e, es⟩
      · exact absurd rfl hc0
      · exact ⟨e, es, rfl⟩
    obtain ⟨h1, h2⟩ := tio_cell u e es
    refine ⟨e, es.map (fun e' => (false, e')) ++ (true, e1) :: rest1, hce e (by simp), ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_append, List.mem_map, List.mem_cons] at hp
      rcases hp with ⟨e', he', rfl⟩ | rfl | hp
      · exact hce e' (by simp [he'])
      · exact he1
      · exact hr1 p hp
    · rw [List.flatMap_cons, hw1, h1]
      simp [tio_word]
    · rw [show tio_rowsW ((e :: es) :: c' :: xs) = tio_row (e :: es) ++ sep :: sep :: tio_rowsW (c' :: xs)
        from rfl, ho1, h2]
      simp [tio_out]

theorem tio_encBs_ne_st (bs : List (List (List Ent))) : ∀ x ∈ encBs bs, x ≠ st := by
  intro x hx
  simp only [encBs, encB, encC, encE, List.mem_flatMap, List.mem_append, List.mem_singleton] at hx
  obtain ⟨_, _, ⟨_, _, ⟨e, _, h | rfl⟩ | rfl⟩ | rfl⟩ := hx
  · exact enc_ne_st e x h
  all_goals decide

theorem tio_getD_nb (R : List Sym7) (h : ∀ x ∈ R, isBit x = false) :
    isBit (R.getD 0 blank) = false := by
  rcases R with _ | ⟨x, R⟩
  · rfl
  · exact h x (by simp)

theorem toutput_false_runs (b : List (List Ent)) (hb : b ≠ []) (hc : ∀ c ∈ b, c ≠ [])
    (he : ∀ c ∈ b, ∀ e ∈ c, e ≠ []) (T : Tapes Sym7 6) (hc2 : T.cells 2 = tapeOf S7 (encB b))
    (hc1 : T.cells 1 = tapeOf S7 []) (hh1 : T.head 1 = 0) :
    ∃ t ≤ T.head 2 + 6 * ((encB b).length + 1), ∃ T',
      Runs st (toutput false) T t T' ∧ T'.cells 1 = tapeOf S7 ((encIn b).map letter) := by
  obtain ⟨e0, rest, he0, hrest, hw, ho⟩ := tio_cells false b hb (fun c h => ⟨hc c h, he c h⟩)
  have hB : encB b = tio_word false e0 rest ++ [rend, runend] := by
    rw [show [rend, runend] = [tio_term false] ++ [runend] from rfl, ← List.append_assoc, ← hw]
    have hu : tio_unit false = encE := by funext e; simp [encE, tio_unit]
    have hC : encC = fun c => c.flatMap encE ++ [rend] := by funext c; rfl
    simp [encB, hC, hu, tio_term]
  have h1 := rewind_runs 2 T (encB b) (fun x hx => tio_encBs_ne_st [b] x (by simpa [encBs] using hx))
    hc2
  have h2 := mv_runs st 1 Move.right ⟨T.cells, Function.update T.head 2 1⟩ nofun
  obtain ⟨t, ht, T', h3, hT'⟩ := tio_oloop false rest e0
    ⟨T.cells, Function.update (Function.update T.head 2 1) 1 (moveHead Move.right (Function.update T.head 2 1 1))⟩
    [] [runend] [] he0 hrest rfl
    ⟨by simp [hc2, hB, tio_term], by simp, by simp [hc1], by simp [moveHead, hh1]⟩
  refine ⟨_, ?_, T', seq_runs h1 (seq_runs h2 h3), ?_⟩
  · rw [hB]; simp only [List.length_append, List.length_cons, List.length_nil] at ht ⊢; omega
  · rw [hT', tio_encIn, ho]; simp

theorem toutput_true_runs (cs : List (List Ent)) (m z : ℕ) (hcs : cs ≠ [])
    (hc : ∀ c ∈ cs, c ≠ [] ∧ ∀ e ∈ c, e ≠ []) (T : Tapes Sym7 6)
    (hc2 : T.cells 2 = tapeOf S7
      (encBs (cs.map (fun c => c.map fun e => [e]) ++ List.replicate z (List.replicate m []))))
    (hc1 : T.cells 1 = tapeOf S7 []) (hh1 : T.head 1 = 0) :
    ∃ t ≤ T.head 2 + 6 * ((encBs (cs.map (fun c => c.map fun e => [e]) ++
        List.replicate z (List.replicate m []))).length + 1), ∃ T',
      Runs st (toutput true) T t T' ∧ T'.cells 1 = tapeOf S7 ((encIn cs).map letter) := by
  obtain ⟨e0, rest, he0, hrest, hw, ho⟩ := tio_cells true cs hcs hc
  have hB : encBs (cs.map (fun c => c.map fun e => [e]) ++ List.replicate z (List.replicate m [])) =
      tio_word true e0 rest ++ runend :: encBs (List.replicate z (List.replicate m [])) := by
    rw [show tio_word true e0 rest ++ runend :: encBs (List.replicate z (List.replicate m [])) =
      (tio_word true e0 rest ++ [tio_term true]) ++ encBs (List.replicate z (List.replicate m []))
      by simp [tio_term], ← hw]
    have hu : tio_unit true = fun e => enc e ++ [sep, rend] := by funext e; simp [tio_unit]
    simp [encBs, encB, encC, encE, hu, tio_term, List.flatMap_map]
  have hZ : ∀ x ∈ encBs (List.replicate z (List.replicate m ([] : List Ent))), isBit x = false := by
    intro x hx
    simp only [encBs, encB, encC, List.mem_flatMap, List.mem_append, List.mem_singleton,
      List.mem_replicate] at hx
    obtain ⟨b, ⟨-, rfl⟩, hb⟩ := hx
    simp only [List.mem_replicate] at hb
    rcases hb with ⟨c, ⟨-, rfl⟩, h | h⟩ | h
    · simp at h
    all_goals (subst h; rfl)
  have h1 := rewind_runs 2 T _ (tio_encBs_ne_st _) hc2
  have h2 := mv_runs st 1 Move.right ⟨T.cells, Function.update T.head 2 1⟩ nofun
  obtain ⟨t, ht, T', h3, hT'⟩ := tio_oloop true rest e0
    ⟨T.cells, Function.update (Function.update T.head 2 1) 1 (moveHead Move.right (Function.update T.head 2 1 1))⟩
    [] _ [] he0 hrest (tio_getD_nb _ hZ)
    ⟨by simp [hc2, hB, tio_term], by simp, by simp [hc1], by simp [moveHead, hh1]⟩
  refine ⟨_, ?_, T', seq_runs h1 (seq_runs h2 h3), ?_⟩
  · rw [hB]; simp only [List.length_append, List.length_cons] at ht ⊢; omega
  · rw [hT', tio_encIn, ho]; simp

/-! ## Deciding between riffle and unriffle -/

theorem tio_at (A B : List Sym7) (x : Sym7) (n : ℕ) (h : n = A.length + 1) :
    tapeOf S7 (A ++ x :: B) n = x := by subst h; exact tapeOf_at7 A B x

theorem tio_scan0 (T : Tapes Sym7 6) (P R : List Sym7) (e : Ent)
    (hc : T.cells 0 = tapeOf S7 (P ++ enc e ++ R)) (hh : T.head 0 = P.length + 1)
    (hR : isBit (R.getD 0 blank) = false) :
    Runs st (scanR 0 isBit) T e.length ⟨T.cells, Function.update T.head 0 (P.length + 1 + e.length)⟩ := by
  have h := scanR_runs st 0 isBit e.length T
    (fun p hp => by
      rw [hc, hh, tapeOf_mid7 P (enc e) R p (by rw [tio_enc_length]; exact hp)]
      exact tio_enc_bit e _ (List.getElem_mem _))
    (by rw [hc, hh, ← tio_enc_length, tapeOf_after7]; exact hR)
  rw [hh] at h; exact h

theorem tio_skip_sep (T : Tapes Sym7 6) (h : T.cells 0 (T.head 0) = sep) :
    Runs st (skipIf 0 sep) T 1 ⟨T.cells, Function.update T.head 0 (T.head 0 + 1)⟩ :=
  ite_runs_true (by simp [Tapes.read, h]) (mv_runs st 0 Move.right T nofun)

theorem tio_skip_no (T : Tapes Sym7 6) (h : T.cells 0 (T.head 0) ≠ sep) :
    Runs st (skipIf 0 sep) T 0 T :=
  ite_runs_false (by simp [Tapes.read, h]) (skip_runs T)

theorem tio_row_cc (e e' : Ent) (r : List Ent) :
    tio_row (e :: e' :: r) = enc e ++ sep :: tio_row (e' :: r) := by
  simp [tio_row, List.intercalate_cons_cons]

theorem tio_row_len (r : List Ent) (hr : r ≠ []) (he : ∀ e ∈ r, e ≠ []) :
    r.length ≤ (tio_row r).length ∧ 1 ≤ (tio_row r).length := by
  induction r with
  | nil => exact absurd rfl hr
  | cons e r ih =>
    have he0 : 1 ≤ e.length := List.length_pos_iff.mpr (he e (by simp))
    rcases r with _ | ⟨e', r⟩
    · simp [tio_row, tio_enc_length]; omega
    · have := ih (by simp) (fun x hx => he x (by simp_all))
      rw [tio_row_cc]; simp only [List.length_append, List.length_cons, tio_enc_length] at this ⊢
      omega

theorem tio_marks : ∀ (r : List Ent) (T : Tapes Sym7 6) (P R Q : List Sym7), r ≠ [] →
    (∀ e ∈ r, e ≠ []) → (R = [] ∨ ∃ R', R = sep :: sep :: R') →
    T.cells 0 = tapeOf S7 (P ++ tio_row r ++ R) → T.head 0 = P.length + 1 →
    T.cells 3 = tapeOf S7 Q → T.head 3 = Q.length + 1 →
    ∃ t ≤ 3 * (tio_row r).length, Runs st (rowMarks 3) T t
      ⟨Function.update T.cells 3 (tapeOf S7 (Q ++ List.replicate r.length one)),
        Function.update (Function.update T.head 0
          (P.length + 1 + (tio_row r).length + if R = [] then 0 else 1)) 3 (Q.length + 1 + r.length)⟩
  | [], _, _, _, _, h, _, _, _, _, _, _ => absurd rfl h
  | [e], T, P, R, Q, _, he, hR, hc0, hh0, hc3, hh3 => by
    have he0 : e ≠ [] := he e (by simp)
    have hel : 1 ≤ e.length := List.length_pos_iff.mpr he0
    have hrow : tio_row [e] = enc e := by simp [tio_row]
    rw [hrow] at hc0 ⊢
    have hRb : isBit (R.getD 0 blank) = false := by rcases hR with rfl | ⟨R', rfl⟩ <;> rfl
    have h1 := tio_scan0 T P R e hc0 hh0 hRb
    have h2 := wsym_runs 3 (by decide) one (by decide)
      ⟨T.cells, Function.update T.head 0 (P.length + 1 + e.length)⟩ Q hc3 (by simp [hh3])
    obtain ⟨b, e', rfl⟩ : ∃ b e', e = b :: e' := by
      rcases e with _ | ⟨b, e'⟩
      · exact absurd rfl he0
      · exact ⟨b, e', rfl⟩
    have hc : isBit (T.read 0) = true := by
      simp only [Tapes.read, hc0, hh0, tio_read_enc, tio_bs_bit]
    rcases hR with rfl | ⟨R', rfl⟩
    · have h3 := tio_skip_no (⟨Function.update T.cells 3 (tapeOf S7 (Q ++ [one])),
        Function.update (Function.update T.head 0 (P.length + 1 + (b :: e').length)) 3 (Q.length + 2)⟩ :
        Tapes Sym7 6) (by
        simp only [Function.update_apply, show (0 : Fin 6) ≠ 3 by decide, if_false, if_true, hc0]
        rw [← tio_enc_length, tapeOf_after7]; decide)
      have hl := loop_iter (c := fun a => isBit (a 0)) hc (by omega) (seq_runs h1 (seq_runs h2 h3))
        (loop_stop (by
          simp only [Tapes.read, Function.update_apply, show (0 : Fin 6) ≠ 3 by decide, if_false,
            if_true, hc0]
          rw [← tio_enc_length, tapeOf_after7]; rfl))
      refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
      · rw [tio_enc_length]; omega
      · simp only [List.length_singleton, List.replicate_one, tio_enc_length, if_true]
        congr 1
    · have h3 := tio_skip_sep (⟨Function.update T.cells 3 (tapeOf S7 (Q ++ [one])),
        Function.update (Function.update T.head 0 (P.length + 1 + (b :: e').length)) 3 (Q.length + 2)⟩ :
        Tapes Sym7 6) (by
        simp only [Function.update_apply, show (0 : Fin 6) ≠ 3 by decide, if_false, if_true, hc0]
        rw [← tio_enc_length, tapeOf_after7]; rfl)
      have hl := loop_iter (c := fun a => isBit (a 0)) hc (by omega) (seq_runs h1 (seq_runs h2 h3))
        (loop_stop (by
          simp only [Tapes.read, Function.update_apply, show (0 : Fin 6) ≠ 3 by decide, if_false,
            if_true, hc0]
          rw [show P ++ enc (b :: e') ++ sep :: sep :: R' = (P ++ enc (b :: e') ++ [sep]) ++ sep :: R'
            by simp, tio_at _ _ _ _ (by simp [tio_enc_length]; omega)]; rfl))
      refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
      · rw [tio_enc_length]; omega
      · simp only [List.length_singleton, List.replicate_one, tio_enc_length, reduceCtorEq, if_false]
        congr 1; funext i; fin_cases i <;> simp
  | e :: e' :: r, T, P, R, Q, _, he, hR, hc0, hh0, hc3, hh3 => by
    have he0 : e ≠ [] := he e (by simp)
    have hel : 1 ≤ e.length := List.length_pos_iff.mpr he0
    rw [tio_row_cc] at hc0 ⊢
    have h1 := tio_scan0 T P (sep :: tio_row (e' :: r) ++ R) e (by rw [hc0]; simp) hh0 rfl
    have h2 := wsym_runs 3 (by decide) one (by decide)
      ⟨T.cells, Function.update T.head 0 (P.length + 1 + e.length)⟩ Q hc3 (by simp [hh3])
    have h3 := tio_skip_sep (⟨Function.update T.cells 3 (tapeOf S7 (Q ++ [one])),
        Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 3 (Q.length + 2)⟩ :
        Tapes Sym7 6) (by
        simp only [Function.update_apply, show (0 : Fin 6) ≠ 3 by decide, if_false, if_true, hc0]
        rw [show P ++ (enc e ++ sep :: tio_row (e' :: r)) ++ R =
          P ++ enc e ++ sep :: (tio_row (e' :: r) ++ R) by simp,
          tio_at _ _ _ _ (by simp [tio_enc_length]; omega)])
    obtain ⟨b, e'', rfl⟩ : ∃ b e', e = b :: e' := by
      rcases e with _ | ⟨b, e'⟩
      · exact absurd rfl he0
      · exact ⟨b, e', rfl⟩
    have hc : isBit (T.read 0) = true := by
      simp only [Tapes.read, hc0, hh0]
      rw [show P ++ (enc (b :: e'') ++ sep :: tio_row (e' :: r)) ++ R =
        P ++ enc (b :: e'') ++ (sep :: tio_row (e' :: r) ++ R) by simp, tio_read_enc]
      exact tio_bs_bit b
    obtain ⟨t', ht', hr⟩ := tio_marks (e' :: r)
      ⟨Function.update T.cells 3 (tapeOf S7 (Q ++ [one])), Function.update (Function.update
        (Function.update T.head 0 (P.length + 1 + (b :: e'').length)) 3 (Q.length + 2)) 0
        (P.length + 1 + (b :: e'').length + 1)⟩ (P ++ enc (b :: e'') ++ [sep]) R (Q ++ [one])
      (by simp) (fun x hx => he x (by simp_all)) hR
      (by simp [hc0]) (by simp [tio_enc_length]; omega) (by simp) (by simp)
    have hl := loop_iter (c := fun a => isBit (a 0)) hc (by omega) (seq_runs h1 (seq_runs h2 h3)) hr
    refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
    · simp only [List.length_append, List.length_cons, tio_enc_length] at ht' ⊢; omega
    · simp only [List.length_append, List.length_cons, List.length_nil, tio_enc_length,
        List.replicate_succ, List.append_assoc, List.singleton_append]
      congr 1
      · funext i; fin_cases i <;> simp
      · funext i; fin_cases i <;> simp <;> omega

def tio_inner : Prog Sym7 6 := loop (fun a => isBit (a 0)) (seq (scanR 0 isBit) (skipIf 0 sep))

theorem tio_skiprow : ∀ (r : List Ent) (T : Tapes Sym7 6) (P R : List Sym7), r ≠ [] →
    (∀ e ∈ r, e ≠ []) → (R = [] ∨ ∃ R', R = sep :: sep :: R') →
    T.cells 0 = tapeOf S7 (P ++ tio_row r ++ R) → T.head 0 = P.length + 1 →
    ∃ t ≤ 3 * (tio_row r).length, Runs st tio_inner T t
      ⟨T.cells, Function.update T.head 0
          (P.length + 1 + (tio_row r).length + if R = [] then 0 else 1)⟩
  | [], _, _, _, h, _, _, _, _ => absurd rfl h
  | [e], T, P, R, _, he, hR, hc0, hh0 => by
    have he0 : e ≠ [] := he e (by simp)
    have hel : 1 ≤ e.length := List.length_pos_iff.mpr he0
    have hrow : tio_row [e] = enc e := by simp [tio_row]
    rw [hrow] at hc0 ⊢
    have hRb : isBit (R.getD 0 blank) = false := by rcases hR with rfl | ⟨R', rfl⟩ <;> rfl
    have h1 := tio_scan0 T P R e hc0 hh0 hRb
    obtain ⟨b, e', rfl⟩ : ∃ b e', e = b :: e' := by
      rcases e with _ | ⟨b, e'⟩
      · exact absurd rfl he0
      · exact ⟨b, e', rfl⟩
    have hc : isBit (T.read 0) = true := by
      simp only [Tapes.read, hc0, hh0, tio_read_enc, tio_bs_bit]
    rcases hR with rfl | ⟨R', rfl⟩
    · have h3 := tio_skip_no (⟨T.cells, Function.update T.head 0 (P.length + 1 + (b :: e').length)⟩ :
          Tapes Sym7 6) (by
        simp only [Function.update_self, hc0]
        rw [← tio_enc_length, tapeOf_after7]; decide)
      have hl := loop_iter (c := fun a => isBit (a 0)) hc (by omega) (seq_runs h1 h3)
        (loop_stop (by
          simp only [Tapes.read, Function.update_self, hc0]
          rw [← tio_enc_length, tapeOf_after7]; rfl))
      refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
      · rw [tio_enc_length]; omega
      · simp only [tio_enc_length, if_true]; rfl
    · have h3 := tio_skip_sep (⟨T.cells, Function.update T.head 0 (P.length + 1 + (b :: e').length)⟩ :
          Tapes Sym7 6) (by
        simp only [Function.update_self, hc0]
        rw [← tio_enc_length, tapeOf_after7]; rfl)
      have hl := loop_iter (c := fun a => isBit (a 0)) hc (by omega) (seq_runs h1 h3)
        (loop_stop (by
          simp only [Tapes.read, Function.update_self, hc0]
          rw [show P ++ enc (b :: e') ++ sep :: sep :: R' = (P ++ enc (b :: e') ++ [sep]) ++ sep :: R'
            by simp, tio_at _ _ _ _ (by simp [tio_enc_length]; omega)]; rfl))
      refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
      · rw [tio_enc_length]; omega
      · simp only [tio_enc_length, reduceCtorEq, if_false, Function.update_idem, Function.update_self]
  | e :: e' :: r, T, P, R, _, he, hR, hc0, hh0 => by
    have he0 : e ≠ [] := he e (by simp)
    have hel : 1 ≤ e.length := List.length_pos_iff.mpr he0
    rw [tio_row_cc] at hc0 ⊢
    have h1 := tio_scan0 T P (sep :: tio_row (e' :: r) ++ R) e (by rw [hc0]; simp) hh0 rfl
    have h3 := tio_skip_sep (⟨T.cells, Function.update T.head 0 (P.length + 1 + e.length)⟩ :
          Tapes Sym7 6) (by
        simp only [Function.update_self, hc0]
        rw [show P ++ (enc e ++ sep :: tio_row (e' :: r)) ++ R =
          P ++ enc e ++ sep :: (tio_row (e' :: r) ++ R) by simp,
          tio_at _ _ _ _ (by simp [tio_enc_length]; omega)])
    obtain ⟨b, e'', rfl⟩ : ∃ b e', e = b :: e' := by
      rcases e with _ | ⟨b, e'⟩
      · exact absurd rfl he0
      · exact ⟨b, e', rfl⟩
    have hc : isBit (T.read 0) = true := by
      simp only [Tapes.read, hc0, hh0]
      rw [show P ++ (enc (b :: e'') ++ sep :: tio_row (e' :: r)) ++ R =
        P ++ enc (b :: e'') ++ (sep :: tio_row (e' :: r) ++ R) by simp, tio_read_enc]
      exact tio_bs_bit b
    obtain ⟨t', ht', hr⟩ := tio_skiprow (e' :: r)
      ⟨T.cells, Function.update (Function.update T.head 0 (P.length + 1 + (b :: e'').length)) 0
        (P.length + 1 + (b :: e'').length + 1)⟩ (P ++ enc (b :: e'') ++ [sep]) R
      (by simp) (fun x hx => he x (by simp_all)) hR
      (by simp [hc0]) (by simp [tio_enc_length]; omega)
    have hl := loop_iter (c := fun a => isBit (a 0)) hc (by omega) (seq_runs h1 h3) hr
    refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
    · simp only [List.length_append, List.length_cons, tio_enc_length] at ht' ⊢; omega
    · simp only [List.length_append, List.length_cons, List.length_nil, tio_enc_length,
        Function.update_idem]
      congr 2; omega

def tio_outer : Prog Sym7 6 :=
  loop (fun a => decide (a 0 ≠ blank)) (seq (wsym 4 one) (seq tio_inner (skipIf 0 sep)))

theorem tio_row_first (r : List Ent) (hr : r ≠ []) (he : ∀ e ∈ r, e ≠ []) :
    ∃ b X, tio_row r = bs b :: X := by
  obtain ⟨e, es, rfl⟩ : ∃ e es, r = e :: es := by
    rcases r with _ | ⟨e, es⟩
    · exact absurd rfl hr
    · exact ⟨e, es, rfl⟩
  obtain ⟨b, e', rfl⟩ : ∃ b e', e = b :: e' := by
    rcases e with _ | ⟨b, e'⟩
    · exact absurd rfl (he [] (by simp))
    · exact ⟨b, e', rfl⟩
  rw [tio_row_cons]
  exact ⟨b, enc e' ++ es.flatMap (fun e' => sep :: enc e'), by simp [enc]⟩

theorem tio_rowsl : ∀ (rows : List (List Ent)) (T : Tapes Sym7 6) (P Q : List Sym7), rows ≠ [] →
    (∀ r ∈ rows, r ≠ [] ∧ ∀ e ∈ r, e ≠ []) →
    T.cells 0 = tapeOf S7 (P ++ tio_rowsW rows) → T.head 0 = P.length + 1 →
    T.cells 4 = tapeOf S7 Q → T.head 4 = Q.length + 1 →
    ∃ t ≤ 5 * (tio_rowsW rows).length, Runs st tio_outer T t
      ⟨Function.update T.cells 4 (tapeOf S7 (Q ++ List.replicate rows.length one)),
        Function.update (Function.update T.head 0 (P.length + 1 + (tio_rowsW rows).length)) 4
          (Q.length + 1 + rows.length)⟩
  | [], _, _, _, h, _, _, _, _, _ => absurd rfl h
  | [r], T, P, Q, _, hr, hc0, hh0, hc4, hh4 => by
    obtain ⟨hr0, hre⟩ := hr r (by simp)
    have hlen := (tio_row_len r hr0 hre).2
    have hW : tio_rowsW [r] = tio_row r := rfl
    rw [hW] at hc0 ⊢
    obtain ⟨b, X, hbX⟩ := tio_row_first r hr0 hre
    have hc : decide (T.read 0 ≠ blank) = true := by
      simp only [Tapes.read, hc0, hh0, hbX]
      rw [tio_at _ _ _ _ rfl]; cases b <;> decide
    have h1 := wsym_runs 4 (by decide) one (by decide) T Q hc4 hh4
    obtain ⟨t2, ht2, h2⟩ := tio_skiprow r
      ⟨Function.update T.cells 4 (tapeOf S7 (Q ++ [one])), Function.update T.head 4 (Q.length + 2)⟩
      P [] hr0 hre (Or.inl rfl) (by simp [hc0]) (by simp [hh0])
    simp only [if_true, Nat.add_zero] at h2
    have hend : tapeOf S7 (P ++ tio_row r) (P.length + 1 + (tio_row r).length) = blank := by
      rw [show P.length + 1 + (tio_row r).length = (P ++ tio_row r).length + 1 by simp; omega,
        tapeOf_end7]
    have h3 := tio_skip_no (⟨Function.update T.cells 4 (tapeOf S7 (Q ++ [one])), Function.update
      (Function.update T.head 4 (Q.length + 2)) 0 (P.length + 1 + (tio_row r).length)⟩ :
        Tapes Sym7 6) (by simp [hc0, hend])
    have hl := loop_iter (c := fun a => decide (a 0 ≠ blank)) hc (by omega)
      (seq_runs h1 (seq_runs h2 h3)) (loop_stop (by simp [Tapes.read, hc0, hend]))
    refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
    · omega
    · simp only [List.length_singleton, List.replicate_one]
      congr 1; funext i; fin_cases i <;> simp
  | r :: r' :: rs, T, P, Q, _, hr, hc0, hh0, hc4, hh4 => by
    obtain ⟨hr0, hre⟩ := hr r (by simp)
    have hlen := (tio_row_len r hr0 hre).2
    have hW : tio_rowsW (r :: r' :: rs) = tio_row r ++ sep :: sep :: tio_rowsW (r' :: rs) := rfl
    rw [hW] at hc0 ⊢
    obtain ⟨b, X, hbX⟩ := tio_row_first r hr0 hre
    have hc : decide (T.read 0 ≠ blank) = true := by
      simp only [Tapes.read, hc0, hh0, hbX]
      rw [List.cons_append, tio_at _ _ _ _ rfl]; cases b <;> decide
    have h1 := wsym_runs 4 (by decide) one (by decide) T Q hc4 hh4
    obtain ⟨t2, ht2, h2⟩ := tio_skiprow r
      ⟨Function.update T.cells 4 (tapeOf S7 (Q ++ [one])), Function.update T.head 4 (Q.length + 2)⟩
      P (sep :: sep :: tio_rowsW (r' :: rs)) hr0 hre (Or.inr ⟨_, rfl⟩) (by simp [hc0]) (by simp [hh0])
    simp only [reduceCtorEq, if_false] at h2
    have hsep : tapeOf S7 (P ++ tio_row r ++ sep :: sep :: tio_rowsW (r' :: rs))
        (P.length + 1 + (tio_row r).length + 1) = sep := by
      rw [show P ++ tio_row r ++ sep :: sep :: tio_rowsW (r' :: rs) =
        (P ++ tio_row r ++ [sep]) ++ sep :: tio_rowsW (r' :: rs) by simp]
      exact tio_at _ _ _ _ (by simp; omega)
    have h3 := tio_skip_sep (⟨Function.update T.cells 4 (tapeOf S7 (Q ++ [one])), Function.update
      (Function.update T.head 4 (Q.length + 2)) 0 (P.length + 1 + (tio_row r).length + 1)⟩ :
        Tapes Sym7 6) (by simp [hc0]; rw [← List.append_assoc]; exact hsep)
    obtain ⟨t', ht', hr'⟩ := tio_rowsl (r' :: rs)
      ⟨Function.update T.cells 4 (tapeOf S7 (Q ++ [one])), Function.update (Function.update
        (Function.update T.head 4 (Q.length + 2)) 0 (P.length + 1 + (tio_row r).length + 1)) 0
        (P.length + 1 + (tio_row r).length + 1 + 1)⟩
      (P ++ tio_row r ++ [sep, sep]) (Q ++ [one]) (by simp) (fun x hx => hr x (by simp_all))
      (by simp [hc0]) (by simp; omega) (by simp) (by simp)
    have hl := loop_iter (c := fun a => decide (a 0 ≠ blank)) hc (by omega)
      (seq_runs h1 (seq_runs h2 h3)) hr'
    refine ⟨_, ?_, hl.of_eq ?_ rfl⟩
    · simp only [List.length_append, List.length_cons] at ht' ⊢; omega
    · simp only [List.length_append, List.length_cons, List.length_nil, List.replicate_succ,
        List.append_assoc, List.singleton_append]
      congr 1
      · funext i; fin_cases i <;> simp
      · funext i; fin_cases i <;> simp <;> omega

theorem tio_rep (k p : ℕ) :
    tapeOf S7 (List.replicate k one) (p + 1) = if p < k then one else blank := by
  rw [tapeOf_succ]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]; rfl

def tio_cmpP : Prog Sym7 6 :=
  loop (fun a => decide (a 3 ≠ blank) && decide (a 4 ≠ blank))
    (act (fun a => wr2 a 3 (a 3) Move.right 4 (a 4) Move.right))

theorem tio_cmp (k m : ℕ) : ∀ n (T : Tapes Sym7 6), T.cells 3 = tapeOf S7 (List.replicate k one) →
    T.cells 4 = tapeOf S7 (List.replicate m one) → T.head 3 = T.head 4 → 1 ≤ T.head 3 →
    T.head 3 + n = min k m + 1 →
    Runs st tio_cmpP T n
      ⟨T.cells, Function.update (Function.update T.head 3 (min k m + 1)) 4 (min k m + 1)⟩
  | 0, T, h3, h4, hh, h1, hn => by
    obtain ⟨p, hp⟩ : ∃ p, T.head 3 = p + 1 := ⟨T.head 3 - 1, by omega⟩
    have e : Function.update (Function.update T.head 3 (min k m + 1)) 4 (min k m + 1) = T.head := by
      funext i; simp only [Function.update_apply]; split_ifs with h4' h3' <;> subst_vars <;> omega
    rw [e]
    refine loop_stop ?_
    simp only [Tapes.read, h3, h4, ← hh, hp, tio_rep]
    by_cases hk : p < k <;> by_cases hm : p < m <;> simp [hk, hm] <;> omega
  | n + 1, T, h3, h4, hh, h1, hn => by
    obtain ⟨p, hp⟩ : ∃ p, T.head 3 = p + 1 := ⟨T.head 3 - 1, by omega⟩
    have hr3 : T.cells 3 (T.head 3) = one := by rw [h3, hp, tio_rep, if_pos (by omega)]
    have hr4 : T.cells 4 (T.head 4) = one := by rw [h4, ← hh, hp, tio_rep, if_pos (by omega)]
    have ha := act_runs (st := st) (fun a => wr2 a 3 (a 3) Move.right 4 (a 4) Move.right) T
    rw [fix_wr2 _ _ _ _ _ _ _ (by decide) (Or.inl ⟨rfl, by simp⟩) (Or.inl ⟨rfl, by simp⟩),
      write_wr2 _ _ _ _ _ _ _ (by decide)] at ha
    simp only [Tapes.read, Function.update_eq_self, moveHead] at ha
    have hl := loop_iter (c := fun a => decide (a 3 ≠ blank) && decide (a 4 ≠ blank))
      (by simp [Tapes.read, hr3, hr4]) (by omega) ha
      (tio_cmp k m n _ h3 h4 (by simp [hh]) (by simp) (by simp; omega))
    refine hl.of_eq ?_ (by omega)
    congr 1
    funext i; simp only [Function.update_apply]; split_ifs <;> rfl

theorem tio_flag (T : Tapes Sym7 6) (h5 : T.cells 5 = tapeOf S7 []) (hh5 : T.head 5 = 1) :
    Runs st (act (fun a => wr1 a 5 (if a 4 = blank then one else zero) Move.stay)) T 1
      ⟨Function.update T.cells 5
        (tapeOf S7 [if T.cells 4 (T.head 4) = blank then one else zero]), T.head⟩ := by
  have ha := act_runs (st := st) (fun a => wr1 a 5 (if a 4 = blank then one else zero) Move.stay) T
  rw [fix_wr1 _ _ _ _ (Or.inr ⟨by decide, by simp [Tapes.read, h5, hh5]; decide,
    by split_ifs <;> decide⟩), write_wr1] at ha
  refine ha.of_eq ?_ rfl
  simp only [Tapes.read, moveHead, Function.update_eq_self]
  rw [h5, hh5, flag_update [] (by simp)]; rfl

theorem tio_scanRep (i : Fin 6) (k : ℕ) (T : Tapes Sym7 6)
    (hc : T.cells i = tapeOf S7 (List.replicate k one)) (h1 : 1 ≤ T.head i) (hk : T.head i ≤ k + 1) :
    Runs st (scanR i notBlank) T (k + 1 - T.head i) ⟨T.cells, Function.update T.head i (k + 1)⟩ := by
  have h := scanR_runs st i notBlank (k + 1 - T.head i) T
    (fun p hp => by
      rw [hc, show T.head i + p = (T.head i + p - 1) + 1 by omega, tio_rep, if_pos (by omega)]; rfl)
    (by rw [hc, show T.head i + (k + 1 - T.head i) = k + 1 by omega, tio_rep, if_neg (by omega)]; rfl)
  refine h.of_eq ?_ rfl
  congr 2; omega

theorem tio_rows_len : ∀ (rows : List (List Ent)), (∀ r ∈ rows, r ≠ [] ∧ ∀ e ∈ r, e ≠ []) →
    rows.length ≤ (tio_rowsW rows).length
  | [], _ => by simp
  | [r], h => by
    have := (tio_row_len r (h r (by simp)).1 (h r (by simp)).2).2
    simp [tio_rowsW]; omega
  | r :: r' :: rs, h => by
    have := (tio_row_len r (h r (by simp)).1 (h r (by simp)).2).2
    have ih := tio_rows_len (r' :: rs) (fun x hx => h x (by simp_all))
    simp only [tio_rowsW, List.length_append, List.length_cons] at ih ⊢; omega

def tio_D (W : List Sym7) (c3 c4 c5 : ℕ → Sym7) (h0 h3 h4 : ℕ) : Tapes Sym7 6 :=
  ⟨fun i => if i = 0 then tapeOf S7 W else if i = 3 then c3 else if i = 4 then c4 else
    if i = 5 then c5 else tapeOf S7 [],
   fun i => if i = 0 then h0 else if i = 1 then 0 else if i = 3 then h3 else if i = 4 then h4 else 1⟩

theorem tio_Dh0 (W : List Sym7) (c3 c4 c5 : ℕ → Sym7) (h0 h3 h4 v v' : ℕ) (hv : v = v') :
    (⟨(tio_D W c3 c4 c5 h0 h3 h4).cells, Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 0 v⟩ :
      Tapes Sym7 6) = tio_D W c3 c4 c5 v' h3 h4 := by
  subst hv; simp only [tio_D]; congr 1; funext i; fin_cases i <;> rfl

theorem tio_Dh3 (W : List Sym7) (c3 c4 c5 : ℕ → Sym7) (h0 h3 h4 v v' : ℕ) (hv : v = v') :
    (⟨(tio_D W c3 c4 c5 h0 h3 h4).cells, Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 3 v⟩ :
      Tapes Sym7 6) = tio_D W c3 c4 c5 h0 v' h4 := by
  subst hv; simp only [tio_D]; congr 1; funext i; fin_cases i <;> rfl

theorem tio_Dh4 (W : List Sym7) (c3 c4 c5 : ℕ → Sym7) (h0 h3 h4 v v' : ℕ) (hv : v = v') :
    (⟨(tio_D W c3 c4 c5 h0 h3 h4).cells, Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 4 v⟩ :
      Tapes Sym7 6) = tio_D W c3 c4 c5 h0 h3 v' := by
  subst hv; simp only [tio_D]; congr 1; funext i; fin_cases i <;> rfl

theorem tio_Dh34 (W : List Sym7) (c3 c4 c5 : ℕ → Sym7) (h0 h3 h4 x x' y y' : ℕ) (hx : x = x')
    (hy : y = y') :
    (⟨(tio_D W c3 c4 c5 h0 h3 h4).cells,
      Function.update (Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 3 x) 4 y⟩ :
      Tapes Sym7 6) = tio_D W c3 c4 c5 h0 x' y' := by
  subst hx hy; simp only [tio_D]; congr 1; funext i; fin_cases i <;> rfl

theorem tio_Dc3 (W : List Sym7) (c3 c4 c5 X X' : ℕ → Sym7) (h0 h3 h4 a a' b b' : ℕ) (hX : X = X')
    (ha : a = a') (hb : b = b') :
    (⟨Function.update (tio_D W c3 c4 c5 h0 h3 h4).cells 3 X,
      Function.update (Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 0 a) 3 b⟩ :
      Tapes Sym7 6) = tio_D W X' c4 c5 a' b' h4 := by
  subst hX ha hb; simp only [tio_D]; congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem tio_Dc4 (W : List Sym7) (c3 c4 c5 X X' : ℕ → Sym7) (h0 h3 h4 a a' b b' : ℕ) (hX : X = X')
    (ha : a = a') (hb : b = b') :
    (⟨Function.update (tio_D W c3 c4 c5 h0 h3 h4).cells 4 X,
      Function.update (Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 0 a) 4 b⟩ :
      Tapes Sym7 6) = tio_D W c3 X' c5 a' h3 b' := by
  subst hX ha hb; simp only [tio_D]; congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem tio_Dc5 (W : List Sym7) (c3 c4 c5 X X' : ℕ → Sym7) (h0 h3 h4 : ℕ) (hX : X = X') :
    (⟨Function.update (tio_D W c3 c4 c5 h0 h3 h4).cells 5 X, (tio_D W c3 c4 c5 h0 h3 h4).head⟩ :
      Tapes Sym7 6) = tio_D W c3 c4 X' h0 h3 h4 := by
  subst hX; simp only [tio_D]; congr 1; funext i; fin_cases i <;> rfl

theorem tio_Dw3 (W : List Sym7) (c3 c4 c5 X X' : ℕ → Sym7) (h0 h3 h4 b b' : ℕ) (hX : X = X')
    (hb : b = b') :
    (⟨Function.update (tio_D W c3 c4 c5 h0 h3 h4).cells 3 X,
      Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 3 b⟩ :
      Tapes Sym7 6) = tio_D W X' c4 c5 h0 b' h4 := by
  subst hX hb; simp only [tio_D]; congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem tio_Dw4 (W : List Sym7) (c3 c4 c5 X X' : ℕ → Sym7) (h0 h3 h4 b b' : ℕ) (hX : X = X')
    (hb : b = b') :
    (⟨Function.update (tio_D W c3 c4 c5 h0 h3 h4).cells 4 X,
      Function.update (tio_D W c3 c4 c5 h0 h3 h4).head 4 b⟩ :
      Tapes Sym7 6) = tio_D W c3 X' c5 h0 h3 b' := by
  subst hX hb; simp only [tio_D]; congr 1 <;> funext i <;> fin_cases i <;> rfl

set_option maxHeartbeats 2000000 in
theorem decideP_runs (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) :
    ∃ t ≤ 20 * ((encIn rows).length + 1),
      Runs st decideP (T0 (encIn rows)) t (TF (encIn rows) (if m ≤ k then one else zero)) := by
  obtain ⟨hm, hm1, hk1, hl1, hrows⟩ := hs
  have hne : ∀ r ∈ rows, r ≠ [] ∧ ∀ e ∈ r, e ≠ [] := by
    intro r hr
    obtain ⟨h1, h2⟩ := hrows r hr
    refine ⟨fun h => by subst h; simp at h1; omega, fun e he h => ?_⟩
    have := h2 e he; subst h; simp at this; omega
  obtain ⟨r1, rs, rfl⟩ : ∃ r1 rs, rows = r1 :: rs := by
    rcases rows with _ | ⟨r1, rs⟩
    · simp at hm; omega
    · exact ⟨r1, rs, rfl⟩
  have hk : r1.length = k := (hrows r1 (by simp)).1
  have hr1 := hne r1 (by simp)
  have hW := tio_encIn (r1 :: rs)
  have hN : (encIn (r1 :: rs)).length = (tio_rowsW (r1 :: rs)).length := by
    rw [← hW, List.length_map]
  have hWst : ∀ x ∈ tio_rowsW (r1 :: rs), x ≠ st := by
    intro x hx; rw [← hW, List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact letter_ne_st y
  obtain ⟨R, hWR, hR⟩ : ∃ R, tio_rowsW (r1 :: rs) = tio_row r1 ++ R ∧
      (R = [] ∨ ∃ R', R = sep :: sep :: R') := by
    rcases rs with _ | ⟨r2, rs⟩
    · exact ⟨[], by simp [tio_rowsW], Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr ⟨_, rfl⟩⟩
  have hNR : (tio_rowsW (r1 :: rs)).length = (tio_row r1).length + R.length := by
    rw [hWR, List.length_append]
  have hite : (if R = [] then 0 else 1) ≤ R.length := by
    split_ifs with h
    · simp
    · exact List.length_pos_iff.mpr h
  have hkN := (tio_row_len r1 hr1.1 hr1.2).1
  have hmN := tio_rows_len (r1 :: rs) hne
  rw [hm] at hmN
  have hT0 : T0 (encIn (r1 :: rs)) = tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 []) (tapeOf S7 [])
      (tapeOf S7 []) 1 1 1 := by
    simp only [T0, tio_D, hW]; congr 1 <;> funext i <;> fin_cases i <;> simp
  have hTF : TF (encIn (r1 :: rs)) (if m ≤ k then one else zero) = tio_D (tio_rowsW (r1 :: rs))
      (tapeOf S7 []) (tapeOf S7 []) (tapeOf S7 [if m ≤ k then one else zero]) 1 1 1 := by
    simp only [TF, T0, tio_D, hW]; congr 1 <;> funext i <;> fin_cases i <;> simp
  rw [hT0, hTF]
  -- the phases
  obtain ⟨t1, ht1, h1⟩ := tio_marks r1 (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 []) (tapeOf S7 []) (tapeOf S7 []) 1 1 1) [] R [] hr1.1 hr1.2 hR (by simp [tio_D, hWR])
    (by simp [tio_D]) (by simp [tio_D]) (by simp [tio_D])
  have h1' : Runs st (rowMarks 3) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 []) (tapeOf S7 []) (tapeOf S7 []) 1 1 1) t1 (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 []) (tapeOf S7 []) ((tio_row r1).length + 1 + if R = [] then 0 else 1) (k + 1) 1) :=
    h1.of_eq (tio_Dc3 _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [hk]) (by simp; omega)
      (by simp only [List.length_nil, hk]; omega)) rfl
  have h2 : Runs st (rewind 0) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 []) (tapeOf S7 []) ((tio_row r1).length + 1 + if R = [] then 0 else 1) (k + 1) 1) (((tio_row r1).length + 1 + if R = [] then 0 else 1) + 1) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 []) (tapeOf S7 []) 1 (k + 1) 1) :=
    (rewind_runs 0 (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 []) (tapeOf S7 []) ((tio_row r1).length + 1 + if R = [] then 0 else 1) (k + 1) 1) (tio_rowsW (r1 :: rs)) hWst (by simp [tio_D])).of_eq (tio_Dh0 _ _ _ _ _ _ _ _ _ rfl)
      (by simp [tio_D])
  obtain ⟨t3, ht3, h3⟩ := tio_rowsl (r1 :: rs) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 []) (tapeOf S7 []) 1 (k + 1) 1) [] [] (by simp) hne (by simp [tio_D])
    (by simp [tio_D]) (by simp [tio_D]) (by simp [tio_D])
  have h3' : Runs st tio_outer (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 []) (tapeOf S7 []) 1 (k + 1) 1) t3 (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) (((tio_rowsW (r1 :: rs)).length) + 1) (k + 1) (m + 1)) :=
    h3.of_eq (tio_Dc4 _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp only [List.nil_append, hm]) (by simp; omega)
      (by simp only [List.length_nil, hm]; omega)) rfl
  have h4 : Runs st (rewind 0) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) (((tio_rowsW (r1 :: rs)).length) + 1) (k + 1) (m + 1)) (((tio_rowsW (r1 :: rs)).length) + 1 + 1) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 (k + 1) (m + 1)) :=
    (rewind_runs 0 (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) (((tio_rowsW (r1 :: rs)).length) + 1) (k + 1) (m + 1)) (tio_rowsW (r1 :: rs)) hWst (by simp [tio_D])).of_eq (tio_Dh0 _ _ _ _ _ _ _ _ _ rfl)
      (by simp [tio_D])
  have h5 : Runs st (rewind 3) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 (k + 1) (m + 1)) (k + 1 + 1) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 1 (m + 1)) :=
    (rewind_runs 3 (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 (k + 1) (m + 1)) (List.replicate k one) (by simp) (by simp [tio_D])).of_eq
      (tio_Dh3 _ _ _ _ _ _ _ _ _ rfl) (by simp [tio_D])
  have h6 : Runs st (rewind 4) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 1 (m + 1)) (m + 1 + 1) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 1 1) :=
    (rewind_runs 4 (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 1 (m + 1)) (List.replicate m one) (by simp) (by simp [tio_D])).of_eq
      (tio_Dh4 _ _ _ _ _ _ _ _ _ rfl) (by simp [tio_D])
  have h7 : Runs st tio_cmpP (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 1 1) (min k m) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 (min k m + 1) (min k m + 1)) :=
    (tio_cmp k m (min k m) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 1 1) (by simp [tio_D]) (by simp [tio_D]) (by simp [tio_D])
      (by simp [tio_D]) (by simp [tio_D]; omega)).of_eq (tio_Dh34 _ _ _ _ _ _ _ _ _ _ _ rfl rfl) rfl
  have hF : (if tapeOf S7 (List.replicate m one) (min k m + 1) = blank then one else zero) =
      if m ≤ k then one else zero := by
    by_cases hmk : m ≤ k
    · simp [tio_rep, show ¬ (min k m < m) by omega, hmk]
    · simp [tio_rep, show min k m < m by omega, hmk]
  have h8 : Runs st (act (fun a => wr1 a 5 (if a 4 = blank then one else zero) Move.stay)) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 (min k m + 1) (min k m + 1)) 1
      (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (min k m + 1) (min k m + 1)) := (tio_flag (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 []) 1 (min k m + 1) (min k m + 1)) (by simp [tio_D]) (by simp [tio_D])).of_eq
        (tio_Dc5 _ _ _ _ _ _ _ _ _ (by simp only [tio_D]; simp [hF])) rfl
  have h9 : Runs st (scanR 3 notBlank) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (min k m + 1) (min k m + 1)) (k + 1 - (min k m + 1)) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (k + 1) (min k m + 1)) :=
    (tio_scanRep 3 k (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (min k m + 1) (min k m + 1)) (by simp [tio_D]) (by simp [tio_D]) (by simp [tio_D])).of_eq
      (tio_Dh3 _ _ _ _ _ _ _ _ _ rfl) (by simp [tio_D])
  have h10 : Runs st (scanR 4 notBlank) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (k + 1) (min k m + 1)) (m + 1 - (min k m + 1)) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (k + 1) (m + 1)) :=
    (tio_scanRep 4 m (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (k + 1) (min k m + 1)) (by simp [tio_D]) (by simp [tio_D]) (by simp [tio_D])).of_eq
      (tio_Dh4 _ _ _ _ _ _ _ _ _ rfl) (by simp [tio_D])
  have h11 : Runs st (wipe 3) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (k + 1) (m + 1)) (k + 2) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 []) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 1 (m + 1)) :=
    (wipe_runs 3 (by decide) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 (List.replicate k one)) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 (k + 1) (m + 1)) (List.replicate k one) (by simp) (by simp [tio_D])
      (by simp [tio_D])).of_eq (tio_Dw3 _ _ _ _ _ _ _ _ _ _ _ rfl rfl) (by simp)
  have h12 : Runs st (wipe 4) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 []) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 1 (m + 1)) (m + 2) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 []) (tapeOf S7 []) (tapeOf S7 [if m ≤ k then one else zero]) 1 1 1) :=
    (wipe_runs 4 (by decide) (tio_D (tio_rowsW (r1 :: rs)) (tapeOf S7 []) (tapeOf S7 (List.replicate m one)) (tapeOf S7 [if m ≤ k then one else zero]) 1 1 (m + 1)) (List.replicate m one) (by simp) (by simp [tio_D])
      (by simp [tio_D])).of_eq (tio_Dw4 _ _ _ _ _ _ _ _ _ _ _ rfl rfl) (by simp)
  refine ⟨_, ?_, seq_runs h1' <| seq_runs h2 <| seq_runs h3' <| seq_runs h4 <| seq_runs h5 <|
    seq_runs h6 <| seq_runs h7 <| seq_runs h8 <| seq_runs h9 <| seq_runs h10 <| seq_runs h11 h12⟩
  have hmin : min k m ≤ k := Nat.min_le_left k m
  have hmin' : min k m ≤ m := Nat.min_le_right k m
  rw [hN]
  omega

end IntMul.Mach.TP

-- ===== TRiffle =====


/-! # Transpose, riffle phase: `rmain_runs` -/

namespace IntMul.Mach.TP

open IntMul IntMul.Mach IntMul.Mach.MS Sym7 IntMul.Mach.MSort

set_option linter.unusedSectionVars false

/-! ## Encodings -/

theorem rf_encE_body (e : Ent) : ∀ x ∈ encE e, isBody x = true := by
  intro x hx
  simp only [encE, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | h
  · exact isBody_enc e x h
  · subst h; rfl

theorem rf_cb_body (c : List Ent) : ∀ x ∈ c.flatMap encE, isBody x = true := by
  intro x hx; simp only [List.mem_flatMap] at hx
  obtain ⟨e, -, he⟩ := hx; exact rf_encE_body e x he

theorem rf_encC_rb (c : List Ent) : ∀ x ∈ encC c, isRunBody x = true := by
  intro x hx; simp only [encC, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | h
  · exact isRunBody_of_isBody (rf_cb_body c x h)
  · subst h; rfl

theorem rf_bb_rb (b : List (List Ent)) : ∀ x ∈ b.flatMap encC, isRunBody x = true := by
  intro x hx; simp only [List.mem_flatMap] at hx
  obtain ⟨c, -, hc⟩ := hx; exact rf_encC_rb c x hc

theorem rf_encB_eq (b : List (List Ent)) : encB b = b.flatMap encC ++ [runend] := rfl

theorem rf_encC_eq (c : List Ent) : encC c = c.flatMap encE ++ [rend] := rfl

theorem rf_rb_ne {x : Sym7} (h : isRunBody x = true) : x ≠ st ∧ x ≠ blank ∧ x ≠ runend := by
  cases x <;> simp_all [isRunBody]

theorem rf_encB_ne_st (b : List (List Ent)) : ∀ x ∈ encB b, x ≠ st := by
  intro x hx
  simp only [rf_encB_eq, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | h
  · exact (rf_rb_ne (rf_bb_rb b x h)).1
  · subst h; decide

theorem rf_encB_ne_blank (b : List (List Ent)) : ∀ x ∈ encB b, x ≠ blank := by
  intro x hx
  simp only [rf_encB_eq, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | h
  · exact (rf_rb_ne (rf_bb_rb b x h)).2.1
  · subst h; decide

theorem rf_encB_ne_nil (b : List (List Ent)) : encB b ≠ [] := by simp [rf_encB_eq]

theorem rf_encBs_cons (b : List (List Ent)) (Gs : List (List (List Ent))) :
    encBs (b :: Gs) = encB b ++ encBs Gs := by simp [encBs]

@[simp] theorem rf_encBs_nil : encBs [] = [] := rfl

theorem rf_encBs_ne_st (Gs : List (List (List Ent))) : ∀ x ∈ encBs Gs, x ≠ st := by
  intro x hx; simp only [encBs, List.mem_flatMap] at hx
  obtain ⟨b, -, hb⟩ := hx; exact rf_encB_ne_st b x hb

/-! ## Copying a block -/

theorem rf_copyRunW (i j : Fin 6) (hij : i ≠ j) (hj : j.val ≠ 0) (T : Tapes Sym7 6)
    (P R Q B : List Sym7) (hB' : ∀ x ∈ B, isRunBody x = true)
    (hci : T.cells i = tapeOf S7 (P ++ (B ++ [runend]) ++ R)) (hhi : T.head i = P.length + 1)
    (hcj : T.cells j = tapeOf S7 Q) (hhj : T.head j = Q.length + 1) :
    Runs st (copyRun i j) T (B ++ [runend]).length
      ⟨Function.update T.cells j (tapeOf S7 (Q ++ (B ++ [runend]))),
        Function.update (Function.update T.head i (P.length + 1 + (B ++ [runend]).length)) j
          (Q.length + 1 + (B ++ [runend]).length)⟩ := by
  have h1 := copyW_runs i j hij hj isRunBody rfl T P B ([runend] ++ R) Q
    (by rw [hci]; simp) hhi hB' rfl hcj hhj
  have h2 := cp1_runs i j hij hj ⟨Function.update T.cells j (tapeOf S7 (Q ++ B)),
      Function.update (Function.update T.head i (P.length + 1 + B.length)) j (Q.length + 1 + B.length)⟩
      runend (by
      show (Function.update T.cells j _) i ((Function.update (Function.update T.head i _) j _) i) = runend
      rw [Function.update_of_ne hij, Function.update_of_ne hij, Function.update_self, hci,
        show P.length + 1 + B.length = (P ++ B).length + 1 by simp; omega,
        show P ++ (B ++ [runend]) ++ R = (P ++ B) ++ runend :: R by simp]
      exact tapeOf_get S7 _ _ _) (by decide) (Q ++ B) (by simp) (by simp; omega)
  refine (seq_runs h1 h2).of_eq ?_ (by simp)
  congr 1
  · funext l; by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  · funext l; by_cases hl : l = j
    · subst hl; simp; omega
    · by_cases hl' : l = i
      · subst hl'; simp [hl]; omega
      · simp [hl, hl']

theorem rf_copyRun_runs (i j : Fin 6) (hij : i ≠ j) (hj : j.val ≠ 0) (T : Tapes Sym7 6)
    (P R Q : List Sym7) (b : List (List Ent))
    (hci : T.cells i = tapeOf S7 (P ++ encB b ++ R)) (hhi : T.head i = P.length + 1)
    (hcj : T.cells j = tapeOf S7 Q) (hhj : T.head j = Q.length + 1) :
    Runs st (copyRun i j) T (encB b).length
      ⟨Function.update T.cells j (tapeOf S7 (Q ++ encB b)),
        Function.update (Function.update T.head i (P.length + 1 + (encB b).length)) j
          (Q.length + 1 + (encB b).length)⟩ := by
  rw [rf_encB_eq] at hci ⊢
  exact rf_copyRunW i j hij hj T P R Q _ (rf_bb_rb b) hci hhi hcj hhj

/-! ## Distribution of blocks -/

theorem rf_dist_runs : ∀ (Rs : List (List (List Ent))) (T : Tapes Sym7 6)
    (P QA QB : List Sym7),
    T.cells 2 = tapeOf S7 (P ++ encBs Rs) → T.head 2 = P.length + 1 →
    T.cells 3 = tapeOf S7 QA → T.head 3 = QA.length + 1 →
    T.cells 4 = tapeOf S7 QB → T.head 4 = QB.length + 1 →
    Runs st dist T (encBs Rs).length
      ⟨Function.update (Function.update T.cells 3 (tapeOf S7 (QA ++ encBs (odds Rs)))) 4
          (tapeOf S7 (QB ++ encBs (evens Rs))),
        Function.update (Function.update (Function.update T.head 2
          (P.length + 1 + (encBs Rs).length)) 3 (QA.length + 1 + (encBs (odds Rs)).length)) 4
          (QB.length + 1 + (encBs (evens Rs)).length)⟩
  | [], T, P, QA, QB, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have h := loop_stop (st := st) (B := (seq (copyRun 2 3)
      (ite (fun a => decide (a 2 = blank)) skip (copyRun 2 4)))) (T := T)
      (c := fun a => decide (a 2 ≠ blank)) (by
        simp only [Tapes.read, hc2, hh2, rf_encBs_nil, List.append_nil, tapeOf_end7]; decide)
    refine h.of_eq ?_ rfl
    simp only [odds, evens, rf_encBs_nil, List.append_nil, List.length_nil, Nat.add_zero]
    rw [← hc3, ← hc4, ← hh2, ← hh3, ← hh4]
    simp
  | [R], T, P, QA, QB, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have h1 := rf_copyRun_runs 2 3 (by decide) (by decide) T P [] QA R
      (by rw [hc2, rf_encBs_cons, rf_encBs_nil]; simp) hh2 hc3 hh3
    have hb : tapeOf S7 (P ++ encB R) (P.length + 1 + (encB R).length) = blank := by
      rw [show P ++ encB R = P ++ encB R ++ [] by simp, tapeOf_after7]; rfl
    have h := loop_iter (c := fun a => decide (a 2 ≠ blank)) ?_ ?_
      (seq_runs h1 (ite_runs_true (c := fun a => decide (a 2 = blank)) (P₂ := copyRun 2 4) ?_ (skip_runs _)))
      (loop_stop ?_)
    rotate_left
    · simp only [Tapes.read, hc2, hh2, rf_encBs_cons, rf_encBs_nil]
      have := tapeOf_first_ne_blank P (encB R) [] (rf_encB_ne_nil R) (rf_encB_ne_blank R)
      simpa using this
    · have := rf_encB_ne_nil R; simp only [Nat.add_zero]; exact List.length_pos_iff.mpr this
    · simp [Tapes.read, hc2, rf_encBs_cons, rf_encBs_nil, hb]
    · simp [Tapes.read, hc2, rf_encBs_cons, rf_encBs_nil, hb]
    refine h.of_eq ?_ (by simp [rf_encBs_cons, rf_encBs_nil])
    simp only [odds, evens, rf_encBs_cons, rf_encBs_nil, List.append_nil, List.length_nil,
      Nat.add_zero]
    rw [← hc4, ← hh4]
    congr 1
    · funext l; fin_cases l <;> simp
    · funext l; fin_cases l <;> simp
  | R1 :: R2 :: rest, T, P, QA, QB, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have hc2' : T.cells 2 = tapeOf S7 (P ++ encB R1 ++ encB R2 ++ encBs rest) := by
      rw [hc2, rf_encBs_cons, rf_encBs_cons]; simp
    have h1 := rf_copyRun_runs 2 3 (by decide) (by decide) T P (encB R2 ++ encBs rest) QA R1
      (by rw [hc2']; simp) hh2 hc3 hh3
    have h2 := rf_copyRun_runs 2 4 (by decide) (by decide)
      ⟨Function.update T.cells 3 (tapeOf S7 (QA ++ encB R1)),
        Function.update (Function.update T.head 2 (P.length + 1 + (encB R1).length)) 3
          (QA.length + 1 + (encB R1).length)⟩ (P ++ encB R1) (encBs rest) QB R2
      (by simp [hc2']) (by simp; omega) (by simp [hc4]) (by simp [hh4])
    have h := loop_iter (c := fun a => decide (a 2 ≠ blank)) ?r1 ?pos
      (seq_runs h1 (ite_runs_false (c := fun a => decide (a 2 = blank)) (P₁ := skip) ?r2 h2))
      (rf_dist_runs rest _ (P ++ encB R1 ++ encB R2) (QA ++ encB R1)
        (QB ++ encB R2) ?a1 ?a2 ?a3 ?a4 ?a5 ?a6)
    case a1 => simp [hc2']
    case a2 => simp; omega
    case a3 => simp
    case a4 => simp; omega
    case a5 => simp
    case a6 => simp; omega
    case r1 =>
      simp only [Tapes.read, hc2', hh2]
      have := tapeOf_first_ne_blank P (encB R1) (encB R2 ++ encBs rest) (rf_encB_ne_nil R1)
        (rf_encB_ne_blank R1)
      simpa [List.append_assoc] using this
    case pos => have := List.length_pos_iff.mpr (rf_encB_ne_nil R1); omega
    case r2 =>
      have := tapeOf_first_ne_blank (P ++ encB R1) (encB R2) (encBs rest)
        (rf_encB_ne_nil R2) (rf_encB_ne_blank R2)
      simp only [Tapes.read]
      simpa [hc2', List.append_assoc, Nat.add_right_comm] using this
    refine h.of_eq ?_ (by simp [rf_encBs_cons]; omega)
    simp only [odds, evens, rf_encBs_cons, List.length_append]
    congr 1
    · funext l; fin_cases l <;> simp
    · funext l; fin_cases l <;> simp <;> omega

/-! ## Riffling two blocks -/

theorem rf_cb_head (c : List Ent) (R : List Sym7) :
    (c.flatMap encE ++ rend :: R).getD 0 blank ≠ runend := by
  rcases h : c.flatMap encE with _ | ⟨x, xs⟩
  · simp
  · have := rf_cb_body c x (by rw [h]; simp)
    simp only [List.cons_append, List.getD_cons_zero]
    intro e; subst e; simp [isBody] at this

theorem rf_rcell_runs (T : Tapes Sym7 6) (c d : List Ent) (PA RA PB RB Q : List Sym7)
    (hc3 : T.cells 3 = tapeOf S7 (PA ++ (c.flatMap encE ++ rend :: RA)))
    (hh3 : T.head 3 = PA.length + 1)
    (hc4 : T.cells 4 = tapeOf S7 (PB ++ (d.flatMap encE ++ rend :: RB)))
    (hh4 : T.head 4 = PB.length + 1)
    (hc2 : T.cells 2 = tapeOf S7 Q) (hh2 : T.head 2 = Q.length + 1) :
    Runs st rcell T ((c.flatMap encE).length + (d.flatMap encE).length + 2)
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ (c.flatMap encE ++ d.flatMap encE ++ [rend]))),
        Function.update (Function.update (Function.update T.head 3
          (PA.length + 1 + (c.flatMap encE).length + 1)) 4
          (PB.length + 1 + (d.flatMap encE).length + 1)) 2
          (Q.length + 1 + (c.flatMap encE).length + (d.flatMap encE).length + 1)⟩ := by
  have h1 := copyW_runs 3 2 (by decide) (by decide) isBody rfl T PA (c.flatMap encE) (rend :: RA) Q
    (by rw [hc3]; simp) hh3 (rf_cb_body c) rfl hc2 hh2
  have h2 := (copyW_runs 4 2 (by decide) (by decide) isBody rfl
    ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ c.flatMap encE)),
      Function.update (Function.update T.head 3 (PA.length + 1 + (c.flatMap encE).length)) 2
        (Q.length + 1 + (c.flatMap encE).length)⟩ PB (d.flatMap encE) (rend :: RB)
    (Q ++ c.flatMap encE) (by dsimp only; rw [Function.update_of_ne (by decide)]; simp [hc4])
    (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hh4])
    (rf_cb_body d) rfl (by simp)
    (by dsimp only; simp only [Function.update_self, List.length_append]; omega)).of_eq
    (T'' := ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ c.flatMap encE ++ d.flatMap encE)),
      Function.update (Function.update (Function.update T.head 3
        (PA.length + 1 + (c.flatMap encE).length)) 4 (PB.length + 1 + (d.flatMap encE).length)) 2
        (Q.length + 1 + (c.flatMap encE).length + (d.flatMap encE).length)⟩) (by
      congr 1
      · funext l; fin_cases l <;> simp
      · funext l; fin_cases l <;> simp <;> omega) rfl
  have h3 := cp1_runs 3 2 (by decide) (by decide)
    ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ c.flatMap encE ++ d.flatMap encE)),
      Function.update (Function.update (Function.update T.head 3
        (PA.length + 1 + (c.flatMap encE).length)) 4 (PB.length + 1 + (d.flatMap encE).length)) 2
        (Q.length + 1 + (c.flatMap encE).length + (d.flatMap encE).length)⟩ rend (by
      dsimp only
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self]
      rw [hc3, show PA.length + 1 + (c.flatMap encE).length = (PA ++ c.flatMap encE).length + 1 by
        rw [List.length_append]; omega, show PA ++ (c.flatMap encE ++ rend :: RA) = (PA ++ c.flatMap encE) ++ rend :: RA
        by simp]
      exact tapeOf_get S7 _ _ _) (by decide) (Q ++ c.flatMap encE ++ d.flatMap encE) (by simp)
      (by simp only [Function.update_self, List.length_append]; omega)
  refine (seq_runs h1 (seq_runs h2 (seq_runs h3 (mv_runs st 4 Move.right _
    (fun h => by cases h))))).of_eq ?_ (by omega)
  congr 1
  · funext l; fin_cases l <;> simp
  · funext l; fin_cases l <;> simp [moveHead] <;> omega

theorem rf_cells_runs : ∀ (a b : List (List Ent)), a.length = b.length →
    ∀ (T : Tapes Sym7 6) (PA RA PB RB Q : List Sym7),
    T.cells 3 = tapeOf S7 (PA ++ (a.flatMap encC ++ runend :: RA)) → T.head 3 = PA.length + 1 →
    T.cells 4 = tapeOf S7 (PB ++ (b.flatMap encC ++ RB)) → T.head 4 = PB.length + 1 →
    T.cells 2 = tapeOf S7 Q → T.head 2 = Q.length + 1 →
    Runs st (loop (fun a => decide (a 3 ≠ runend)) rcell) T
      ((a.flatMap encC).length + (b.flatMap encC).length)
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ (List.zipWith (· ++ ·) a b).flatMap encC)),
        Function.update (Function.update (Function.update T.head 3
          (PA.length + 1 + (a.flatMap encC).length)) 4 (PB.length + 1 + (b.flatMap encC).length)) 2
          (Q.length + 1 + ((List.zipWith (· ++ ·) a b).flatMap encC).length)⟩
  | [], [], _, T, PA, RA, PB, RB, Q, hc3, hh3, hc4, hh4, hc2, hh2 => by
    refine (loop_stop ?_).of_eq ?_ (by simp)
    · simp [Tapes.read, hc3, hh3, tapeOf_at7]
    · cases T with | mk cells head =>
      simp only at hc2 hh2 hh3 hh4
      congr 1
      · funext l; fin_cases l <;> simp [hc2]
      · funext l; fin_cases l <;> simp [hh2, hh3, hh4]
  | [], _ :: _, h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at h
  | c :: a, d :: b, h, T, PA, RA, PB, RB, Q, hc3, hh3, hc4, hh4, hc2, hh2 => by
    have r1 := rf_rcell_runs T c d PA (a.flatMap encC ++ runend :: RA) PB (b.flatMap encC ++ RB) Q
      (by rw [hc3]; simp [rf_encC_eq]) hh3 (by rw [hc4]; simp [rf_encC_eq]) hh4 hc2 hh2
    have r2 := rf_cells_runs a b (by simpa using h)
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ (c.flatMap encE ++ d.flatMap encE ++ [rend]))),
        Function.update (Function.update (Function.update T.head 3
          (PA.length + 1 + (c.flatMap encE).length + 1)) 4
          (PB.length + 1 + (d.flatMap encE).length + 1)) 2
          (Q.length + 1 + (c.flatMap encE).length + (d.flatMap encE).length + 1)⟩ (PA ++ encC c) RA (PB ++ encC d) RB
      (Q ++ encC (c ++ d)) (by simp [hc3]) (by simp [rf_encC_eq]; omega)
      (by simp [hc4]) (by simp [rf_encC_eq]; omega)
      (by simp [rf_encC_eq]) (by simp [rf_encC_eq]; omega)
    refine (loop_iter ?_ (by omega) r1 r2).of_eq ?_ (by simp [rf_encC_eq]; omega)
    · simp only [Tapes.read, hc3, hh3, tapeOf_first]
      have := rf_cb_head c (a.flatMap encC ++ runend :: RA)
      simpa [rf_encC_eq] using this
    · congr 1
      · funext l; fin_cases l <;> simp [rf_encC_eq]
      · funext l; fin_cases l <;> simp [rf_encC_eq] <;> omega

theorem rf_rpair_runs (T : Tapes Sym7 6) (a b : List (List Ent)) (hab : a.length = b.length)
    (PA RA PB RB Q : List Sym7)
    (hc3 : T.cells 3 = tapeOf S7 (PA ++ encB a ++ RA)) (hh3 : T.head 3 = PA.length + 1)
    (hc4 : T.cells 4 = tapeOf S7 (PB ++ encB b ++ RB)) (hh4 : T.head 4 = PB.length + 1)
    (hc2 : T.cells 2 = tapeOf S7 Q) (hh2 : T.head 2 = Q.length + 1) :
    Runs st rpair T ((encB a).length + (encB b).length)
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encB (List.zipWith (· ++ ·) a b))),
        Function.update (Function.update (Function.update T.head 3
          (PA.length + 1 + (encB a).length)) 4 (PB.length + 1 + (encB b).length)) 2
          (Q.length + 1 + (encB (List.zipWith (· ++ ·) a b)).length)⟩ := by
  have r1 := rf_cells_runs a b hab T PA RA PB (runend :: RB) Q (by rw [hc3, rf_encB_eq]; simp) hh3
    (by rw [hc4, rf_encB_eq]; simp) hh4 hc2 hh2
  have r2 := cp1_runs 3 2 (by decide) (by decide)
    ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ (List.zipWith (· ++ ·) a b).flatMap encC)),
        Function.update (Function.update (Function.update T.head 3
          (PA.length + 1 + (a.flatMap encC).length)) 4 (PB.length + 1 + (b.flatMap encC).length)) 2
          (Q.length + 1 + ((List.zipWith (· ++ ·) a b).flatMap encC).length)⟩ runend (by
      dsimp only
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self]
      rw [hc3, rf_encB_eq, show PA.length + 1 + (a.flatMap encC).length =
        (PA ++ a.flatMap encC).length + 1 by rw [List.length_append]; omega,
        show PA ++ (a.flatMap encC ++ [runend]) ++ RA = (PA ++ a.flatMap encC) ++ runend :: RA
        by simp]
      exact tapeOf_get S7 _ _ _) (by decide) (Q ++ (List.zipWith (· ++ ·) a b).flatMap encC)
      (by simp) (by simp only [Function.update_self, List.length_append]; omega)
  have hb := tapeOf_first_ne_blank PB (encB b) RB (rf_encB_ne_nil b) (rf_encB_ne_blank b)
  refine (ite_runs_false ?_ (seq_runs r1 (seq_runs r2 (mv_runs st 4 Move.right _
    (fun h => by cases h))))).of_eq ?_ ?_
  · simp only [Tapes.read, hc4, hh4]; simpa using hb
  · congr 1
    · funext l; fin_cases l <;> simp [rf_encB_eq]
    · funext l; fin_cases l <;> simp [moveHead, rf_encB_eq] <;> omega
  · simp [rf_encB_eq]; omega

def rf_zip : List (List (List Ent)) → List (List (List Ent)) → List (List (List Ent))
  | a :: as, b :: bs => List.zipWith (· ++ ·) a b :: rf_zip as bs
  | as, [] => as
  | [], bs => bs

theorem rf_rall_runs (k : ℕ) : ∀ (As Bs : List (List (List Ent))), Bs.length ≤ As.length →
    As.length ≤ Bs.length + 1 → (∀ a ∈ As, a.length = k) → (∀ b ∈ Bs, b.length = k) →
    ∀ (T : Tapes Sym7 6) (PA PB Q : List Sym7),
    T.cells 3 = tapeOf S7 (PA ++ encBs As) → T.head 3 = PA.length + 1 →
    T.cells 4 = tapeOf S7 (PB ++ encBs Bs) → T.head 4 = PB.length + 1 →
    T.cells 2 = tapeOf S7 Q → T.head 2 = Q.length + 1 →
    Runs st rall T ((encBs As).length + (encBs Bs).length)
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encBs (rf_zip As Bs))),
        Function.update (Function.update (Function.update T.head 3
          (PA.length + 1 + (encBs As).length)) 4 (PB.length + 1 + (encBs Bs).length)) 2
          (Q.length + 1 + (encBs (rf_zip As Bs)).length)⟩ := by
  intro As
  induction As with
  | nil =>
    intro Bs h1 _ _ _ T PA PB Q hA hhA hB hhB hC hhC
    obtain rfl : Bs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at h1; omega)
    refine (loop_stop ?_).of_eq ?_ rfl
    · simp [Tapes.read, hA, hhA]; exact tapeOf_end7 PA
    · cases T with | mk cells head =>
      simp only at hC hhC hhA hhB
      congr 1
      · funext l; fin_cases l <;> simp [hC, rf_zip]
      · funext l; fin_cases l <;> simp [hhC, hhA, hhB, rf_zip]
  | cons a As ih =>
    intro Bs h1 h2 hlA hlB T PA PB Q hA hhA hB hhB hC hhC
    have hfa := tapeOf_first_ne_blank PA (encB a) (encBs As) (rf_encB_ne_nil a) (rf_encB_ne_blank a)
    have hcond : decide (T.read 3 ≠ blank) = true := by
      simp only [Tapes.read, hA, hhA, rf_encBs_cons, ← List.append_assoc]
      simpa using hfa
    have hpos : 0 < (encB a).length := List.length_pos_iff.mpr (rf_encB_ne_nil a)
    rcases Bs with _ | ⟨b, Bs⟩
    · obtain rfl : As = [] := List.eq_nil_of_length_eq_zero
        (by simp only [List.length_cons, List.length_nil] at h2; omega)
      have hcopy := rf_copyRun_runs 3 2 (by decide) (by decide) T PA [] Q a
        (by rw [hA]; simp [encBs]) hhA hC hhC
      have hite := ite_runs_true (c := fun a => decide (a 4 = blank))
        (P₂ := seq (loop (fun a => decide (a 3 ≠ runend)) rcell) (seq (cp1 3 2) (mv 4 Move.right)))
        (by simp [Tapes.read, hB, hhB]; exact tapeOf_end7 PB) hcopy
      refine (loop_iter hcond hpos hite (loop_stop ?_)).of_eq ?_ (by simp [encBs])
      · have e : T.cells 3 (PA.length + 1 + (encB a).length) = blank := by
          rw [hA, show PA ++ encBs [a] = PA ++ encB a by simp [encBs],
            show PA.length + 1 + (encB a).length = (PA ++ encB a).length + 1 by simp; omega]
          exact tapeOf_end7 _
        simp [Tapes.read, e]
      · congr 1
        · funext l; fin_cases l <;> simp [rf_zip, encBs]
        · funext l; fin_cases l <;> simp [rf_zip, encBs, hhB]
    · have hb : b.length = a.length := by rw [hlB b (by simp), hlA a (by simp)]
      have r1 := rf_rpair_runs T a b hb.symm PA (encBs As) PB (encBs Bs) Q
        (by rw [hA, rf_encBs_cons]; simp) hhA (by rw [hB, rf_encBs_cons]; simp) hhB hC hhC
      have r2 := ih Bs (by simp at h1 h2; omega) (by simp at h1 h2; omega)
        (fun x hx => hlA x (by simp [hx])) (fun x hx => hlB x (by simp [hx]))
        ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encB (List.zipWith (· ++ ·) a b))),
          Function.update (Function.update (Function.update T.head 3
            (PA.length + 1 + (encB a).length)) 4 (PB.length + 1 + (encB b).length)) 2
            (Q.length + 1 + (encB (List.zipWith (· ++ ·) a b)).length)⟩
        (PA ++ encB a) (PB ++ encB b) (Q ++ encB (List.zipWith (· ++ ·) a b))
        (by simp [hA, rf_encBs_cons]) (by simp; omega) (by simp [hB, rf_encBs_cons])
        (by simp; omega) (by simp) (by simp; omega)
      refine (loop_iter hcond (by omega) r1 r2).of_eq ?_ (by simp [rf_encBs_cons]; omega)
      congr 1
      · funext l; fin_cases l <;> simp [rf_zip, rf_encBs_cons]
      · funext l; fin_cases l <;> simp [rf_zip, rf_encBs_cons] <;> omega

/-! ## List facts -/

theorem rf_cols_length (k : ℕ) (rows : List (List Ent)) : (cols k rows).length = k := by
  simp [cols]

theorem rf_cols_append (k : ℕ) (a b : List (List Ent)) :
    List.zipWith (· ++ ·) (cols k a) (cols k b) = cols k (a ++ b) := by
  simp [cols, List.zipWith_map, List.zipWith_self]

theorem rf_zip_oe (k : ℕ) : ∀ cs : List (List (List Ent)),
    rf_zip (odds (cs.map (cols k))) (evens (cs.map (cols k))) = (pairUp cs).map (cols k)
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    simp only [List.map_cons, odds, evens, rf_zip, pairUp, rf_cols_append, rf_zip_oe k rest]

theorem rf_encBs_oe : ∀ Gs : List (List (List Ent)),
    (encBs (odds Gs)).length + (encBs (evens Gs)).length = (encBs Gs).length
  | [] => rfl
  | [a] => by simp [odds, evens, encBs]
  | a :: b :: rest => by
    have := rf_encBs_oe rest
    simp only [odds, evens, rf_encBs_cons, List.length_append]; omega

theorem rf_zipC_len : ∀ (A B : List (List Ent)),
    ((List.zipWith (· ++ ·) A B).flatMap encC).length ≤
      (A.flatMap encC).length + (B.flatMap encC).length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | c :: A, d :: B => by
    have := rf_zipC_len A B
    simp only [List.zipWith_cons_cons, List.flatMap_cons, List.length_append, rf_encC_eq,
      List.flatMap_append, List.length_singleton] at this ⊢
    omega

theorem rf_zip_len : ∀ (As Bs : List (List (List Ent))),
    (encBs (rf_zip As Bs)).length ≤ (encBs As).length + (encBs Bs).length
  | a :: As, b :: Bs => by
    have := rf_zip_len As Bs
    have h2 := rf_zipC_len a b
    simp only [rf_zip, rf_encBs_cons, List.length_append, rf_encB_eq, List.length_singleton] at this ⊢
    omega
  | As, [] => by
    rcases As with _ | ⟨a, As⟩ <;> simp [rf_zip]
  | [], b :: Bs => by simp [rf_zip]

theorem rf_pair_len (k : ℕ) (cs : List (List (List Ent))) :
    (encBs ((pairUp cs).map (cols k))).length ≤ (encBs (cs.map (cols k))).length := by
  have h1 := rf_zip_len (odds (cs.map (cols k))) (evens (cs.map (cols k)))
  rw [rf_zip_oe] at h1
  have h2 := rf_encBs_oe (cs.map (cols k))
  omega

theorem rf_oe_cols (k : ℕ) (cs : List (List (List Ent))) :
    (∀ a ∈ odds (cs.map (cols k)), a.length = k) ∧ (∀ b ∈ evens (cs.map (cols k)), b.length = k) := by
  constructor
  · intro a ha
    have := mem_odds ha
    simp only [List.mem_map] at this
    obtain ⟨c, -, rfl⟩ := this; exact rf_cols_length k c
  · intro a ha
    have := mem_evens ha
    simp only [List.mem_map] at this
    obtain ⟨c, -, rfl⟩ := this; exact rf_cols_length k c

/-! ## One pass -/

def rf_Inv (k : ℕ) (T : Tapes Sym7 6) (cs : List (List (List Ent))) : Prop :=
  T.cells 1 = tapeOf S7 [] ∧ T.head 1 = 0 ∧
  T.cells 2 = tapeOf S7 (encBs (cs.map (cols k))) ∧
  T.head 2 = (encBs (cs.map (cols k))).length + 1 ∧
  T.cells 3 = tapeOf S7 (encBs (odds (cs.map (cols k)))) ∧ T.head 3 = 1 ∧
  T.cells 4 = tapeOf S7 (encBs (evens (cs.map (cols k)))) ∧ T.head 4 = 1

set_option maxHeartbeats 2000000 in
theorem rf_pass_runs (k : ℕ) (cs : List (List (List Ent))) (T : Tapes Sym7 6) (hI : rf_Inv k T cs) :
    ∃ t ≤ 6 * (encBs (cs.map (cols k))).length + 12, ∃ T',
      Runs st rpass T t T' ∧ rf_Inv k T' (pairUp cs) := by
  obtain ⟨c1, h1, c2, h2, c3, h3, c4, h4⟩ := hI
  have hoe := rf_encBs_oe (cs.map (cols k))
  have hoe' := rf_encBs_oe ((pairUp cs).map (cols k))
  have hpl := rf_pair_len k cs
  obtain ⟨hA, hB⟩ := rf_oe_cols k cs
  -- a. wipe `C`
  have ra := wipe_runs 2 (by decide) T _ (rf_encBs_ne_st _) c2 h2
  set Ta : Tapes Sym7 6 := ⟨Function.update T.cells 2 (tapeOf S7 []), Function.update T.head 2 1⟩
    with hTa
  -- b. riffle all pairs
  have rb := rf_rall_runs k (odds (cs.map (cols k))) (evens (cs.map (cols k)))
    (odds_evens_len _).1 (odds_evens_len _).2 hA hB Ta [] [] [] (by simp [hTa, c3])
    (by simp [hTa, h3]) (by simp [hTa, c4]) (by simp [hTa, h4]) (by simp [hTa]) (by simp [hTa])
  rw [rf_zip_oe] at rb
  set Tb : Tapes Sym7 6 := ⟨Function.update Ta.cells 2
      (tapeOf S7 ([] ++ encBs ((pairUp cs).map (cols k)))),
    Function.update (Function.update (Function.update Ta.head 3
      (([] : List Sym7).length + 1 + (encBs (odds (cs.map (cols k)))).length)) 4
      (([] : List Sym7).length + 1 + (encBs (evens (cs.map (cols k)))).length)) 2
      (([] : List Sym7).length + 1 + (encBs ((pairUp cs).map (cols k))).length)⟩ with hTb
  -- c, d. wipe `A` and `B`
  have rc := wipe_runs 3 (by decide) Tb _ (rf_encBs_ne_st (odds (cs.map (cols k))))
    (by simp [hTb, hTa, c3]) (by simp [hTb]; omega)
  set Tc : Tapes Sym7 6 := ⟨Function.update Tb.cells 3 (tapeOf S7 []), Function.update Tb.head 3 1⟩
    with hTc
  have rd := wipe_runs 4 (by decide) Tc _ (rf_encBs_ne_st (evens (cs.map (cols k))))
    (by simp [hTc, hTb, hTa, c4]) (by simp [hTc, hTb]; omega)
  set Td : Tapes Sym7 6 := ⟨Function.update Tc.cells 4 (tapeOf S7 []), Function.update Tc.head 4 1⟩
    with hTd
  -- e. rewind `C`
  have re := rewind_runs 2 Td _ (rf_encBs_ne_st ((pairUp cs).map (cols k)))
    (by simp [hTd, hTc, hTb])
  set Te : Tapes Sym7 6 := ⟨Td.cells, Function.update Td.head 2 1⟩ with hTe
  -- f. distribute
  have rf := rf_dist_runs ((pairUp cs).map (cols k)) Te [] [] [] (by simp [hTe, hTd, hTc, hTb])
    (by simp [hTe]) (by simp [hTe, hTd, hTc]) (by simp [hTe, hTd, hTc])
    (by simp [hTe, hTd, hTc]) (by simp [hTe, hTd, hTc])
  set Tf : Tapes Sym7 6 := ⟨Function.update (Function.update Te.cells 3
      (tapeOf S7 ([] ++ encBs (odds ((pairUp cs).map (cols k)))))) 4
      (tapeOf S7 ([] ++ encBs (evens ((pairUp cs).map (cols k))))),
    Function.update (Function.update (Function.update Te.head 2
      (([] : List Sym7).length + 1 + (encBs ((pairUp cs).map (cols k))).length)) 3
      (([] : List Sym7).length + 1 + (encBs (odds ((pairUp cs).map (cols k)))).length)) 4
      (([] : List Sym7).length + 1 + (encBs (evens ((pairUp cs).map (cols k)))).length)⟩ with hTf
  -- g. rewind `A` and `B`
  have rg := rewind_runs 3 Tf _ (rf_encBs_ne_st (odds ((pairUp cs).map (cols k)))) (by simp [hTf])
  set Tg : Tapes Sym7 6 := ⟨Tf.cells, Function.update Tf.head 3 1⟩ with hTg
  have rh := rewind_runs 4 Tg _ (rf_encBs_ne_st (evens ((pairUp cs).map (cols k))))
    (by simp [hTg, hTf])
  refine ⟨_, ?_, _, seq_runs ra (seq_runs rb (seq_runs rc (seq_runs rd (seq_runs re (seq_runs rf
    (seq_runs rg rh)))))), ?_⟩
  · have e1 : Td.head 2 = (encBs ((pairUp cs).map (cols k))).length + 1 := by
      simp [hTd, hTc, hTb]; omega
    have e2 : Tf.head 3 = (encBs (odds ((pairUp cs).map (cols k)))).length + 1 := by
      simp [hTf]; omega
    have e3 : Tg.head 4 = (encBs (evens ((pairUp cs).map (cols k)))).length + 1 := by
      simp [hTg, hTf]; omega
    rw [e1, e2, e3]
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hTg, hTf, hTe, hTd, hTc, hTb, hTa, c1]
    · simp [hTg, hTf, hTe, hTd, hTc, hTb, hTa, h1]
    · simp [hTg, hTf, hTe, hTd, hTc, hTb]
    · simp [hTg, hTf, hTe, hTd, hTc]; omega
    · simp [hTg, hTf]
    · simp [hTg, hTf]
    · simp [hTg, hTf]
    · simp [hTg, hTf]

/-! ## The pass loop -/

theorem rf_mainLoop_runs (k N : ℕ) : ∀ (n : ℕ) (cs : List (List (List Ent))), cs.length = n →
    1 ≤ n → (encBs (cs.map (cols k))).length ≤ N → ∀ T, rf_Inv k T cs →
    ∃ t ≤ Nat.clog 2 n * (6 * N + 12), ∃ T',
      Runs st (loop (fun a => decide (a 4 ≠ blank)) rpass) T t T' ∧
      T'.cells 1 = tapeOf S7 [] ∧ T'.head 1 = 0 ∧
      T'.cells 2 = tapeOf S7 (encB (cols k cs.flatten)) ∧
      T'.head 2 = (encB (cols k cs.flatten)).length + 1 ∧
      (encB (cols k cs.flatten)).length ≤ N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro cs hn h1 hN T hI
  by_cases hn1 : n = 1
  · subst hn1
    obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
      rcases cs with _ | ⟨c, _ | ⟨d, cs⟩⟩
      · simp at hn
      · exact ⟨c, rfl⟩
      · simp at hn
    obtain ⟨c1, h1', c2, h2', c3, h3', c4, h4'⟩ := hI
    refine ⟨0, by simp, T, loop_stop ?_, c1, h1', ?_, ?_, ?_⟩
    · simp [Tapes.read, c4, h4', evens_one, tapeOf]; rfl
    · rw [c2]; simp [encBs]
    · rw [h2']; simp [encBs]
    · simpa [encBs] using hN
  · have hn2 : 2 ≤ n := by omega
    have hcond : decide (T.read 4 ≠ blank) = true := by
      obtain ⟨-, -, -, -, -, -, c4, h4'⟩ := hI
      have hev := evens_ne_nil (cs.map (cols k)) (by simp; omega)
      obtain ⟨a, Rs, he⟩ := List.exists_cons_of_ne_nil hev
      have := tapeOf_first_ne_blank [] (encB a) (encBs Rs) (rf_encB_ne_nil a) (rf_encB_ne_blank a)
      simp only [Tapes.read, c4, h4', he, rf_encBs_cons]
      simpa using this
    obtain ⟨t1, ht1, T1, r1, hI1⟩ := rf_pass_runs k cs T hI
    have hlen : (pairUp cs).length = (n + 1) / 2 := by rw [length_pairUp, hn]
    obtain ⟨t2, ht2, T2, r2, o1, o2, o3, o4, o5⟩ := ih ((n + 1) / 2) (by omega) (pairUp cs) hlen
      (by omega) (le_trans (rf_pair_len k cs) hN) T1 hI1
    rw [flatten_pairUp] at o3 o4 o5
    have hpos : 0 < t1 := by
      rcases Nat.eq_zero_or_pos t1 with h | h
      · subst h
        exfalso
        cases r1 with
        | done h0 => simp [rpass, wipe, seq, mv, act] at h0
      · exact h
    refine ⟨t1 + t2, ?_, T2, loop_iter hcond hpos r1 r2, o1, o2, o3, o4, o5⟩
    rw [Nat.clog_of_two_le (by norm_num) hn2, show n + 2 - 1 = n + 1 by omega]
    nlinarith

/-! ## Input conversion -/

def rf_rowToks : List Ent → List (Ent × Bool)
  | [] => []
  | [e] => [(e, true)]
  | e :: e' :: es => (e, false) :: rf_rowToks (e' :: es)

def rf_tokIn : List (Ent × Bool) → List Sym7
  | [] => []
  | [(e, _)] => enc e
  | (e, b) :: t :: ts => enc e ++ (if b then [sep, sep] else [sep]) ++ rf_tokIn (t :: ts)

def rf_tokOut : List (Ent × Bool) → List Sym7
  | [] => []
  | (e, b) :: ts => enc e ++ [sep, rend] ++ (if b then [runend] else []) ++ rf_tokOut ts

def rf_ITE : Prog Sym7 6 :=
  ite (fun a => decide (a 0 = sep))
    (seq (mv 0 Move.right) (ite (fun a => decide (a 0 = sep)) (seq (mv 0 Move.right) (wsym 2 runend)) skip))
    (wsym 2 runend)

theorem rf_enc_bit (e : Ent) : ∀ x ∈ enc e, isBit x = true := by
  intro x hx; simp only [enc, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx; cases b <;> rfl

theorem rf_start {P : Prog Sym7 6} {T1 T2 T' : Tapes Sym7 6} {t : ℕ} (e : T1 = T2)
    (h : Runs st P T2 t T') : Runs st P T1 t T' := e ▸ h

theorem rf_step_runs (T : Tapes Sym7 6) (e : Ent) (P R Q : List Sym7) (hR : isBit (R.getD 0 blank) = false)
    (hc0 : T.cells 0 = tapeOf S7 (P ++ enc e ++ R)) (hh0 : T.head 0 = P.length + 1)
    (hc2 : T.cells 2 = tapeOf S7 Q) (hh2 : T.head 2 = Q.length + 1) {s : ℕ} {T' : Tapes Sym7 6}
    (h : Runs st rf_ITE ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ enc e ++ [sep, rend])),
      Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
        (Q.length + 1 + e.length + 2)⟩ s T') :
    Runs st rconvStep T (e.length + 2 + s) T' := by
  have h1 := copyW_runs 0 2 (by decide) (by decide) isBit rfl T P (enc e) R Q hc0 hh0
    (rf_enc_bit e) hR hc2 hh2
  have e1 : (enc e).length = e.length := by simp [enc]
  refine (seq_runs h1 (seq_runs (wsym_runs 2 (by decide) sep (by decide) _ (Q ++ enc e) ?a ?b)
    (seq_runs (wsym_runs 2 (by decide) rend (by decide) _ (Q ++ enc e ++ [sep]) ?c ?d)
    (rf_start ?eq h)))).of_eq rfl (by omega)
  case a => simp
  case b => simp; omega
  case c => simp
  case d => simp; omega
  case eq =>
    congr 1
    · funext l; fin_cases l <;> simp
    · funext l; fin_cases l <;> simp <;> omega

theorem rf_tok_first (P : List Sym7) (t : Ent × Bool) (ts : List (Ent × Bool)) (ht : t.1 ≠ []) :
    tapeOf S7 (P ++ rf_tokIn (t :: ts)) (P.length + 1) ≠ blank ∧
      tapeOf S7 (P ++ rf_tokIn (t :: ts)) (P.length + 1) ≠ sep := by
  obtain ⟨e, b⟩ := t
  obtain ⟨x, e', rfl⟩ := List.exists_cons_of_ne_nil ht
  have : ∃ rest, rf_tokIn ((x :: e', b) :: ts) = bs x :: rest := by
    rcases ts with _ | ⟨u, ts⟩
    · exact ⟨enc e', by simp [rf_tokIn, enc]⟩
    · exact ⟨enc e' ++ ((if b then [sep, sep] else [sep]) ++ rf_tokIn (u :: ts)),
        by simp [rf_tokIn, enc]⟩
  obtain ⟨rest, h⟩ := this
  rw [h, tapeOf_at7]
  cases x <;> decide

theorem rf_conv_runs : ∀ (ts : List (Ent × Bool)), (∀ x ∈ ts, x.1 ≠ []) →
    (∀ x, ts.getLast? = some x → x.2 = true) → ∀ (T : Tapes Sym7 6) (P Q : List Sym7),
    T.cells 0 = tapeOf S7 (P ++ rf_tokIn ts) → T.head 0 = P.length + 1 →
    T.cells 2 = tapeOf S7 Q → T.head 2 = Q.length + 1 →
    ∃ t ≤ 3 * (rf_tokIn ts).length + 3,
      Runs st (loop (fun a => decide (a 0 ≠ blank)) rconvStep) T t
        ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ rf_tokOut ts)),
          Function.update (Function.update T.head 0 (P.length + 1 + (rf_tokIn ts).length)) 2
            (Q.length + 1 + (rf_tokOut ts).length)⟩
  | [], _, _, T, P, Q, hc0, hh0, hc2, hh2 => by
    refine ⟨0, by omega, (loop_stop ?_).of_eq ?_ rfl⟩
    · simp [Tapes.read, hc0, hh0, rf_tokIn, tapeOf_end7]
    · cases T with | mk cells head =>
      simp only at hc2 hh2 hh0
      congr 1
      · funext l; fin_cases l <;> simp [hc2, rf_tokOut]
      · funext l; fin_cases l <;> simp [hh2, hh0, rf_tokIn, rf_tokOut]
  | [(e, b)], hne, hl, T, P, Q, hc0, hh0, hc2, hh2 => by
    have hb : b = true := hl (e, b) rfl
    have he : e ≠ [] := hne (e, b) (by simp)
    subst hb
    have e1 : (enc e).length = e.length := by simp [enc]
    have hc0' : T.cells 0 = tapeOf S7 (P ++ enc e ++ []) := by simpa [rf_tokIn] using hc0
    have hend : T.cells 0 (P.length + 1 + e.length) = blank := by
      rw [hc0', List.append_nil, show P.length + 1 + e.length = (P ++ enc e).length + 1 by
        simp [e1]; omega]
      exact tapeOf_end7 _
    have r := rf_step_runs T e P [] Q rfl hc0' hh0 hc2 hh2
      (ite_runs_false (c := fun a => decide (a 0 = sep)) ?c
        (wsym_runs 2 (by decide) runend (by decide) _ (Q ++ enc e ++ [sep, rend]) (by simp)
          (by simp; omega)))
    case c => simp [Tapes.read, hend]
    have hfirst := (rf_tok_first P (e, true) [] he).1
    refine ⟨_, ?_, (loop_iter ?_ (by omega) r (loop_stop ?_)).of_eq ?_ rfl⟩
    · simp [rf_tokIn, e1]; omega
    · simp only [Tapes.read, hc0, hh0]; simpa using hfirst
    · simp [Tapes.read, hend]
    · congr 1
      · funext l; fin_cases l <;> simp [rf_tokOut]
      · funext l; fin_cases l <;> simp [rf_tokIn, rf_tokOut, e1] <;> omega
  | (e, b) :: t :: ts, hne, hl, T, P, Q, hc0, hh0, hc2, hh2 => by
    have he : e ≠ [] := hne (e, b) (by simp)
    have ht : t.1 ≠ [] := hne t (by simp)
    have e1 : (enc e).length = e.length := by simp [enc]
    have hc0' : T.cells 0 = tapeOf S7 (P ++ enc e ++ ((if b then [sep, sep] else [sep]) ++
        rf_tokIn (t :: ts))) := by rw [hc0]; simp [rf_tokIn]
    have hS1 : T.cells 0 (P.length + 1 + e.length) = sep := by
      rw [hc0', show P.length + 1 + e.length = (P ++ enc e).length + 1 by simp [e1]; omega,
        tapeOf_first]
      cases b <;> rfl
    -- the part of the step after the entry
    obtain ⟨P', Q', s, hs, rI, hP', hQ', hlen⟩ : ∃ (P' Q' : List Sym7) (s : ℕ),
        s + 1 ≤ 2 * (P'.length - P.length - e.length) ∧
        Runs st rf_ITE ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ enc e ++ [sep, rend])),
          Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
            (Q.length + 1 + e.length + 2)⟩ s
          ⟨Function.update T.cells 2 (tapeOf S7 Q'),
            Function.update (Function.update T.head 0 (P'.length + 1)) 2 (Q'.length + 1)⟩ ∧
        P ++ rf_tokIn ((e, b) :: t :: ts) = P' ++ rf_tokIn (t :: ts) ∧
        Q' = Q ++ enc e ++ [sep, rend] ++ (if b then [runend] else []) ∧
        P.length + e.length + 1 ≤ P'.length := by
      cases b with
      | false =>
        have hS2 : T.cells 0 (P.length + 1 + e.length + 1) ≠ sep := by
          have := (rf_tok_first (P ++ enc e ++ [sep]) t ts ht).2
          rw [hc0]; simp only [rf_tokIn, Bool.false_eq_true, if_false]
          convert this using 2
          · simp
          · simp [e1]; omega
        refine ⟨P ++ enc e ++ [sep], Q ++ enc e ++ [sep, rend], 1, by simp [e1], ?_, by simp [rf_tokIn],
          by simp, by simp [e1]⟩
        refine (ite_runs_true (c := fun a => decide (a 0 = sep)) ?_ (seq_runs
          (mv_runs st 0 Move.right _ nofun)
          (ite_runs_false (c := fun a => decide (a 0 = sep)) ?_ (skip_runs _)))).of_eq ?_ rfl
        · simp [Tapes.read, hS1]
        · simp [Tapes.read, moveHead, hS2]
        · congr 1 <;> funext l <;> fin_cases l <;> simp [moveHead, e1] <;> omega
      | true =>
        have hS2 : T.cells 0 (P.length + 1 + e.length + 1) = sep := by
          rw [hc0', show P.length + 1 + e.length + 1 = (P ++ enc e ++ [sep]).length + 1 by
            simp [e1]; omega]
          simp only [if_true]
          rw [show P ++ enc e ++ ([sep, sep] ++ rf_tokIn (t :: ts)) =
            (P ++ enc e ++ [sep]) ++ sep :: rf_tokIn (t :: ts) by simp]
          exact tapeOf_at7 _ _ _
        refine ⟨P ++ enc e ++ [sep, sep], Q ++ enc e ++ [sep, rend, runend], 3, by simp [e1], ?_,
          by simp [rf_tokIn], by simp, by simp [e1]⟩
        refine (ite_runs_true (c := fun a => decide (a 0 = sep)) ?_ (seq_runs
          (mv_runs st 0 Move.right _ nofun)
          (ite_runs_true (c := fun a => decide (a 0 = sep)) ?_ (seq_runs
            (mv_runs st 0 Move.right _ nofun)
            (wsym_runs 2 (by decide) runend (by decide) _ (Q ++ enc e ++ [sep, rend]) ?_ ?_))))).of_eq
          ?_ rfl
        · simp [Tapes.read, hS1]
        · simp [Tapes.read, moveHead, hS2]
        · simp
        · simp [moveHead]; omega
        · congr 1 <;> funext l <;> fin_cases l <;> simp [moveHead, e1] <;> omega
    have r1 := rf_step_runs T e P _ Q (by cases b <;> rfl) hc0' hh0 hc2 hh2 rI
    obtain ⟨t2, ht2, r2⟩ := rf_conv_runs (t :: ts) (fun x hx => hne x (by simp_all))
      (fun x hx => hl x (by simpa using hx))
      ⟨Function.update T.cells 2 (tapeOf S7 Q'),
        Function.update (Function.update T.head 0 (P'.length + 1)) 2 (Q'.length + 1)⟩ P' Q'
      (by simp [hc0, hP']) (by simp) (by simp) (by simp)
    have hfirst := (rf_tok_first P (e, b) (t :: ts) he).1
    have hlenIn := congrArg List.length hP'
    simp only [List.length_append] at hlenIn
    have hin : (rf_tokIn ((e, b) :: t :: ts)).length =
        e.length + (if b then 2 else 1) + (rf_tokIn (t :: ts)).length := by
      cases b <;> simp [rf_tokIn, e1] <;> omega
    refine ⟨_, ?_, (loop_iter ?_ (by omega) r1 r2).of_eq ?_ rfl⟩
    · omega
    · simp only [Tapes.read, hc0, hh0]; simpa using hfirst
    · subst hQ'
      congr 1
      · funext l; fin_cases l <;> simp [rf_tokOut]
      · funext l; fin_cases l <;> simp [rf_tokOut, e1] <;> omega

/-! ## Token lists -/

theorem rf_tokIn_cons (e : Ent) (b : Bool) (ts : List (Ent × Bool)) (h : ts ≠ []) :
    rf_tokIn ((e, b) :: ts) = enc e ++ (if b then [sep, sep] else [sep]) ++ rf_tokIn ts := by
  rcases ts with _ | ⟨t, ts⟩
  · exact absurd rfl h
  · rfl

theorem rf_tokOut_append (xs ys : List (Ent × Bool)) :
    rf_tokOut (xs ++ ys) = rf_tokOut xs ++ rf_tokOut ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => obtain ⟨e, b⟩ := x; simp [rf_tokOut, ih]

theorem rf_letter_bits (e : Ent) : (bits e).map letter = enc e := by
  simp [bits, enc, Function.comp_def, letter]

theorem rf_rowToks_ne (r : List Ent) (h : r ≠ []) : rf_rowToks r ≠ [] := by
  rcases r with _ | ⟨e, _ | ⟨e', es⟩⟩
  · exact absurd rfl h
  · simp [rf_rowToks]
  · simp [rf_rowToks]

theorem rf_rowIn : ∀ (r : List Ent), r ≠ [] →
    (joinSep (r.map bits)).map letter = rf_tokIn (rf_rowToks r) ∧
    ∀ ts, ts ≠ [] → rf_tokIn (rf_rowToks r ++ ts) =
      (joinSep (r.map bits)).map letter ++ [sep, sep] ++ rf_tokIn ts
  | [], h => absurd rfl h
  | [e], _ => by
    refine ⟨by simp [joinSep, rf_rowToks, rf_tokIn, rf_letter_bits], fun ts hts => ?_⟩
    simp only [rf_rowToks, List.singleton_append]
    rw [rf_tokIn_cons _ _ _ hts]
    simp [joinSep, rf_letter_bits]
  | e :: e' :: es, _ => by
    obtain ⟨ih1, ih2⟩ := rf_rowIn (e' :: es) (by simp)
    have hne := rf_rowToks_ne (e' :: es) (by simp)
    have hj : joinSep ((e :: e' :: es).map bits) = bits e ++ [none] ++ joinSep ((e' :: es).map bits) := by
      simp [joinSep, List.intercalate_cons_cons]
    refine ⟨?_, fun ts hts => ?_⟩
    · rw [hj, show rf_rowToks (e :: e' :: es) = (e, false) :: rf_rowToks (e' :: es) from rfl,
        rf_tokIn_cons _ _ _ hne, ← ih1]
      simp [rf_letter_bits, letter]
    · rw [hj, show rf_rowToks (e :: e' :: es) = (e, false) :: rf_rowToks (e' :: es) from rfl,
        List.cons_append, rf_tokIn_cons _ _ _ (by simp [hne]), ih2 ts hts]
      simp [rf_letter_bits, letter]

theorem rf_encIn_toks : ∀ (rows : List (List Ent)), (∀ r ∈ rows, r ≠ []) →
    (encIn rows).map letter = rf_tokIn (rows.flatMap rf_rowToks)
  | [], _ => rfl
  | [r], h => by
    simp only [encIn, List.map_cons, List.map_nil, List.intercalate_singleton, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    exact (rf_rowIn r (h r (by simp))).1
  | r :: r2 :: rs, h => by
    have ih := rf_encIn_toks (r2 :: rs) (fun x hx => h x (by simp_all))
    have hne : (r2 :: rs).flatMap rf_rowToks ≠ [] := by
      simp only [List.flatMap_cons]
      have := rf_rowToks_ne r2 (h r2 (by simp))
      intro e; simp_all
    rw [List.flatMap_cons, (rf_rowIn r (h r (by simp))).2 _ hne, ← ih]
    simp [encIn, List.intercalate_cons_cons, letter]

theorem rf_rowOut : ∀ (r : List Ent), r ≠ [] → rf_tokOut (rf_rowToks r) = encB (r.map fun e => [e])
  | [], h => absurd rfl h
  | [e], _ => by simp [rf_rowToks, rf_tokOut, encB, encC, encE]
  | e :: e' :: es, _ => by
    have ih := rf_rowOut (e' :: es) (by simp)
    rw [show rf_rowToks (e :: e' :: es) = (e, false) :: rf_rowToks (e' :: es) from rfl]
    simp only [rf_tokOut, ih]
    simp [encB, encC, encE]

theorem rf_encBs_toks : ∀ (rows : List (List Ent)), (∀ r ∈ rows, r ≠ []) →
    encBs (rows.map fun r => r.map fun e => [e]) = rf_tokOut (rows.flatMap rf_rowToks)
  | [], _ => rfl
  | r :: rs, h => by
    rw [List.map_cons, rf_encBs_cons, List.flatMap_cons, rf_tokOut_append,
      rf_rowOut r (h r (by simp)), rf_encBs_toks rs (fun x hx => h x (by simp [hx]))]

theorem rf_rowToks_mem : ∀ (r : List Ent), ∀ x ∈ rf_rowToks r, x.1 ∈ r
  | [], x, hx => by simp [rf_rowToks] at hx
  | [e], x, hx => by simp [rf_rowToks] at hx; simp [hx]
  | e :: e' :: es, x, hx => by
    simp only [rf_rowToks, List.mem_cons] at hx
    rcases hx with hx | hx
    · simp [hx]
    · have := rf_rowToks_mem (e' :: es) x hx
      simp only [List.mem_cons] at this ⊢; tauto

theorem rf_rowToks_last : ∀ (r : List Ent), ∀ x, (rf_rowToks r).getLast? = some x → x.2 = true
  | [], x, hx => by simp [rf_rowToks] at hx
  | [e], x, hx => by simp [rf_rowToks] at hx; simp [← hx]
  | e :: e' :: es, x, hx => by
    have hne := rf_rowToks_ne (e' :: es) (by simp)
    rw [show rf_rowToks (e :: e' :: es) = (e, false) :: rf_rowToks (e' :: es) from rfl] at hx
    obtain ⟨u, us, hu⟩ := List.exists_cons_of_ne_nil hne
    rw [hu, List.getLast?_cons_cons, ← hu] at hx
    exact rf_rowToks_last (e' :: es) x hx

theorem rf_toks_last : ∀ (rows : List (List Ent)), ∀ x,
    (rows.flatMap rf_rowToks).getLast? = some x → x.2 = true
  | [], x, hx => by simp at hx
  | r :: rs, x, hx => by
    rw [List.flatMap_cons, List.getLast?_append] at hx
    rcases h : (rs.flatMap rf_rowToks).getLast? with _ | y
    · rw [h] at hx; simp at hx; exact rf_rowToks_last r x hx
    · rw [h] at hx; simp at hx; subst hx; exact rf_toks_last rs _ h

theorem rf_tok_len : ∀ (ts : List (Ent × Bool)), (∀ x ∈ ts, x.1 ≠ []) →
    (rf_tokOut ts).length ≤ 2 * (rf_tokIn ts).length + 2
  | [], _ => by simp [rf_tokOut]
  | [(e, b)], h => by
    have : e ≠ [] := h (e, b) (by simp)
    have : 0 < e.length := List.length_pos_iff.mpr this
    cases b <;> simp [rf_tokOut, rf_tokIn, enc] <;> omega
  | (e, b) :: t :: ts, h => by
    have ih := rf_tok_len (t :: ts) (fun x hx => h x (by simp_all))
    have : e ≠ [] := h (e, b) (by simp)
    have : 0 < e.length := List.length_pos_iff.mpr this
    rw [rf_tokIn_cons _ _ _ (by simp)]
    simp only [rf_tokOut] at ih ⊢
    cases b <;> simp [enc] at ih ⊢ <;> omega

theorem rf_cols_single (k : ℕ) (r : List Ent) (hr : r.length = k) :
    cols k [r] = r.map fun e => [e] := by
  apply List.ext_getElem
  · simp [cols, hr]
  · intro j h1 h2
    simp [cols, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp at h2; omega)]
    simp

/-! ## The riffle phase -/

theorem rf_flatten_single (rows : List (List Ent)) : (rows.map fun r => [r]).flatten = rows := by
  induction rows <;> simp_all

set_option maxHeartbeats 4000000 in
theorem rmain_runs (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) (F : Sym7)
    (hF : F ≠ st) :
    ∃ t ≤ 100 * ((encIn rows).length + 1) * (Nat.clog 2 m + 1), ∃ T',
      Runs st rmain (TF (encIn rows) F) t T' ∧ T'.cells 1 = tapeOf S7 [] ∧ T'.head 1 = 0 ∧
      T'.cells 2 = tapeOf S7 (encB (cols k rows)) ∧
      T'.head 2 ≤ 4 * ((encIn rows).length + 1) ∧
      (encB (cols k rows)).length ≤ 4 * ((encIn rows).length + 1) := by
  obtain ⟨hm, hm1, hk1, hl1, hrows⟩ := hs
  have hrne : ∀ r ∈ rows, r ≠ [] := by
    intro r hr; have := (hrows r hr).1; intro e; subst e; simp at this; omega
  have hene : ∀ x ∈ rows.flatMap rf_rowToks, x.1 ≠ [] := by
    intro x hx
    simp only [List.mem_flatMap] at hx
    obtain ⟨r, hr, hx⟩ := hx
    have := (hrows r hr).2 _ (rf_rowToks_mem r x hx)
    intro e; rw [e] at this; simp at this; omega
  set ts := rows.flatMap rf_rowToks with hts
  set w := encIn rows with hw
  have hIn : w.map letter = rf_tokIn ts := rf_encIn_toks rows hrne
  have hn : (rf_tokIn ts).length = w.length := by rw [← hIn]; simp
  set G0 : List (List (List Ent)) := rows.map fun r => r.map fun e => [e] with hG0
  have hOut : encBs G0 = rf_tokOut ts := rf_encBs_toks rows hrne
  set cs : List (List (List Ent)) := rows.map fun r => [r] with hcs
  have hG : cs.map (cols k) = G0 := by
    simp only [hcs, hG0, List.map_map]
    apply List.map_congr_left
    intro r hr; exact rf_cols_single k r (hrows r hr).1
  have hlenO : (rf_tokOut ts).length ≤ 2 * w.length + 2 := by
    have := rf_tok_len ts hene; omega
  -- 1. conversion
  obtain ⟨t1, ht1, r1⟩ := rf_conv_runs ts hene (rf_toks_last rows) (TF w F) [] []
    (by simp [TF, T0, hIn]) (by simp [TF, T0]) (by simp [TF, T0]) (by simp [TF, T0])
  set T1 : Tapes Sym7 6 := ⟨Function.update (TF w F).cells 2 (tapeOf S7 ([] ++ rf_tokOut ts)),
    Function.update (Function.update (TF w F).head 0
      (([] : List Sym7).length + 1 + (rf_tokIn ts).length)) 2
      (([] : List Sym7).length + 1 + (rf_tokOut ts).length)⟩ with hT1
  -- 2. rewind `C`
  have r2 := rewind_runs 2 T1 _ (rf_encBs_ne_st G0) (by simp [hT1, hOut])
  set T2 : Tapes Sym7 6 := ⟨T1.cells, Function.update T1.head 2 1⟩ with hT2
  -- 3. distribute
  have r3 := rf_dist_runs G0 T2 [] [] [] (by simp [hT2, hT1, hOut]) (by simp [hT2])
    (by simp [hT2, hT1, TF, T0]) (by simp [hT2, hT1, TF, T0]) (by simp [hT2, hT1, TF, T0])
    (by simp [hT2, hT1, TF, T0])
  set T3 : Tapes Sym7 6 := ⟨Function.update (Function.update T2.cells 3
      (tapeOf S7 ([] ++ encBs (odds G0)))) 4 (tapeOf S7 ([] ++ encBs (evens G0))),
    Function.update (Function.update (Function.update T2.head 2
      (([] : List Sym7).length + 1 + (encBs G0).length)) 3
      (([] : List Sym7).length + 1 + (encBs (odds G0)).length)) 4
      (([] : List Sym7).length + 1 + (encBs (evens G0)).length)⟩ with hT3
  -- 4, 5. rewind `A` and `B`
  have r4 := rewind_runs 3 T3 _ (rf_encBs_ne_st (odds G0)) (by simp [hT3])
  set T4 : Tapes Sym7 6 := ⟨T3.cells, Function.update T3.head 3 1⟩ with hT4
  have r5 := rewind_runs 4 T4 _ (rf_encBs_ne_st (evens G0)) (by simp [hT4, hT3])
  set T5 : Tapes Sym7 6 := ⟨T4.cells, Function.update T4.head 4 1⟩ with hT5
  have hI : rf_Inv k T5 cs := by
    rw [rf_Inv, hG]
    refine ⟨by simp [hT5, hT4, hT3, hT2, hT1, TF, T0], by simp [hT5, hT4, hT3, hT2, hT1, TF, T0],
      by simp [hT5, hT4, hT3, hT2, hT1, hOut], by simp [hT5, hT4, hT3, hT2]; omega,
      by simp [hT5, hT4, hT3], by simp [hT5, hT4], by simp [hT5, hT4, hT3], by simp [hT5]⟩
  -- 6. the pass loop
  have hN : (encBs (cs.map (cols k))).length ≤ (rf_tokOut ts).length := by rw [hG, hOut]
  obtain ⟨t6, ht6, T6, r6, o1, o2, o3, o4, o5⟩ := rf_mainLoop_runs k (rf_tokOut ts).length m cs
    (by simp [hcs, hm]) hm1 hN T5 hI
  rw [hcs, rf_flatten_single] at o3 o4 o5
  have hoe := rf_encBs_oe G0
  have hG0len : (encBs G0).length = (rf_tokOut ts).length := by rw [hOut]
  refine ⟨_, ?_, T6, seq_runs r1 (seq_runs r2 (seq_runs r3 (seq_runs r4 (seq_runs r5 r6)))),
    o1, o2, o3, by omega, by omega⟩
  have e1 : T1.head 2 = (rf_tokOut ts).length + 1 := by simp [hT1]; omega
  have e2 : T3.head 3 = (encBs (odds G0)).length + 1 := by simp [hT3]; omega
  have e3 : T4.head 4 = (encBs (evens G0)).length + 1 := by simp [hT4, hT3]; omega
  rw [e1, e2, e3]
  rw [hn] at ht1
  generalize Nat.clog 2 m = K at ht6 ⊢
  generalize (rf_tokOut ts).length = L at *
  generalize w.length = n at *
  have hKL := Nat.mul_le_mul_left K hlenO
  nlinarith

end IntMul.Mach.TP

-- ===== TUnriffle =====


/-! # Transpose, unriffle phase: `umain_runs` -/

namespace IntMul.Mach.TP

open IntMul IntMul.Mach IntMul.Mach.MS Sym7

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-! ## List math for the unriffle -/

section UrMath
variable {α : Type}

def ur_il : List α → List α → List α
  | a :: as, b :: bs => a :: b :: ur_il as bs
  | as, [] => as
  | [], bs => bs

theorem ur_il_nil_right (as : List α) : ur_il as [] = as := by
  cases as <;> rfl

theorem ur_il_length : ∀ (as bs : List α), (ur_il as bs).length = as.length + bs.length
  | a :: as, b :: bs => by simp only [ur_il, List.length_cons, ur_il_length as bs]; omega
  | as, [] => by rw [ur_il_nil_right]; simp
  | [], b :: bs => by simp [ur_il]

theorem ur_il_map {β : Type} (f : α → β) : ∀ (as bs : List α),
    (ur_il as bs).map f = ur_il (as.map f) (bs.map f)
  | a :: as, b :: bs => by simp [ur_il, ur_il_map f as bs]
  | as, [] => by simp [ur_il_nil_right]
  | [], b :: bs => by simp [ur_il]

theorem ur_il_append : ∀ (as bs cs ds : List α), as.length = bs.length →
    ur_il (as ++ cs) (bs ++ ds) = ur_il as bs ++ ur_il cs ds
  | a :: as, b :: bs, cs, ds, h => by
    simp only [List.cons_append, ur_il]
    rw [ur_il_append as bs cs ds (by simpa using h)]
  | [], [], cs, ds, _ => by simp [ur_il]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem ur_il_rep (x : α) : ∀ n, ur_il (List.replicate n x) (List.replicate n x) =
    List.replicate (2 * n) x
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [List.replicate_succ, ur_il, ur_il_rep x n]

theorem ur_il_headD (a d : α) (as bs : List α) : (ur_il (a :: as) bs).headD d = a := by
  cases bs <;> rfl

def ur_spl : ℕ → List α → List (List α)
  | 0, l => [l]
  | p + 1, l => ur_il (ur_spl p (odds l)) (ur_spl p (evens l))

theorem ur_spl_length : ∀ (p : ℕ) (l : List α), (ur_spl p l).length = 2 ^ p
  | 0, l => rfl
  | p + 1, l => by
    rw [ur_spl, ur_il_length, ur_spl_length p, ur_spl_length p, pow_succ]; omega

theorem ur_spl_succ : ∀ (p : ℕ) (l : List α),
    (ur_spl p l).map odds ++ (ur_spl p l).map evens = ur_spl (p + 1) l
  | 0, l => rfl
  | p + 1, l => by
    rw [ur_spl, ur_il_map, ur_il_map, ← ur_il_append _ _ _ _ (by simp [ur_spl_length]),
      ur_spl_succ p (odds l), ur_spl_succ p (evens l)]
    rfl

theorem ur_odds_length : ∀ (l : List α), (odds l).length = (l.length + 1) / 2
  | [] => by simp [odds]
  | [a] => by simp [odds]
  | a :: b :: l => by simp [odds, ur_odds_length l]; omega

theorem ur_evens_length : ∀ (l : List α), (evens l).length = l.length / 2
  | [] => by simp [evens]
  | [a] => by simp [evens]
  | a :: b :: l => by simp [evens, ur_evens_length l]; omega

theorem ur_il_singles : ∀ (l : List α) (n : ℕ), l.length ≤ 2 * n →
    ur_il ((odds l).map (fun e => [e]) ++ List.replicate (n - (odds l).length) [])
      ((evens l).map (fun e => [e]) ++ List.replicate (n - (evens l).length) []) =
      l.map (fun e => [e]) ++ List.replicate (2 * n - l.length) []
  | [], n, _ => by simp [odds, evens, ur_il_rep]
  | [a], n, h => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at h; omega⟩
    simp only [odds, evens, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append]
    rw [show n + 1 - (0 + 1) = n by omega, show n + 1 - 0 = n + 1 by omega,
      List.replicate_succ, ur_il, ur_il_rep, show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      List.replicate_succ]
  | a :: b :: l, n, h => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at h; omega⟩
    simp only [odds, evens, List.map_cons, List.length_cons, List.cons_append, ur_il]
    rw [show n + 1 - ((odds l).length + 1) = n - (odds l).length by omega,
      show n + 1 - ((evens l).length + 1) = n - (evens l).length by omega,
      ur_il_singles l n (by simp at h; omega),
      show 2 * (n + 1) - (l.length + 1 + 1) = 2 * n - l.length by omega]

theorem ur_spl_big : ∀ (p : ℕ) (l : List α), l.length ≤ 2 ^ p →
    ur_spl p l = l.map (fun e => [e]) ++ List.replicate (2 ^ p - l.length) []
  | 0, l, h => by
    rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
    · rfl
    · rfl
    · simp at h
  | p + 1, l, h => by
    rw [ur_spl, ur_spl_big p (odds l) (by rw [ur_odds_length]; rw [pow_succ] at h; omega),
      ur_spl_big p (evens l) (by rw [ur_evens_length]; rw [pow_succ] at h; omega),
      ur_il_singles l (2 ^ p) (by rw [pow_succ] at h; omega), pow_succ, Nat.mul_comm]

theorem ur_spl_first : ∀ (p : ℕ) (l : List α), l ≠ [] →
    1 ≤ ((ur_spl p l).headD []).length ∧ (2 ≤ ((ur_spl p l).headD []).length ↔ 2 ^ p < l.length)
  | 0, l, h => by
    simp only [ur_spl, List.headD_cons, pow_zero]
    have := List.length_pos_iff.mpr h
    omega
  | p + 1, l, h => by
    have ho : odds l ≠ [] := by
      intro e; have := congrArg List.length e
      rw [ur_odds_length, List.length_nil] at this; have := List.length_pos_iff.mpr h; omega
    obtain ⟨h1, h2⟩ := ur_spl_first p (odds l) ho
    have hl := ur_spl_length p (odds l)
    obtain ⟨a, as, hA⟩ : ∃ a as, ur_spl p (odds l) = a :: as := by
      rcases hs : ur_spl p (odds l) with _ | ⟨a, as⟩
      · rw [hs] at hl; simp at hl; have := Nat.two_pow_pos p; omega
      · exact ⟨a, as, rfl⟩
    rw [ur_spl, hA, ur_il_headD]
    rw [hA] at h1 h2
    simp only [List.headD_cons] at h1 h2
    refine ⟨h1, ?_⟩
    rw [h2, ur_odds_length, pow_succ]
    omega

end UrMath

/-- The block list after `p` passes. -/
def ur_G (p : ℕ) (rows : List (List Ent)) : List (List (List Ent)) :=
  (List.range (2 ^ p)).map (fun r => rows.map (fun row => (ur_spl p row).getD r []))

def ur_step (G : List (List (List Ent))) : List (List (List Ent)) :=
  G.map (·.map odds) ++ G.map (·.map evens)

theorem ur_G_length (p : ℕ) (rows : List (List Ent)) : (ur_G p rows).length = 2 ^ p := by
  simp [ur_G]

theorem ur_G_zero (rows : List (List Ent)) : ur_G 0 rows = [rows] := by
  simp [ur_G, ur_spl]

theorem ur_G_get (p : ℕ) (rows : List (List Ent)) (i : ℕ) (h : i < (ur_G p rows).length) :
    (ur_G p rows)[i] = rows.map (fun row => (ur_spl p row).getD i []) := by
  simp [ur_G]

theorem ur_step_G (p : ℕ) (rows : List (List Ent)) : ur_step (ur_G p rows) = ur_G (p + 1) rows := by
  have hlen : (ur_step (ur_G p rows)).length = (ur_G (p + 1) rows).length := by
    simp only [ur_step, List.length_append, List.length_map, ur_G_length, pow_succ]; omega
  apply List.ext_getElem hlen
  intro i h1 h2
  have h2' : i < 2 ^ (p + 1) := by rwa [ur_G_length] at h2
  rw [ur_G_get]
  by_cases hi : i < 2 ^ p
  · have e : (ur_step (ur_G p rows))[i] = ((ur_G p rows)[i]'(by rwa [ur_G_length])).map odds := by
      simp only [ur_step]
      rw [List.getElem_append_left (by simp [ur_G_length, hi])]
      simp
    rw [e, ur_G_get, List.map_map]
    apply List.map_congr_left
    intro row _
    have hl := ur_spl_length p row
    rw [← ur_spl_succ, List.getD_append _ _ _ _ (by simp [hl, hi]),
      List.getD_eq_getElem _ _ (by simp [hl, hi])]
    simp only [Function.comp]
    rw [List.getD_eq_getElem _ _ (by simp [hl, hi])]
    simp
  · have e : (ur_step (ur_G p rows))[i] =
        ((ur_G p rows)[i - 2 ^ p]'(by rw [ur_G_length, pow_succ] at *; omega)).map evens := by
      simp only [ur_step]
      rw [List.getElem_append_right (by simp [ur_G_length]; omega)]
      simp [ur_G_length]
    rw [e, ur_G_get, List.map_map]
    apply List.map_congr_left
    intro row _
    have hl := ur_spl_length p row
    rw [pow_succ] at h2'
    rw [← ur_spl_succ, List.getD_append_right _ _ _ _ (by simp [hl]; omega),
      List.getD_eq_getElem _ _ (by simp [hl]; omega)]
    simp only [Function.comp]
    rw [List.getD_eq_getElem _ _ (by simp [hl]; omega)]
    simp [hl]

theorem ur_G_final (k p : ℕ) (rows : List (List Ent)) (hk : k ≤ 2 ^ p)
    (hr : ∀ r ∈ rows, r.length = k) :
    ur_G p rows = ufinal rows.length k (2 ^ p - k) rows := by
  apply List.ext_getElem
  · simp [ur_G, ufinal, cols]; omega
  · intro i h1 h2
    simp only [ur_G, List.getElem_map, List.getElem_range]
    have hrw : rows.map (fun row => (ur_spl p row).getD i []) =
        rows.map (fun row => if i < k then [row.getD i []] else []) := by
      apply List.map_congr_left
      intro row hrow
      rw [ur_spl_big p row (by rw [hr row hrow]; exact hk), hr row hrow]
      by_cases hi : i < k
      · rw [if_pos hi, List.getD_append _ _ _ _ (by simp [hr row hrow, hi]),
          List.getD_eq_getElem _ _ (by simp [hr row hrow, hi]),
          List.getD_eq_getElem _ _ (by simp [hr row hrow, hi])]
        simp
      · rw [if_neg hi, List.getD_append_right _ _ _ _ (by simp [hr row hrow]; omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
    rw [hrw]
    by_cases hi : i < k
    · simp only [hi, if_true]
      simp only [ufinal]
      rw [List.getElem_append_left (by simp [cols]; omega)]
      simp [cols]
    · simp only [hi, if_false]
      simp only [ufinal]
      rw [List.getElem_append_right (by simp [cols]; omega)]
      simp

/-! ## Lengths -/

theorem ur_encE_length (e : Ent) : (encE e).length = e.length + 1 := by
  simp [encE, enc]

theorem ur_encC_length (c : List Ent) :
    (encC c).length = (c.map (fun e => e.length + 1)).sum + 1 := by
  simp [encC, List.length_flatMap, ur_encE_length]

theorem ur_sum_oe {β : Type} (f : β → ℕ) : ∀ (c : List β),
    ((odds c).map f).sum + ((evens c).map f).sum = (c.map f).sum
  | [] => rfl
  | [a] => by simp [odds, evens]
  | a :: b :: c => by
    have := ur_sum_oe f c
    simp only [odds, evens, List.map_cons, List.sum_cons]; omega

theorem ur_encC_oe (c : List Ent) :
    (encC (odds c)).length + (encC (evens c)).length = (encC c).length + 1 := by
  rw [ur_encC_length, ur_encC_length, ur_encC_length]
  have := ur_sum_oe (fun e : Ent => e.length + 1) c
  omega

theorem ur_encB_length (b : List (List Ent)) :
    (encB b).length = (b.map (fun c => (encC c).length)).sum + 1 := by
  simp [encB, List.length_flatMap]

theorem ur_encB_oe (b : List (List Ent)) :
    (encB (b.map odds)).length + (encB (b.map evens)).length = (encB b).length + b.length + 1 := by
  rw [ur_encB_length, ur_encB_length, ur_encB_length]
  induction b with
  | nil => simp
  | cons c b ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have := ur_encC_oe c
    omega

theorem ur_encBs_length (G : List (List (List Ent))) :
    (encBs G).length = (G.map (fun b => (encB b).length)).sum := by
  simp [encBs, List.length_flatMap]

theorem ur_encBs_append (G H : List (List (List Ent))) : encBs (G ++ H) = encBs G ++ encBs H := by
  simp [encBs]

theorem ur_step_length (m : ℕ) (G : List (List (List Ent))) (hG : ∀ b ∈ G, b.length = m) :
    (encBs (ur_step G)).length = (encBs G).length + (m + 1) * G.length := by
  rw [ur_step, ur_encBs_append, List.length_append, ur_encBs_length, ur_encBs_length,
    ur_encBs_length]
  induction G with
  | nil => simp
  | cons b G ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have := ur_encB_oe b
    have hb := hG b (by simp)
    have := ih (fun b' hb' => hG b' (by simp [hb']))
    have e : (m + 1) * (G.length + 1) = (m + 1) * G.length + (m + 1) := by ring
    omega

theorem ur_G_blocks (p : ℕ) (rows : List (List Ent)) : ∀ b ∈ ur_G p rows, b.length = rows.length := by
  intro b hb
  simp only [ur_G, List.mem_map] at hb
  obtain ⟨r, -, rfl⟩ := hb
  simp

theorem ur_G_len (p : ℕ) (rows : List (List Ent)) :
    (encBs (ur_G p rows)).length + (rows.length + 1) = (encB rows).length + (rows.length + 1) * 2 ^ p := by
  induction p with
  | zero => simp [ur_G_zero, encBs]
  | succ p ih =>
    rw [← ur_step_G, ur_step_length rows.length _ (ur_G_blocks p rows), ur_G_length, pow_succ]
    nlinarith

/-! ## Machine operations for the unriffle -/

theorem ur_act1_runs (i : Fin 6) (hi : i.val ≠ 0) (f : (Fin 6 → Sym7) → Fin 6 → Sym7 × Move)
    (s : Sym7) (hs : s ≠ st) (T : Tapes Sym7 6) (F : List Sym7) (hF : F.length ≤ 1)
    (hF' : ∀ x ∈ F, x ≠ st) (hc : T.cells i = tapeOf S7 F) (hh : T.head i = 1)
    (hf : f T.read = wr1 T.read i s Move.stay) :
    Runs st (act f) T 1 ⟨Function.update T.cells i (tapeOf S7 [s]), T.head⟩ := by
  have h1 := act_runs (st := st) f T
  have hT : T.read i ≠ st := by
    simp only [Tapes.read]; rw [hc, hh]; exact tapeOf_ne_st7 F hF' 1 le_rfl
  rw [hf, fix_wr1 _ _ _ _ (Or.inr ⟨hi, hT, hs⟩), write_wr1] at h1
  refine h1.of_eq ?_ rfl
  rw [hc, hh, flag_update F hF]
  congr 1
  funext l; by_cases hl : l = i
  · subst hl; simp [moveHead, hh]
  · simp [hl]

theorem ur_tog_runs (b : Bool) (T : Tapes Sym7 6) (hc : T.cells 4 = tapeOf S7 [bs b])
    (hh : T.head 4 = 1) :
    Runs st tog T 1 ⟨Function.update T.cells 4 (tapeOf S7 [bs (!b)]), T.head⟩ := by
  have hr : T.read 4 = bs b := by simp only [Tapes.read]; rw [hc, hh]; rfl
  refine ur_act1_runs 4 (by decide) _ (bs (!b)) (by cases b <;> decide) T [bs b] (by simp)
    (by intro x hx; simp at hx; subst hx; cases b <;> decide) hc hh ?_
  show wr1 _ 4 (if T.read 4 = zero then one else zero) Move.stay = _
  rw [hr]; cases b <;> rfl

theorem ur_encE_syms (e : Ent) : ∀ x ∈ encE e, x ≠ rend ∧ x ≠ runend ∧ x ≠ blank ∧ x ≠ st := by
  intro x hx
  simp only [encE, enc, List.mem_append, List.mem_map, List.mem_singleton] at hx
  rcases hx with ⟨b, -, rfl⟩ | rfl
  · cases b <;> decide
  · decide

theorem ur_encC_syms (c : List Ent) : ∀ x ∈ encC c, x ≠ runend ∧ x ≠ blank ∧ x ≠ st := by
  intro x hx
  simp only [encC, List.mem_append, List.mem_flatMap, List.mem_singleton] at hx
  rcases hx with ⟨e, -, h⟩ | rfl
  · exact (ur_encE_syms e x h).2
  · decide

theorem ur_encB_syms (b : List (List Ent)) : ∀ x ∈ encB b, x ≠ blank ∧ x ≠ st := by
  intro x hx
  simp only [encB, List.mem_append, List.mem_flatMap, List.mem_singleton] at hx
  rcases hx with ⟨c, -, h⟩ | rfl
  · exact (ur_encC_syms c x h).2
  · decide

theorem ur_encBs_ne_st (G : List (List (List Ent))) : ∀ x ∈ encBs G, x ≠ st := by
  intro x hx
  simp only [encBs, List.mem_flatMap] at hx
  obtain ⟨b, -, h⟩ := hx
  exact (ur_encB_syms b x h).2

theorem ur_first_mem (P W R : List Sym7) (hW : W ≠ []) :
    tapeOf S7 (P ++ W ++ R) (P.length + 1) ∈ W := by
  have := tapeOf_mid7 P W R 0 (List.length_pos_iff.mpr hW)
  rw [Nat.add_zero] at this
  rw [this]; exact List.getElem_mem _

theorem ur_encE_ne (e : Ent) : encE e ≠ [] := by simp [encE]
theorem ur_encC_ne (c : List Ent) : encC c ≠ [] := by simp [encC]
theorem ur_encB_ne (b : List (List Ent)) : encB b ≠ [] := by simp [encB]

theorem ur_enc_length (e : Ent) : (enc e).length = e.length := by simp [enc]
theorem ur_encE_len (e : Ent) : (encE e).length = e.length + 1 := by simp [encE, enc]

theorem ur_isBit_enc (e : Ent) : ∀ x ∈ enc e, isBit x = true := by
  intro x hx; simp only [enc, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx; cases b <;> rfl

set_option maxHeartbeats 1000000 in
theorem ur_uent_runs (q b : Bool) (e : Ent) (T : Tapes Sym7 6) (P R QA : List Sym7)
    (hc2 : T.cells 2 = tapeOf S7 (P ++ encE e ++ R)) (hh2 : T.head 2 = P.length + 1)
    (hc3 : T.cells 3 = tapeOf S7 QA) (hh3 : T.head 3 = QA.length + 1)
    (hc4 : T.cells 4 = tapeOf S7 [bs b]) (hh4 : T.head 4 = 1) :
    Runs st (uent (bs q)) T (e.length + 2)
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ if b = q then encE e else []))) 4 (tapeOf S7 [bs (!b)]),
        Function.update (Function.update T.head 2 (P.length + 1 + (e.length + 1))) 3
          (QA.length + 1 + if b = q then e.length + 1 else 0)⟩ := by
  have hsep : tapeOf S7 (P ++ encE e ++ R) (P.length + 1 + e.length) = sep := by
    rw [show P ++ encE e ++ R = (P ++ enc e) ++ sep :: R by simp [encE],
      show P.length + 1 + e.length = (P ++ enc e).length + 1 by simp [ur_enc_length]; omega,
      tapeOf_at7]
  have hr4 : T.read 4 = bs b := by simp only [Tapes.read]; rw [hc4, hh4]; rfl
  by_cases hb : b = q
  · subst hb
    have h1 := copyW_runs 2 3 (by decide) (by decide) isBit rfl T P (enc e) (sep :: R) QA
      (by rw [hc2]; simp [encE]) hh2 (ur_isBit_enc e) rfl hc3 hh3
    have h2 := cp1_runs 2 3 (by decide) (by decide)
      ⟨Function.update T.cells 3 (tapeOf S7 (QA ++ enc e)),
        Function.update (Function.update T.head 2 (P.length + 1 + (enc e).length)) 3
          (QA.length + 1 + (enc e).length)⟩ sep
      (by simpa [ur_enc_length, hc2] using hsep) (by decide) (QA ++ enc e) (by simp) (by simp; omega)
    have h3 := ur_tog_runs b
      ⟨Function.update (Function.update T.cells 3 (tapeOf S7 (QA ++ enc e))) 3
          (tapeOf S7 (QA ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update (Function.update T.head 2
          (P.length + 1 + (enc e).length)) 3 (QA.length + 1 + (enc e).length)) 2
          ((P.length + 1 + (enc e).length) + 1)) 3 ((QA ++ enc e).length + 2)⟩
      (by simp [hc4]) (by simp [hh4])
    have h := seq_runs (ite_runs_true (c := fun a => decide (a 4 = bs b))
      (P₂ := seq (scanR 2 isBit) (mv 2 Move.right)) (by simp [hr4]) (seq_runs h1 h2)) h3
    refine h.of_eq ?_ (by simp [ur_enc_length])
    simp only [if_true]
    congr 1
    · funext l; fin_cases l <;> simp [encE]
    · funext l; fin_cases l <;> simp [ur_enc_length] <;> omega
  · have h1 := scanR_runs st 2 isBit e.length T
      (fun p hp => by
        rw [hc2, hh2, tapeOf_mid7 P (encE e) R p (by simp [ur_encE_len]; omega)]
        simp only [encE, enc]
        rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_map]
        cases e[p] <;> rfl)
      (by rw [hc2, hh2, hsep]; rfl)
    have h2 := mv_runs st 2 Move.right ⟨T.cells, Function.update T.head 2 (T.head 2 + e.length)⟩
      (by intro h; cases h)
    have h3 := ur_tog_runs b
      ⟨T.cells, Function.update (Function.update T.head 2 (T.head 2 + e.length)) 2
        (moveHead Move.right ((Function.update T.head 2 (T.head 2 + e.length)) 2))⟩
      (by simp [hc4]) (by simp [hh4])
    have h := seq_runs (ite_runs_false (c := fun a => decide (a 4 = bs q))
      (P₁ := seq (copy 2 3 isBit id) (cp1 2 3)) (by simp only [hr4]; cases b <;> cases q <;> (first | decide | exact absurd rfl hb))
      (seq_runs h1 h2)) h3
    refine h.of_eq ?_ (by omega)
    simp only [hb, if_false, List.append_nil]
    congr 1
    · funext l; fin_cases l <;> simp [← hc3]
    · funext l; fin_cases l <;> simp [moveHead, hh2, hh3] <;> omega

/-- Entries selected by a parity sweep starting with parity `b`. -/
def ur_sel (q : Bool) : Bool → List Ent → List Ent
  | _, [] => []
  | b, x :: xs => if b = q then x :: ur_sel q (!b) xs else ur_sel q (!b) xs

def ur_par : Bool → List Ent → Bool
  | b, [] => b
  | b, _ :: xs => ur_par (!b) xs

set_option maxHeartbeats 1000000 in
theorem ur_ents_runs (q : Bool) : ∀ (c : List Ent) (b : Bool) (T : Tapes Sym7 6)
    (P R QA : List Sym7),
    T.cells 2 = tapeOf S7 (P ++ c.flatMap encE ++ rend :: R) → T.head 2 = P.length + 1 →
    T.cells 3 = tapeOf S7 QA → T.head 3 = QA.length + 1 →
    T.cells 4 = tapeOf S7 [bs b] → T.head 4 = 1 →
    Runs st (loop (fun a => decide (a 2 ≠ rend)) (uent (bs q))) T
      ((c.flatMap encE).length + c.length)
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ (ur_sel q b c).flatMap encE))) 4 (tapeOf S7 [bs (ur_par b c)]),
        Function.update (Function.update T.head 2 (P.length + 1 + (c.flatMap encE).length)) 3
          (QA.length + 1 + ((ur_sel q b c).flatMap encE).length)⟩
  | [], b, T, P, R, QA, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have h := loop_stop (st := st) (B := uent (bs q)) (T := T)
      (c := fun a => decide (a 2 ≠ rend)) (by
        simp only [Tapes.read, hc2, hh2, List.flatMap_nil, List.append_nil, tapeOf_at7]; decide)
    refine h.of_eq ?_ rfl
    simp only [ur_sel, ur_par, List.flatMap_nil, List.append_nil, List.length_nil, Nat.add_zero]
    rw [← hc3, ← hc4, ← hh2, ← hh3]
    simp
  | e :: c, b, T, P, R, QA, hc2, hh2, hc3, hh3, hc4, hh4 => by
    have hc2' : T.cells 2 = tapeOf S7 (P ++ encE e ++ (c.flatMap encE ++ rend :: R)) := by
      rw [hc2]; simp
    have h1 := ur_uent_runs q b e T P _ QA hc2' hh2 hc3 hh3 hc4 hh4
    have h2 := ur_ents_runs q c (!b) ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ if b = q then encE e else []))) 4 (tapeOf S7 [bs (!b)]),
        Function.update (Function.update T.head 2 (P.length + 1 + (e.length + 1))) 3
          (QA.length + 1 + if b = q then e.length + 1 else 0)⟩ (P ++ encE e) R
      (QA ++ if b = q then encE e else [])
      (by simp [hc2]) (by simp [ur_encE_len]; omega) (by simp) (by split_ifs <;> simp [ur_encE_len] <;> omega)
      (by simp) (by simp [hh4])
    have hfirst : T.read 2 ≠ rend := by
      have := ur_first_mem P (encE e) (c.flatMap encE ++ rend :: R) (ur_encE_ne e)
      simp only [Tapes.read]; rw [hc2', hh2]
      exact (ur_encE_syms e _ this).1
    have h := loop_iter (c := fun a => decide (a 2 ≠ rend)) (by simpa using hfirst) (by omega) h1 h2
    refine h.of_eq ?_ (by simp [ur_encE_len]; omega)
    by_cases hb : b = q
    · simp only [hb, if_true, ur_sel, ur_par, List.flatMap_cons]
      congr 1
      · funext l; fin_cases l <;> simp
      · funext l; fin_cases l <;> simp [ur_encE_len] <;> omega
    · have hb' : (!b) = q := by cases b <;> cases q <;> simp_all
      simp only [hb, if_false, ur_sel, ur_par, List.append_nil, List.flatMap_cons]
      congr 1
      · funext l; fin_cases l <;> simp
      · funext l; fin_cases l <;> simp [ur_encE_len] <;> omega

theorem ur_flat_len (c : List Ent) : (c.flatMap encE).length = (c.map (fun e => e.length + 1)).sum := by
  simp [List.length_flatMap, ur_encE_len]

theorem ur_len_le_flat (c : List Ent) : c.length ≤ (c.flatMap encE).length := by
  rw [ur_flat_len]
  induction c with
  | nil => simp
  | cons e c ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

theorem ur_encC_len (c : List Ent) : (encC c).length = (c.flatMap encE).length + 1 := by
  simp [encC]

set_option maxHeartbeats 1000000 in
theorem ur_uchunk_runs (q : Bool) (c : List Ent) (T : Tapes Sym7 6) (P R QA F : List Sym7)
    (hF : F.length ≤ 1) (hF' : ∀ x ∈ F, x ≠ st)
    (hc2 : T.cells 2 = tapeOf S7 (P ++ encC c ++ R)) (hh2 : T.head 2 = P.length + 1)
    (hc3 : T.cells 3 = tapeOf S7 QA) (hh3 : T.head 3 = QA.length + 1)
    (hc4 : T.cells 4 = tapeOf S7 F) (hh4 : T.head 4 = 1) :
    Runs st (uchunk (bs q)) T ((encC c).length + c.length + 1)
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ encC (ur_sel q false c)))) 4 (tapeOf S7 [bs (ur_par false c)]),
        Function.update (Function.update T.head 2 (P.length + 1 + (encC c).length)) 3
          (QA.length + 1 + (encC (ur_sel q false c)).length)⟩ := by
  have h1 := ur_act1_runs 4 (by decide) (fun a => wr1 a 4 zero Move.stay) zero (by decide) T F hF hF'
    hc4 hh4 rfl
  have h2 := ur_ents_runs q c false ⟨Function.update T.cells 4 (tapeOf S7 [zero]), T.head⟩ P R QA
    (by simp [hc2, encC]) (by simp [hh2]) (by simp [hc3]) (by simp [hh3]) (by simp; rfl) (by simp [hh4])
  have h3 := cp1_runs 2 3 (by decide) (by decide)
    ⟨Function.update (Function.update (Function.update T.cells 4 (tapeOf S7 [zero])) 3
          (tapeOf S7 (QA ++ (ur_sel q false c).flatMap encE))) 4
          (tapeOf S7 [bs (ur_par false c)]),
        Function.update (Function.update T.head 2 (P.length + 1 + (c.flatMap encE).length)) 3
          (QA.length + 1 + ((ur_sel q false c).flatMap encE).length)⟩ rend
    (by
      simp only [Function.update_apply]
      simp only [show (2 : Fin 6) ≠ 4 by decide, show (2 : Fin 6) ≠ 3 by decide, if_false, if_true]
      rw [hc2, show P ++ encC c ++ R = (P ++ c.flatMap encE) ++ rend :: R by simp [encC],
        show P.length + 1 + (c.flatMap encE).length = (P ++ c.flatMap encE).length + 1 by simp; omega,
        tapeOf_at7])
    (by decide) (QA ++ (ur_sel q false c).flatMap encE) (by simp) (by simp; omega)
  refine (seq_runs h1 (seq_runs h2 h3)).of_eq ?_ (by simp [ur_encC_len]; omega)
  congr 1
  · funext l; fin_cases l <;> simp [encC]
  · funext l; fin_cases l <;> simp [ur_encC_len] <;> omega

set_option maxHeartbeats 1000000 in
theorem ur_cells_runs (q : Bool) : ∀ (b : List (List Ent)) (T : Tapes Sym7 6)
    (P R QA F : List Sym7), F.length ≤ 1 → (∀ x ∈ F, x ≠ st) →
    T.cells 2 = tapeOf S7 (P ++ b.flatMap encC ++ runend :: R) → T.head 2 = P.length + 1 →
    T.cells 3 = tapeOf S7 QA → T.head 3 = QA.length + 1 →
    T.cells 4 = tapeOf S7 F → T.head 4 = 1 →
    ∃ t F', t ≤ 2 * (b.flatMap encC).length ∧ F'.length ≤ 1 ∧ (∀ x ∈ F', x ≠ st) ∧
      Runs st (loop (fun a => decide (a 2 ≠ runend)) (uchunk (bs q))) T t
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ (b.map (ur_sel q false)).flatMap encC))) 4 (tapeOf S7 F'),
        Function.update (Function.update T.head 2 (P.length + 1 + (b.flatMap encC).length)) 3
          (QA.length + 1 + ((b.map (ur_sel q false)).flatMap encC).length)⟩
  | [], T, P, R, QA, F, hF, hF', hc2, hh2, hc3, hh3, hc4, hh4 => by
    have h := loop_stop (st := st) (B := uchunk (bs q)) (T := T)
      (c := fun a => decide (a 2 ≠ runend)) (by
        simp only [Tapes.read, hc2, hh2, List.flatMap_nil, List.append_nil, tapeOf_at7]; decide)
    refine ⟨0, F, le_refl _ |>.trans (Nat.zero_le _), hF, hF', h.of_eq ?_ rfl⟩
    simp only [List.map_nil, List.flatMap_nil, List.append_nil, List.length_nil, Nat.add_zero]
    rw [← hc3, ← hc4, ← hh2, ← hh3]
    simp
  | c :: b, T, P, R, QA, F, hF, hF', hc2, hh2, hc3, hh3, hc4, hh4 => by
    have hc2' : T.cells 2 = tapeOf S7 (P ++ encC c ++ (b.flatMap encC ++ runend :: R)) := by
      rw [hc2]; simp
    have h1 := ur_uchunk_runs q c T P _ QA F hF hF' hc2' hh2 hc3 hh3 hc4 hh4
    obtain ⟨t, F', ht, hF1, hF2, h2⟩ := ur_cells_runs q b
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ encC (ur_sel q false c)))) 4 (tapeOf S7 [bs (ur_par false c)]),
        Function.update (Function.update T.head 2 (P.length + 1 + (encC c).length)) 3
          (QA.length + 1 + (encC (ur_sel q false c)).length)⟩ (P ++ encC c) R
      (QA ++ encC (ur_sel q false c)) [bs (ur_par false c)] (by simp)
      (by intro x hx; simp at hx; subst hx; cases ur_par false c <;> decide)
      (by simp [hc2]) (by simp; omega) (by simp) (by simp; omega) (by simp) (by simp [hh4])
    have hfirst : T.read 2 ≠ runend := by
      have := ur_first_mem P (encC c) (b.flatMap encC ++ runend :: R) (ur_encC_ne c)
      simp only [Tapes.read]; rw [hc2', hh2]
      exact (ur_encC_syms c _ this).1
    have h := loop_iter (c := fun a => decide (a 2 ≠ runend)) (by simpa using hfirst) (by omega) h1 h2
    have hlc := ur_len_le_flat c
    have hcl := ur_encC_len c
    refine ⟨_, F', ?_, hF1, hF2, h.of_eq ?_ rfl⟩
    · simp only [List.flatMap_cons, List.length_append]; omega
    · simp only [List.map_cons, List.flatMap_cons]
      congr 1
      · funext l; fin_cases l <;> simp
      · funext l; fin_cases l <;> simp <;> omega

set_option maxHeartbeats 1000000 in
theorem ur_ublock_runs (q : Bool) (b : List (List Ent)) (T : Tapes Sym7 6)
    (P R QA F : List Sym7) (hF : F.length ≤ 1) (hF' : ∀ x ∈ F, x ≠ st)
    (hc2 : T.cells 2 = tapeOf S7 (P ++ encB b ++ R)) (hh2 : T.head 2 = P.length + 1)
    (hc3 : T.cells 3 = tapeOf S7 QA) (hh3 : T.head 3 = QA.length + 1)
    (hc4 : T.cells 4 = tapeOf S7 F) (hh4 : T.head 4 = 1) :
    ∃ t F', 0 < t ∧ t ≤ 2 * (encB b).length ∧ F'.length ≤ 1 ∧ (∀ x ∈ F', x ≠ st) ∧
      Runs st (ublock (bs q)) T t
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ encB (b.map (ur_sel q false))))) 4 (tapeOf S7 F'),
        Function.update (Function.update T.head 2 (P.length + 1 + (encB b).length)) 3
          (QA.length + 1 + (encB (b.map (ur_sel q false))).length)⟩ := by
  obtain ⟨t, F', ht, hF1, hF2, h1⟩ := ur_cells_runs q b T P R QA F hF hF'
    (by rw [hc2]; simp [encB]) hh2 hc3 hh3 hc4 hh4
  have h2 := cp1_runs 2 3 (by decide) (by decide)
    ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ (b.map (ur_sel q false)).flatMap encC))) 4 (tapeOf S7 F'),
        Function.update (Function.update T.head 2 (P.length + 1 + (b.flatMap encC).length)) 3
          (QA.length + 1 + ((b.map (ur_sel q false)).flatMap encC).length)⟩ runend
    (by
      simp only [Function.update_apply]
      simp only [show (2 : Fin 6) ≠ 4 by decide, show (2 : Fin 6) ≠ 3 by decide, if_false, if_true]
      rw [hc2, show P ++ encB b ++ R = (P ++ b.flatMap encC) ++ runend :: R by simp [encB],
        show P.length + 1 + (b.flatMap encC).length = (P ++ b.flatMap encC).length + 1 by simp; omega,
        tapeOf_at7])
    (by decide) (QA ++ (b.map (ur_sel q false)).flatMap encC) (by simp) (by simp; omega)
  have hBl : (encB b).length = (b.flatMap encC).length + 1 := by simp [encB]
  refine ⟨_, F', by omega, by omega, hF1, hF2, (seq_runs h1 h2).of_eq ?_ rfl⟩
  · congr 1
    · funext l; fin_cases l <;> simp [encB]
    · funext l; fin_cases l <;> simp [encB] <;> omega

set_option maxHeartbeats 1000000 in
theorem ur_usweep_runs (q : Bool) : ∀ (G : List (List (List Ent))) (T : Tapes Sym7 6)
    (P QA F : List Sym7), F.length ≤ 1 → (∀ x ∈ F, x ≠ st) →
    T.cells 2 = tapeOf S7 (P ++ encBs G) → T.head 2 = P.length + 1 →
    T.cells 3 = tapeOf S7 QA → T.head 3 = QA.length + 1 →
    T.cells 4 = tapeOf S7 F → T.head 4 = 1 →
    ∃ t F', t ≤ 2 * (encBs G).length ∧ F'.length ≤ 1 ∧ (∀ x ∈ F', x ≠ st) ∧
      Runs st (usweep (bs q)) T t
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ encBs (G.map (·.map (ur_sel q false)))))) 4 (tapeOf S7 F'),
        Function.update (Function.update T.head 2 (P.length + 1 + (encBs G).length)) 3
          (QA.length + 1 + (encBs (G.map (·.map (ur_sel q false)))).length)⟩
  | [], T, P, QA, F, hF, hF', hc2, hh2, hc3, hh3, hc4, hh4 => by
    have h := loop_stop (st := st) (B := ublock (bs q)) (T := T)
      (c := fun a => decide (a 2 ≠ blank)) (by
        simp only [Tapes.read, hc2, hh2, encBs, List.flatMap_nil, List.append_nil, tapeOf_end7]
        decide)
    refine ⟨0, F, Nat.zero_le _, hF, hF', h.of_eq ?_ rfl⟩
    simp only [encBs, List.map_nil, List.flatMap_nil, List.append_nil, List.length_nil, Nat.add_zero]
    rw [← hc3, ← hc4, ← hh2, ← hh3]
    simp
  | b :: G, T, P, QA, F, hF, hF', hc2, hh2, hc3, hh3, hc4, hh4 => by
    have hc2' : T.cells 2 = tapeOf S7 (P ++ encB b ++ encBs G) := by
      rw [hc2]; simp [encBs]
    obtain ⟨t1, F1, ht0, ht1, hF1, hF1', h1⟩ := ur_ublock_runs q b T P _ QA F hF hF' hc2' hh2 hc3 hh3 hc4 hh4
    obtain ⟨t, F', ht, hF2, hF2', h2⟩ := ur_usweep_runs q G
      ⟨Function.update (Function.update T.cells 3
          (tapeOf S7 (QA ++ encB (b.map (ur_sel q false))))) 4 (tapeOf S7 F1),
        Function.update (Function.update T.head 2 (P.length + 1 + (encB b).length)) 3
          (QA.length + 1 + (encB (b.map (ur_sel q false))).length)⟩ (P ++ encB b)
      (QA ++ encB (b.map (ur_sel q false))) F1 hF1 hF1'
      (by simp [hc2']) (by simp; omega) (by simp) (by simp; omega) (by simp) (by simp [hh4])
    have hfirst : T.read 2 ≠ blank := by
      have := ur_first_mem P (encB b) (encBs G) (ur_encB_ne b)
      simp only [Tapes.read]; rw [hc2', hh2]
      exact (ur_encB_syms b _ this).1
    have h := loop_iter (c := fun a => decide (a 2 ≠ blank)) (by simpa using hfirst) ht0 h1 h2
    refine ⟨_, F', ?_, hF2, hF2', h.of_eq ?_ rfl⟩
    · simp only [encBs, List.flatMap_cons, List.length_append] at ht ⊢; omega
    · simp only [encBs, List.map_cons, List.flatMap_cons]
      congr 1
      · funext l; fin_cases l <;> simp
      · funext l; fin_cases l <;> simp <;> omega

theorem ur_sel_odds : ∀ (l : List Ent), ur_sel false false l = odds l
  | [] => by simp [ur_sel, odds]
  | [a] => by simp [ur_sel, odds]
  | a :: b :: l => by simp [ur_sel, odds, ur_sel_odds l]

theorem ur_sel_evens : ∀ (l : List Ent), ur_sel true false l = evens l
  | [] => by simp [ur_sel, evens]
  | [a] => by simp [ur_sel, evens]
  | a :: b :: l => by simp [ur_sel, evens, ur_sel_evens l]

set_option maxHeartbeats 1000000 in
/-- `ucheck` on a block list whose first cell is `e :: rest`. -/
theorem ur_ucheck_runs (T : Tapes Sym7 6) (e : Ent) (rest : List Ent) (cs : List (List Ent))
    (G : List (List (List Ent))) (F : List Sym7) (hF : F.length ≤ 1) (hF' : ∀ x ∈ F, x ≠ st)
    (hc2 : T.cells 2 = tapeOf S7 (encBs (((e :: rest) :: cs) :: G))) (hh2 : T.head 2 = 1)
    (hc5 : T.cells 5 = tapeOf S7 F) (hh5 : T.head 5 = 1) :
    Runs st ucheck T (2 * e.length + 5)
      ⟨Function.update T.cells 5 (tapeOf S7 [if rest = [] then zero else one]), T.head⟩ := by
  have hW : encBs (((e :: rest) :: cs) :: G) = enc e ++ sep :: (rest.flatMap encE ++
      rend :: (cs.flatMap encC ++ runend :: encBs G)) := by
    simp [encBs, encB, encC, encE]
  have h1 := scanR_runs st 2 isBit e.length T
    (fun p hp => by
      rw [hc2, hh2, hW, Nat.add_comm, tapeOf_succ, List.getD_eq_getElem _ _ (by simp [enc]; omega),
        List.getElem_append_left (by simp [enc]; omega)]
      simp only [enc, List.getElem_map]
      cases e[p] <;> rfl)
    (by
      rw [hc2, hh2, hW, Nat.add_comm, tapeOf_succ, List.getD_eq_getElem _ _ (by simp [enc]),
        List.getElem_append_right (by simp [enc])]
      simp [enc]; rfl)
  have h2 := mv_runs st 2 Move.right ⟨T.cells, Function.update T.head 2 (T.head 2 + e.length)⟩
    (by intro h; cases h)
  have hsym : T.cells 2 (e.length + 2) = rend ↔ rest = [] := by
    rw [hc2, hW, show e.length + 2 = (enc e ++ [sep]).length + 1 by simp [enc],
      show enc e ++ sep :: (rest.flatMap encE ++ rend :: (cs.flatMap encC ++ runend :: encBs G)) =
        (enc e ++ [sep]) ++ (rest.flatMap encE ++ rend :: (cs.flatMap encC ++ runend :: encBs G))
        by simp]
    rcases rest with _ | ⟨e', rest⟩
    · simp only [List.flatMap_nil, List.nil_append, tapeOf_at7]
    · obtain ⟨x, xs, hx⟩ : ∃ x xs, encE e' = x :: xs := by
        cases h : encE e' with
        | nil => exact absurd h (ur_encE_ne e')
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hxr : x ≠ rend := (ur_encE_syms e' x (by rw [hx]; simp)).1
      simp only [List.flatMap_cons, hx, List.cons_append, tapeOf_at7]
      simp [hxr]
  have hs : (if rest = [] then zero else one) ≠ st := by split_ifs <;> decide
  have h3 := ur_act1_runs 5 (by decide)
    (fun a => wr1 a 5 (if a 2 = rend then zero else one) Move.stay)
    (if rest = [] then zero else one) hs
    ⟨T.cells, Function.update (Function.update T.head 2 (T.head 2 + e.length)) 2
      (moveHead Move.right ((Function.update T.head 2 (T.head 2 + e.length)) 2))⟩ F hF hF'
    (by simp [hc5]) (by simp [hh5])
    (by
      simp only [Tapes.read, Function.update_self, moveHead, hh2]
      rw [show 1 + e.length + 1 = e.length + 2 by omega]
      by_cases hr : rest = []
      · simp [hr, hsym.mpr hr]
      · rw [if_neg (fun h => hr (hsym.mp h)), if_neg hr])
  have h4 := rewind_runs 2
    ⟨Function.update T.cells 5 (tapeOf S7 [if rest = [] then zero else one]),
      Function.update (Function.update T.head 2 (T.head 2 + e.length)) 2
      (moveHead Move.right ((Function.update T.head 2 (T.head 2 + e.length)) 2))⟩
    (encBs (((e :: rest) :: cs) :: G)) (ur_encBs_ne_st _) (by simp [hc2])
  refine (seq_runs h1 (seq_runs h2 (seq_runs h3 h4))).of_eq ?_ (by simp [moveHead, hh2]; omega)
  congr 1
  funext l; fin_cases l <;> simp [hh2]

/-! ## Input conversion -/

def ur_rowU : List Ent → ℕ → List (Ent × ℕ)
  | [], _ => []
  | [e], t => [(e, t)]
  | e :: e' :: r, t => (e, 1) :: ur_rowU (e' :: r) t

def ur_units : List (List Ent) → List (Ent × ℕ)
  | [] => []
  | [r] => ur_rowU r 0
  | r :: r' :: rs => ur_rowU r 2 ++ ur_units (r' :: rs)

def ur_inU (U : List (Ent × ℕ)) : List (Option Bool) :=
  U.flatMap (fun u => bits u.1 ++ List.replicate u.2 none)

def ur_outU (U : List (Ent × ℕ)) : List Sym7 :=
  U.flatMap (fun u => encE u.1 ++ if u.2 = 1 then [] else [rend])

def ur_WF : List (Ent × ℕ) → Prop
  | [] => False
  | [u] => u.1 ≠ [] ∧ u.2 = 0
  | u :: v :: U => u.1 ≠ [] ∧ (u.2 = 1 ∨ u.2 = 2) ∧ ur_WF (v :: U)

theorem ur_inU_rowU : ∀ (r : List Ent) (t : ℕ), r ≠ [] →
    ur_inU (ur_rowU r t) = joinSep (r.map bits) ++ List.replicate t none
  | [], _, h => absurd rfl h
  | [e], t, _ => by simp [ur_rowU, ur_inU, joinSep]
  | e :: e' :: r, t, _ => by
    have := ur_inU_rowU (e' :: r) t (by simp)
    simp only [ur_inU] at this
    simp only [ur_rowU, ur_inU, List.flatMap_cons, this, joinSep, List.map_cons,
      List.intercalate_cons_cons]
    simp

theorem ur_outU_rowU : ∀ (r : List Ent) (t : ℕ), r ≠ [] → t ≠ 1 →
    ur_outU (ur_rowU r t) = encC r
  | [], _, h, _ => absurd rfl h
  | [e], t, _, ht => by simp [ur_rowU, ur_outU, encC, ht]
  | e :: e' :: r, t, _, ht => by
    have := ur_outU_rowU (e' :: r) t (by simp) ht
    simp only [ur_outU] at this
    simp only [ur_rowU, ur_outU, List.flatMap_cons, this, encC]
    simp

theorem ur_inU_units : ∀ (rows : List (List Ent)), (∀ r ∈ rows, r ≠ []) →
    ur_inU (ur_units rows) = encIn rows
  | [], _ => rfl
  | [r], h => by
    rw [ur_units, ur_inU_rowU r 0 (h r (by simp))]; simp [encIn]
  | r :: r' :: rs, h => by
    rw [ur_units, ur_inU, List.flatMap_append, ← ur_inU, ← ur_inU,
      ur_inU_units (r' :: rs) (fun x hx => h x (by simp [hx])), ur_inU_rowU r 2 (h r (by simp))]
    simp [encIn, List.intercalate_cons_cons]

theorem ur_outU_units : ∀ (rows : List (List Ent)), (∀ r ∈ rows, r ≠ []) →
    ur_outU (ur_units rows) = rows.flatMap encC
  | [], _ => rfl
  | [r], h => by
    rw [ur_units, ur_outU_rowU r 0 (h r (by simp)) (by decide)]; simp
  | r :: r' :: rs, h => by
    rw [ur_units, ur_outU, List.flatMap_append, ← ur_outU, ← ur_outU,
      ur_outU_units (r' :: rs) (fun x hx => h x (by simp [hx])),
      ur_outU_rowU r 2 (h r (by simp)) (by decide)]
    simp

theorem ur_mem_rowU : ∀ (r : List Ent) (t : ℕ) (u : Ent × ℕ), u ∈ ur_rowU r t →
    u.1 ∈ r ∧ (u.2 = 1 ∨ u.2 = t)
  | [], _, _, h => by simp [ur_rowU] at h
  | [e], t, u, h => by simp [ur_rowU] at h; subst h; simp
  | e :: e' :: r, t, u, h => by
    simp only [ur_rowU, List.mem_cons] at h
    rcases h with h | h
    · subst h; simp
    · have := ur_mem_rowU (e' :: r) t u (by simpa using h)
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem ur_WF_rowU : ∀ (r : List Ent), r ≠ [] → (∀ e ∈ r, e ≠ []) → ur_WF (ur_rowU r 0)
  | [], h, _ => absurd rfl h
  | [e], _, he => by simp [ur_rowU, ur_WF, he e (by simp)]
  | e :: e' :: r, _, he => by
    have := ur_WF_rowU (e' :: r) (by simp) (fun x hx => he x (by simp [hx]))
    rcases hr : r with _ | ⟨e'', r'⟩
    · subst hr
      simp only [ur_rowU, ur_WF] at this ⊢
      exact ⟨he e (by simp), by simp, this⟩
    · subst hr
      simp only [ur_rowU] at this ⊢
      exact ⟨he e (by simp), by simp, this⟩

theorem ur_WF_append : ∀ (A B : List (Ent × ℕ)), A ≠ [] →
    (∀ u ∈ A, u.1 ≠ [] ∧ (u.2 = 1 ∨ u.2 = 2)) → ur_WF B → ur_WF (A ++ B)
  | [], _, h, _, _ => absurd rfl h
  | [u], B, _, hA, hB => by
    rcases B with _ | ⟨v, B⟩
    · exact absurd hB id
    · exact ⟨(hA u (by simp)).1, (hA u (by simp)).2, hB⟩
  | u :: u' :: A, B, _, hA, hB => by
    have := ur_WF_append (u' :: A) B (by simp) (fun x hx => hA x (by simp [hx])) hB
    exact ⟨(hA u (by simp)).1, (hA u (by simp)).2, this⟩

theorem ur_WF_units : ∀ (rows : List (List Ent)), rows ≠ [] → (∀ r ∈ rows, r ≠ []) →
    (∀ r ∈ rows, ∀ e ∈ r, e ≠ []) → ur_WF (ur_units rows)
  | [], h, _, _ => absurd rfl h
  | [r], _, h1, h2 => ur_WF_rowU r (h1 r (by simp)) (h2 r (by simp))
  | r :: r' :: rs, _, h1, h2 => by
    rw [ur_units]
    apply ur_WF_append
    · intro h
      have : ur_rowU r 2 = [] := h
      rcases r with _ | ⟨e, _ | ⟨e', r⟩⟩
      · exact h1 [] (by simp) rfl
      · simp [ur_rowU] at this
      · simp [ur_rowU] at this
    · intro u hu
      have := ur_mem_rowU r 2 u hu
      exact ⟨h2 r (by simp) u.1 this.1, this.2⟩
    · exact ur_WF_units (r' :: rs) (by simp) (fun x hx => h1 x (by simp [hx]))
        (fun x hx => h2 x (by simp [hx]))

theorem ur_letters (e : Ent) (n : ℕ) :
    (bits e ++ List.replicate n none).map letter = enc e ++ List.replicate n sep := by
  simp [bits, enc, letter, Function.comp_def]

theorem ur_bs_ne (b : Bool) : bs b ≠ sep ∧ bs b ≠ blank ∧ bs b ≠ st := by
  cases b <;> decide

set_option maxHeartbeats 2000000 in
theorem ur_cstep_runs (e : Ent) (n : ℕ) (hn : n ≤ 2) (T : Tapes Sym7 6)
    (P R Q : List Sym7) (hR : n = 0 → R = [])
    (hR' : 1 ≤ n → ∃ x R', R = x :: R' ∧ x ≠ sep ∧ x ≠ blank)
    (hc0 : T.cells 0 = tapeOf S7 (P ++ enc e ++ List.replicate n sep ++ R))
    (hh0 : T.head 0 = P.length + 1)
    (hc2 : T.cells 2 = tapeOf S7 Q) (hh2 : T.head 2 = Q.length + 1) :
    Runs st uconvStep T (e.length + 2 + (if n = 2 then 2 else 0))
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encE e ++ if n = 1 then [] else [rend])),
        Function.update (Function.update T.head 0 (P.length + 1 + e.length + n)) 2
          (Q.length + 1 + (e.length + 1) + if n = 1 then 0 else 1)⟩ := by
  have hsym : ∀ j, T.cells 0 (P.length + 1 + e.length + j) =
      (List.replicate n sep ++ R).getD j blank := by
    intro j
    rw [hc0, show P.length + 1 + e.length + j = (P ++ enc e).length + j + 1 by
      simp [ur_enc_length]; omega, tapeOf_succ, List.append_assoc (P ++ enc e),
      List.getD_append_right _ _ _ _ (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl
  have h1 := copyW_runs 0 2 (by decide) (by decide) isBit rfl T P (enc e)
    (List.replicate n sep ++ R) Q (by rw [hc0]; simp) hh0 (ur_isBit_enc e) ?hb hc2 hh2
  case hb =>
    rcases n with _ | n
    · rw [hR rfl]; rfl
    · rfl
  rw [ur_enc_length] at h1
  have h2 := wsym_runs 2 (by decide) sep (by decide)
    ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ enc e)),
      Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
        (Q.length + 1 + e.length)⟩ (Q ++ enc e) (by simp) (by simp [ur_enc_length]; omega)
  have hr0 : ∀ j, (Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
      (tapeOf S7 (Q ++ enc e ++ [sep]))) 0 (P.length + 1 + e.length + j) =
      (List.replicate n sep ++ R).getD j blank := by
    intro j; simp [hsym]
  have hlenE : (encE e).length = e.length + 1 := ur_encE_len e
  interval_cases n
  · -- end of the input
    have h3 := wsym_runs 2 (by decide) rend (by decide)
      ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
          (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)⟩ (Q ++ enc e ++ [sep])
      (by simp) (by simp [ur_enc_length]; omega)
    have hc : (fun a : Fin 6 → Sym7 => decide (a 0 = sep))
        (Tapes.read ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
          (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)⟩) = false := by
      have := hr0 0
      simp only [Tapes.read, Nat.add_zero] at this ⊢
      simp only [Function.update_apply, show (0 : Fin 6) ≠ 2 by decide, if_false, if_true] at this ⊢
      rw [this, hR rfl]; rfl
    refine (seq_runs h1 (seq_runs h2 (ite_runs_false hc h3))).of_eq ?_ (by simp)
    congr 1
    · funext l; fin_cases l <;> simp [encE]
    · funext l; fin_cases l <;> simp [ur_enc_length] <;> omega
  · -- entry separator
    obtain ⟨x, R', rfl, hx1, hx2⟩ := hR' le_rfl
    have h3 := mv_runs st 0 Move.right
      ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
          (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)⟩ (by intro h; cases h)
    have hc : (fun a : Fin 6 → Sym7 => decide (a 0 = sep))
        (Tapes.read ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
          (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)⟩) = true := by
      have := hr0 0
      simp only [Tapes.read, Nat.add_zero] at this ⊢
      simp only [Function.update_apply, show (0 : Fin 6) ≠ 2 by decide, if_false, if_true] at this ⊢
      rw [this]; rfl
    have hc' : (fun a : Fin 6 → Sym7 => decide (a 0 = sep))
        (Tapes.read ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update (Function.update T.head 0
          (P.length + 1 + e.length)) 2 (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)) 0
          (moveHead Move.right (P.length + 1 + e.length))⟩) = false := by
      have := hr0 1
      simp only [Tapes.read, moveHead] at this ⊢
      simp only [Function.update_apply, show (0 : Fin 6) ≠ 2 by decide, if_false, if_true] at this ⊢
      rw [this]; simpa using hx1
    have h3' := seq_runs h3 (ite_runs_false (c := fun a => decide (a 0 = sep))
      (P₁ := seq (mv 0 Move.right) (wsym 2 rend)) hc' (skip_runs _))
    refine (seq_runs h1 (seq_runs h2 (ite_runs_true (c := fun a => decide (a 0 = sep)) (P₂ := wsym 2 rend) hc h3'))).of_eq ?_ ?_
    rotate_left
    · simp
    congr 1
    · funext l; fin_cases l <;> simp [encE]
    · funext l; fin_cases l <;> simp [ur_enc_length, moveHead] <;> omega
  · -- row separator
    have h3 := mv_runs st 0 Move.right
      ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
          (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)⟩ (by intro h; cases h)
    have h4 := mv_runs st 0 Move.right
      ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update (Function.update T.head 0
          (P.length + 1 + e.length)) 2 (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)) 0
          (moveHead Move.right (P.length + 1 + e.length))⟩ (by intro h; cases h)
    have h5 := wsym_runs 2 (by decide) rend (by decide)
      ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update (Function.update (Function.update T.head 0
          (P.length + 1 + e.length)) 2 (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)) 0
          (moveHead Move.right (P.length + 1 + e.length))) 0
          (moveHead Move.right (moveHead Move.right (P.length + 1 + e.length)))⟩
      (Q ++ enc e ++ [sep]) (by simp) (by simp [ur_enc_length]; omega)
    have hc : (fun a : Fin 6 → Sym7 => decide (a 0 = sep))
        (Tapes.read ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update T.head 0 (P.length + 1 + e.length)) 2
          (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)⟩) = true := by
      have := hr0 0
      simp only [Tapes.read, Nat.add_zero] at this ⊢
      simp only [Function.update_apply, show (0 : Fin 6) ≠ 2 by decide, if_false, if_true] at this ⊢
      rw [this]; rfl
    have hc' : (fun a : Fin 6 → Sym7 => decide (a 0 = sep))
        (Tapes.read ⟨Function.update (Function.update T.cells 2 (tapeOf S7 (Q ++ enc e))) 2
          (tapeOf S7 (Q ++ enc e ++ [sep])),
        Function.update (Function.update (Function.update (Function.update T.head 0
          (P.length + 1 + e.length)) 2 (Q.length + 1 + e.length)) 2 ((Q ++ enc e).length + 2)) 0
          (moveHead Move.right (P.length + 1 + e.length))⟩) = true := by
      have := hr0 1
      simp only [Tapes.read, moveHead] at this ⊢
      simp only [Function.update_apply, show (0 : Fin 6) ≠ 2 by decide, if_false, if_true] at this ⊢
      rw [this]; rfl
    have h3' := seq_runs h3 (ite_runs_true (c := fun a => decide (a 0 = sep)) (P₂ := skip) hc' (seq_runs h4 h5))
    refine (seq_runs h1 (seq_runs h2 (ite_runs_true (c := fun a => decide (a 0 = sep)) (P₂ := wsym 2 rend) hc h3'))).of_eq ?_ ?_
    rotate_left
    · simp
    congr 1
    · funext l; fin_cases l <;> simp [encE]
    · funext l; fin_cases l <;> simp [ur_enc_length, moveHead] <;> omega

theorem ur_inU_cons (u : Ent × ℕ) (V : List (Ent × ℕ)) :
    (ur_inU (u :: V)).map letter = enc u.1 ++ List.replicate u.2 sep ++ (ur_inU V).map letter := by
  rw [ur_inU, List.flatMap_cons, List.map_append, ← ur_inU, ur_letters]

theorem ur_inU_cons_len (u : Ent × ℕ) (V : List (Ent × ℕ)) :
    (ur_inU (u :: V)).length = u.1.length + u.2 + (ur_inU V).length := by
  simp [ur_inU, bits]; omega

theorem ur_outU_cons (u : Ent × ℕ) (V : List (Ent × ℕ)) :
    ur_outU (u :: V) = (encE u.1 ++ if u.2 = 1 then [] else [rend]) ++ ur_outU V := by
  simp [ur_outU]

set_option maxHeartbeats 2000000 in
theorem ur_conv_loop : ∀ (U : List (Ent × ℕ)), ur_WF U → ∀ (T : Tapes Sym7 6) (P Q : List Sym7),
    T.cells 0 = tapeOf S7 (P ++ (ur_inU U).map letter) → T.head 0 = P.length + 1 →
    T.cells 2 = tapeOf S7 Q → T.head 2 = Q.length + 1 →
    ∃ t ≤ 3 * (ur_inU U).length, Runs st (loop (fun a => decide (a 0 ≠ blank)) uconvStep) T t
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ ur_outU U)),
       Function.update (Function.update T.head 0 (P.length + 1 + (ur_inU U).length)) 2
         (Q.length + 1 + (ur_outU U).length)⟩
  | [], h => h.elim
  | [u], h => by
    intro T P Q hc0 hh0 hc2 hh2
    obtain ⟨he, hn⟩ := h
    obtain ⟨e, n⟩ := u
    simp only at he hn
    subst hn
    have hc0' : T.cells 0 = tapeOf S7 (P ++ enc e ++ List.replicate 0 sep ++ []) := by
      rw [hc0, ur_inU_cons]; simp [ur_inU]
    have h1 := ur_cstep_runs e 0 (by omega) T P [] Q (fun _ => rfl) (by omega) hc0' hh0 hc2 hh2
    obtain ⟨b, e', rfl⟩ : ∃ b e', e = b :: e' := by
      cases e with
      | nil => exact absurd rfl he
      | cons b e' => exact ⟨b, e', rfl⟩
    have hstart : T.read 0 ≠ blank := by
      simp only [Tapes.read]; rw [hc0', hh0]
      simp only [enc, List.map_cons, List.cons_append, List.append_assoc, tapeOf_at7]
      exact (ur_bs_ne b).2.1
    have hstop := loop_stop (st := st) (B := uconvStep) (c := fun a => decide (a 0 ≠ blank))
      (T := ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encE (b :: e') ++ if 0 = 1 then [] else [rend])),
        Function.update (Function.update T.head 0 (P.length + 1 + (b :: e').length + 0)) 2
          (Q.length + 1 + ((b :: e').length + 1) + if 0 = 1 then 0 else 1)⟩) (by
        simp only [Tapes.read, Function.update_apply, show (0 : Fin 6) ≠ 2 by decide, if_false,
          if_true, hc0']
        rw [show P.length + 1 + (b :: e').length + 0 = (P ++ enc (b :: e') ++
          List.replicate 0 sep ++ []).length + 1 by simp [enc]; omega, tapeOf_end7]
        decide)
    refine ⟨_, ?_, (loop_iter (c := fun a => decide (a 0 ≠ blank)) (by simpa using hstart)
      (by omega) h1 hstop).of_eq ?_ rfl⟩
    · simp [ur_inU, bits]; omega
    · simp only [ur_outU, ur_inU, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      congr 1
      · funext l; fin_cases l <;> simp
      · funext l; fin_cases l <;> simp [bits, ur_encE_len] <;> omega
  | u :: v :: U, h => by
    intro T P Q hc0 hh0 hc2 hh2
    obtain ⟨he, hn, hWF⟩ := h
    obtain ⟨e, n⟩ := u
    simp only at he hn
    have hv : v.1 ≠ [] := by
      rcases U with _ | ⟨w, U⟩
      · exact hWF.1
      · exact hWF.1
    obtain ⟨c, e'', hc⟩ : ∃ c e'', v.1 = c :: e'' := by
      rcases h' : v.1 with _ | ⟨c, e''⟩
      · exact absurd h' hv
      · exact ⟨c, e'', rfl⟩
    have hR : (ur_inU (v :: U)).map letter = bs c :: (enc e'' ++ List.replicate v.2 sep ++
        (ur_inU U).map letter) := by
      rw [ur_inU_cons, hc]; simp [enc]
    have hc0' : T.cells 0 = tapeOf S7 (P ++ enc e ++ List.replicate n sep ++
        (ur_inU (v :: U)).map letter) := by
      rw [hc0, ur_inU_cons]; simp
    have h1 := ur_cstep_runs e n (by omega) T P _ Q (by omega)
      (fun _ => ⟨_, _, hR, (ur_bs_ne c).1, (ur_bs_ne c).2.1⟩) hc0' hh0 hc2 hh2
    obtain ⟨t, ht, h2⟩ := ur_conv_loop (v :: U) hWF
      ⟨Function.update T.cells 2 (tapeOf S7 (Q ++ encE e ++ if n = 1 then [] else [rend])),
        Function.update (Function.update T.head 0 (P.length + 1 + e.length + n)) 2
          (Q.length + 1 + (e.length + 1) + if n = 1 then 0 else 1)⟩
      (P ++ enc e ++ List.replicate n sep) (Q ++ encE e ++ if n = 1 then [] else [rend])
      (by simp [hc0'])
      (by simp [ur_enc_length]; omega)
      (by simp)
      (by simp [ur_encE_len]; split_ifs <;> simp <;> omega)
    obtain ⟨b, e', rfl⟩ : ∃ b e', e = b :: e' := by
      cases e with
      | nil => exact absurd rfl he
      | cons b e' => exact ⟨b, e', rfl⟩
    have hstart : T.read 0 ≠ blank := by
      simp only [Tapes.read]; rw [hc0', hh0]
      simp only [enc, List.map_cons, List.cons_append, List.append_assoc, tapeOf_at7]
      exact (ur_bs_ne b).2.1
    have h := loop_iter (c := fun a => decide (a 0 ≠ blank)) (by simpa using hstart) (by omega) h1 h2
    have hlen := ur_inU_cons_len (b :: e', n) (v :: U)
    refine ⟨_, ?_, h.of_eq ?_ rfl⟩
    · simp only at hlen; rw [hlen]; split_ifs <;> simp at * <;> omega
    · congr 1
      · funext l; fin_cases l <;> simp [ur_outU_cons]
      · funext l; fin_cases l <;> simp [hlen, ur_enc_length, ur_outU_cons] <;> omega

theorem ur_encBs_ne_blank (G : List (List (List Ent))) : ∀ x ∈ encBs G, x ≠ blank := by
  intro x hx
  simp only [encBs, List.mem_flatMap] at hx
  obtain ⟨b, -, h⟩ := hx
  exact (ur_encB_syms b x h).1

/-- A state that differs from `T` on tapes `2`, `3`, `4` (and heads `2`, `3`) only. -/
def ur_S (T : Tapes Sym7 6) (c2 c3 F4 : List Sym7) (h2 h3 : ℕ) : Tapes Sym7 6 :=
  ⟨Function.update (Function.update (Function.update T.cells 2 (tapeOf S7 c2)) 3 (tapeOf S7 c3)) 4
    (tapeOf S7 F4), Function.update (Function.update T.head 2 h2) 3 h3⟩

set_option maxHeartbeats 4000000 in
theorem ur_upass_runs (G : List (List (List Ent))) (e : Ent) (rest : List Ent)
    (cs : List (List Ent)) (G' : List (List (List Ent)))
    (hfc : ur_step G = ((e :: rest) :: cs) :: G') (T : Tapes Sym7 6)
    (F4 : List Sym7) (hF4 : F4.length ≤ 1) (hF4' : ∀ x ∈ F4, x ≠ st) (hh4 : T.head 4 = 1)
    (F5 : List Sym7) (hF5 : F5.length ≤ 1) (hF5' : ∀ x ∈ F5, x ≠ st)
    (hc5 : T.cells 5 = tapeOf S7 F5) (hh5 : T.head 5 = 1) :
    ∃ t ≤ 6 * (encBs G).length + 6 * (encBs (ur_step G)).length + 15, ∃ F, 0 < t ∧
      F.length ≤ 1 ∧ (∀ x ∈ F, x ≠ st) ∧
      Runs st upass (ur_S T (encBs G) [] F4 1 1) t
        ⟨Function.update (ur_S T (encBs (ur_step G)) [] F 1 1).cells 5
          (tapeOf S7 [if rest = [] then zero else one]), (ur_S T (encBs (ur_step G)) [] F 1 1).head⟩ := by
  have hodds : G.map (·.map (ur_sel false false)) = G.map (·.map odds) := by
    congr 1; funext b; congr 1; funext c; exact ur_sel_odds c
  have hevens : G.map (·.map (ur_sel true false)) = G.map (·.map evens) := by
    congr 1; funext b; congr 1; funext c; exact ur_sel_evens c
  have hW : encBs (ur_step G) = encBs (G.map (·.map odds)) ++ encBs (G.map (·.map evens)) := by
    rw [ur_step, ur_encBs_append]
  have hWl : (encBs (ur_step G)).length =
      (encBs (G.map (·.map odds))).length + (encBs (G.map (·.map evens))).length := by
    rw [hW, List.length_append]
  -- a. odds to `A`
  obtain ⟨ta, Fa, hta, hFa, hFa', ra⟩ := ur_usweep_runs false G (ur_S T (encBs G) [] F4 1 1)
    [] [] F4 hF4 hF4' (by simp [ur_S]) (by simp [ur_S]) (by simp [ur_S]) (by simp [ur_S])
    (by simp [ur_S]) (by simp [ur_S, hh4])
  rw [hodds] at ra
  have ra' : Runs st (usweep zero) (ur_S T (encBs G) [] F4 1 1) ta
      (ur_S T (encBs G) (encBs (G.map (·.map odds))) Fa ((encBs G).length + 1)
        ((encBs (G.map (·.map odds))).length + 1)) := by
    refine ra.of_eq ?_ rfl
    simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp <;> omega
  -- b. rewind `C`
  have rb := (rewind_runs 2 (ur_S T (encBs G) (encBs (G.map (·.map odds))) Fa
      ((encBs G).length + 1) ((encBs (G.map (·.map odds))).length + 1)) (encBs G)
      (ur_encBs_ne_st G) (by simp [ur_S])).of_eq
    (T'' := ur_S T (encBs G) (encBs (G.map (·.map odds))) Fa 1
        ((encBs (G.map (·.map odds))).length + 1))
    (by simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp) rfl
  -- c. evens to `A`
  obtain ⟨tc, Fc, htc, hFc, hFc', rc⟩ := ur_usweep_runs true G
    (ur_S T (encBs G) (encBs (G.map (·.map odds))) Fa 1 ((encBs (G.map (·.map odds))).length + 1))
    [] (encBs (G.map (·.map odds))) Fa hFa hFa'
    (by simp [ur_S]) (by simp [ur_S]) (by simp [ur_S]) (by simp [ur_S]) (by simp [ur_S])
    (by simp [ur_S, hh4])
  rw [hevens, ← hW] at rc
  have rc' : Runs st (usweep one) (ur_S T (encBs G) (encBs (G.map (·.map odds))) Fa 1
      ((encBs (G.map (·.map odds))).length + 1)) tc
      (ur_S T (encBs G) (encBs (ur_step G)) Fc ((encBs G).length + 1)
        ((encBs (ur_step G)).length + 1)) := by
    refine rc.of_eq ?_ rfl
    simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp <;> omega
  -- d. wipe `C`
  have rd := (wipe_runs 2 (by decide) (ur_S T (encBs G) (encBs (ur_step G)) Fc
      ((encBs G).length + 1) ((encBs (ur_step G)).length + 1)) (encBs G) (ur_encBs_ne_st G)
      (by simp [ur_S]) (by simp [ur_S])).of_eq
    (T'' := ur_S T [] (encBs (ur_step G)) Fc 1 ((encBs (ur_step G)).length + 1))
    (by simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp) rfl
  -- e. rewind `A`
  have re := (rewind_runs 3 (ur_S T [] (encBs (ur_step G)) Fc 1 ((encBs (ur_step G)).length + 1))
      (encBs (ur_step G)) (ur_encBs_ne_st _) (by simp [ur_S])).of_eq
    (T'' := ur_S T [] (encBs (ur_step G)) Fc 1 1)
    (by simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp) rfl
  -- f. copy `A` to `C`
  have rf := (copy_runs' 3 2 (by decide) (by decide) notBlank id (encBs (ur_step G)) []
      (ur_S T [] (encBs (ur_step G)) Fc 1 1) (fun x hx => ur_encBs_ne_st _ x hx)
      (fun p hp => by
        simp [ur_S]
        rw [Nat.add_comm, tapeOf_get7 _ _ hp])
      (fun x hx => by
        have := ur_encBs_ne_blank _ x hx
        cases x <;> simp_all [notBlank])
      (by simp [ur_S]; rw [Nat.add_comm, tapeOf_end7]; rfl)
      (by simp [ur_S]) (by simp [ur_S])).of_eq
    (T'' := ur_S T (encBs (ur_step G)) (encBs (ur_step G)) Fc ((encBs (ur_step G)).length + 1)
      ((encBs (ur_step G)).length + 1))
    (by simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp <;> omega) rfl
  -- g. wipe `A`
  have rg := (wipe_runs 3 (by decide) (ur_S T (encBs (ur_step G)) (encBs (ur_step G)) Fc
      ((encBs (ur_step G)).length + 1) ((encBs (ur_step G)).length + 1)) (encBs (ur_step G))
      (ur_encBs_ne_st _) (by simp [ur_S]) (by simp [ur_S])).of_eq
    (T'' := ur_S T (encBs (ur_step G)) [] Fc ((encBs (ur_step G)).length + 1) 1)
    (by simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp) rfl
  -- h. rewind `C`
  have rh := (rewind_runs 2 (ur_S T (encBs (ur_step G)) [] Fc ((encBs (ur_step G)).length + 1) 1)
      (encBs (ur_step G)) (ur_encBs_ne_st _) (by simp [ur_S])).of_eq
    (T'' := ur_S T (encBs (ur_step G)) [] Fc 1 1)
    (by simp only [ur_S]; congr 1 <;> funext l <;> fin_cases l <;> simp) rfl
  -- i. check
  have ri := ur_ucheck_runs (ur_S T (encBs (ur_step G)) [] Fc 1 1) e rest cs G' F5 hF5 hF5'
    (by simp [ur_S, hfc]) (by simp [ur_S]) (by simp [ur_S, hc5]) (by simp [ur_S, hh5])
  have hel : e.length + 1 ≤ (encBs (ur_step G)).length := by
    rw [hfc]; simp [encBs, encB, encC, encE, enc]
  refine ⟨_, ?_, Fc, by omega, hFc, hFc', seq_runs ra' (seq_runs rb (seq_runs rc' (seq_runs rd
    (seq_runs re (seq_runs rf (seq_runs rg (seq_runs rh ri)))))))⟩
  simp only [ur_S, Function.update_self, Function.update_of_ne (show (2 : Fin 6) ≠ 3 by decide)]
  omega

theorem ur_intercalate_len {β : Type} (s : List β) (a : ℕ) : ∀ (L : List (List β)), L ≠ [] →
    (∀ x ∈ L, x.length = a) → (List.intercalate s L).length + s.length = L.length * (a + s.length)
  | [], h, _ => absurd rfl h
  | [x], _, h => by simp [h x (by simp)]
  | x :: y :: L, _, h => by
    have := ur_intercalate_len s a (y :: L) (by simp) (fun z hz => h z (by simp [hz]))
    rw [List.intercalate_cons_cons]
    simp only [List.length_append, List.length_cons] at this ⊢
    rw [h x (by simp)]
    rw [Nat.succ_mul, ← this]
    simp [List.intercalate]
    omega

theorem ur_encIn_len (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) :
    (encIn rows).length + 2 = m * (k * (ℓ + 1) + 1) := by
  obtain ⟨hlen, hm, hk, hl, hr⟩ := hs
  have hrow : ∀ r ∈ rows, (joinSep (r.map bits)).length + 1 = k * (ℓ + 1) := by
    intro r hr'
    have := ur_intercalate_len [none] ℓ (r.map bits)
      (by intro h; have := (hr r hr').1; rw [List.map_eq_nil_iff] at h; subst h; simp at this; omega)
      (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨e, he, rfl⟩ := hx
          simp [bits, (hr r hr').2 e he])
    simp only [List.length_map, List.length_singleton, (hr r hr').1] at this
    exact this
  have hk1 : 1 ≤ k * (ℓ + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have := ur_intercalate_len [none, none] (k * (ℓ + 1) - 1) (rows.map fun r => joinSep (r.map bits))
    (by intro h; rw [List.map_eq_nil_iff] at h; subst h; simp at hlen; omega)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨r, hr', rfl⟩ := hx
        have := hrow r hr'; omega)
  simp only [List.length_map, hlen, List.length_cons, List.length_nil] at this
  rw [encIn, this]
  congr 1
  omega

theorem ur_sum_const {β : Type} (f : β → ℕ) (a : ℕ) :
    ∀ (L : List β), (∀ x ∈ L, f x = a) → (L.map f).sum = L.length * a
  | [], _ => by simp
  | x :: L, h => by
    rw [List.map_cons, List.sum_cons, ur_sum_const f a L (fun y hy => h y (by simp [hy])),
      h x (by simp), List.length_cons, Nat.succ_mul]
    omega

theorem ur_encB_rows (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) :
    (encB rows).length = m * (k * (ℓ + 1) + 1) + 1 := by
  obtain ⟨hlen, hm, hk, hl, hr⟩ := hs
  rw [ur_encB_length, ur_sum_const _ (k * (ℓ + 1) + 1) rows, hlen]
  intro r hr'
  rw [ur_encC_length, ur_sum_const _ (ℓ + 1) r, (hr r hr').1]
  intro e he; rw [(hr r hr').2 e he]

theorem ur_G_first (p : ℕ) (rows : List (List Ent)) (row0 : List Ent) (rows' : List (List Ent))
    (hr : rows = row0 :: rows') (h0 : row0 ≠ []) :
    ∃ e rest cs G', ur_G p rows = ((e :: rest) :: cs) :: G' ∧ (rest = [] ↔ ¬ 2 ^ p < row0.length) := by
  obtain ⟨h1, h2⟩ := ur_spl_first p row0 h0
  have hl := ur_spl_length p row0
  obtain ⟨c0, cs0, hcs⟩ : ∃ c0 cs0, ur_spl p row0 = c0 :: cs0 := by
    rcases h : ur_spl p row0 with _ | ⟨c0, cs0⟩
    · rw [h] at hl; simp at hl; have := Nat.two_pow_pos p; omega
    · exact ⟨c0, cs0, rfl⟩
  rw [hcs] at h1 h2
  simp only [List.headD_cons] at h1 h2
  obtain ⟨e, rest, rfl⟩ : ∃ e rest, c0 = e :: rest := by
    rcases c0 with _ | ⟨e, rest⟩
    · simp at h1
    · exact ⟨e, rest, rfl⟩
  have hp : 2 ^ p = (2 ^ p - 1) + 1 := by have := Nat.two_pow_pos p; omega
  refine ⟨e, rest, rows'.map (fun row => (ur_spl p row).getD 0 []),
    ((List.range (2 ^ p - 1)).map Nat.succ).map
      (fun r => rows.map (fun row => (ur_spl p row).getD r [])), ?_, ?_⟩
  · rw [ur_G, hp, List.range_succ_eq_map, List.map_cons, ← hp, List.map_map]
    simp [hr, hcs, Function.comp_def]
  · rw [← h2]; simp at h2 ⊢

set_option maxHeartbeats 2000000 in
theorem ur_loop_runs (k : ℕ) (rows : List (List Ent)) (row0 : List Ent) (rows' : List (List Ent))
    (hr : rows = row0 :: rows') (hk : row0.length = k) (h0 : row0 ≠ []) (B : ℕ)
    (hB : ∀ p ≤ Nat.clog 2 k, (encBs (ur_G p rows)).length ≤ B) :
    ∀ d p, p + d = Nat.clog 2 k → ∀ (T : Tapes Sym7 6) (F4 : List Sym7), F4.length ≤ 1 →
      (∀ x ∈ F4, x ≠ st) → T.head 4 = 1 →
      T.cells 5 = tapeOf S7 [if 2 ^ p < k then one else zero] → T.head 5 = 1 →
      ∃ t ≤ d * (12 * B + 15), ∃ T',
        Runs st (loop (fun a => decide (a 5 = one)) upass) (ur_S T (encBs (ur_G p rows)) [] F4 1 1)
          t T' ∧ T'.cells 1 = T.cells 1 ∧ T'.head 1 = T.head 1 ∧
          T'.cells 2 = tapeOf S7 (encBs (ur_G (Nat.clog 2 k) rows)) ∧ T'.head 2 = 1 := by
  intro d
  induction d with
  | zero =>
    intro p hp T F4 _ _ _ hc5 hh5
    have hp' : p = Nat.clog 2 k := by omega
    subst hp'
    have hpk : ¬ 2 ^ Nat.clog 2 k < k := not_lt.mpr (Nat.le_pow_clog (by norm_num) k)
    refine ⟨0, le_refl _ |>.trans (by simp), _, loop_stop ?_, by simp [ur_S], by simp [ur_S],
      by simp [ur_S], by simp [ur_S]⟩
    simp only [Tapes.read, ur_S]
    simp [hc5, hh5, hpk]
    exact (by decide : ¬ (zero = one))
  | succ d ih =>
    intro p hp T F4 hF4 hF4' hh4 hc5 hh5
    have hpk : 2 ^ p < k := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp (by omega)
    obtain ⟨e, rest, cs, G', hG, hrest⟩ := ur_G_first (p + 1) rows row0 rows' hr h0
    have hfc : ur_step (ur_G p rows) = ((e :: rest) :: cs) :: G' := by rw [ur_step_G, hG]
    obtain ⟨t1, ht1, F, hpos, hF, hF', r1⟩ := ur_upass_runs (ur_G p rows) e rest cs G' hfc T F4 hF4 hF4'
      hh4 [if 2 ^ p < k then one else zero] (by simp) (by intro x hx; simp at hx; subst hx; split_ifs <;> decide)
      hc5 hh5
    rw [ur_step_G] at r1 ht1
    have hflag : (if rest = [] then zero else one) = if 2 ^ (p + 1) < k then one else zero := by
      rw [← hk]; by_cases h : rest = []
      · rw [if_pos h, if_neg (hrest.mp h)]
      · rw [if_neg h, if_pos (by by_contra h'; exact h (hrest.mpr h'))]
    rw [hflag] at r1
    set T1 : Tapes Sym7 6 := ⟨Function.update (ur_S T (encBs (ur_G (p + 1) rows)) [] F 1 1).cells 5
      (tapeOf S7 [if 2 ^ (p + 1) < k then one else zero]),
      (ur_S T (encBs (ur_G (p + 1) rows)) [] F 1 1).head⟩ with hT1
    obtain ⟨t2, ht2, T', r2, e1, e2, e3, e4⟩ := ih (p + 1) (by omega) T1 F hF hF'
      (by simp [hT1, ur_S, hh4]) (by simp [hT1]) (by simp [hT1, ur_S, hh5])
    have hS : ur_S T1 (encBs (ur_G (p + 1) rows)) [] F 1 1 = T1 := by
      simp only [hT1, ur_S]
      congr 1 <;> funext l <;> fin_cases l <;> simp
    rw [hS] at r2
    have hrd : T.cells 5 (T.head 5) = one := by rw [hc5, hh5, if_pos hpk]; rfl
    refine ⟨t1 + t2, ?_, T', loop_iter ?_ hpos r1 r2, by rw [e1]; simp [hT1, ur_S],
      by rw [e2]; simp [hT1, ur_S], e3, e4⟩
    · have := hB p (by omega)
      have := hB (p + 1) (by omega)
      rw [Nat.succ_mul]; omega
    · simp [Tapes.read, ur_S, hrd]

theorem ur_pow_clog_lt (k : ℕ) (hk : 1 ≤ k) : 2 ^ Nat.clog 2 k < 2 * k := by
  rcases Nat.lt_or_ge 1 k with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    rw [Nat.pred_eq_sub_one] at h1
    have h2 : 0 < Nat.clog 2 k := Nat.clog_pos (by norm_num) h
    have : 2 ^ Nat.clog 2 k = 2 * 2 ^ (Nat.clog 2 k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have : k = 1 := by omega
    subst this; simp

theorem ur_L_bound (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) (p : ℕ)
    (hp : p ≤ Nat.clog 2 k) :
    (encBs (ur_G p rows)).length ≤ 4 * ((encIn rows).length + 1) := by
  have hNl := ur_encIn_len m k ℓ rows hs
  have hB0 := ur_encB_rows m k ℓ rows hs
  have hG := ur_G_len p rows
  obtain ⟨hlen, hm, hk, hl, hr⟩ := hs
  rw [hlen, hB0] at hG
  have hq : 2 ^ p + 1 ≤ 2 * k := by
    have := ur_pow_clog_lt k hk
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hp
    omega
  have hmq : (m + 1) * 2 ^ p + (m + 1) ≤ (m + 1) * (2 * k) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq
  have hkl : 2 * k ≤ k * (ℓ + 1) := by nlinarith
  have hmk : m * (2 * k) ≤ m * (k * (ℓ + 1)) := Nat.mul_le_mul_left _ hkl
  have hkm : k ≤ m * k := Nat.le_mul_of_pos_left k hm
  nlinarith

set_option maxHeartbeats 4000000 in
theorem umain_runs (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) (F : Sym7)
    (hF : F ≠ st) :
    ∃ t ≤ 100 * ((encIn rows).length + 1) * (Nat.clog 2 k + 1), ∃ T', ∃ z,
      Runs st umain (TF (encIn rows) F) t T' ∧ T'.cells 1 = tapeOf S7 [] ∧ T'.head 1 = 0 ∧
      T'.cells 2 = tapeOf S7 (encBs (ufinal m k z rows)) ∧
      T'.head 2 ≤ 4 * ((encIn rows).length + 1) ∧
      (encBs (ufinal m k z rows)).length ≤ 4 * ((encIn rows).length + 1) := by
  have hs' := hs
  have hNl := ur_encIn_len m k ℓ rows hs
  have hB0 := ur_encB_rows m k ℓ rows hs
  obtain ⟨hlen, hm, hk, hl, hr⟩ := hs
  obtain ⟨row0, rows', hrows⟩ : ∃ row0 rows', rows = row0 :: rows' := by
    cases rows with
    | nil => simp at hlen; omega
    | cons r rs => exact ⟨r, rs, rfl⟩
  have hk0 : row0.length = k := (hr row0 (by simp [hrows])).1
  obtain ⟨e0, rest0, hrow0⟩ : ∃ e rest, row0 = e :: rest := by
    cases row0 with
    | nil => simp at hk0; omega
    | cons e rest => exact ⟨e, rest, rfl⟩
  have he0 : e0.length = ℓ := (hr row0 (by simp [hrows])).2 e0 (by simp [hrow0])
  have hrne : ∀ r ∈ rows, r ≠ [] := by
    intro r hr'; have := (hr r hr').1; intro h; subst h; simp at this; omega
  have hene : ∀ r ∈ rows, ∀ e ∈ r, e ≠ [] := by
    intro r hr' e he h; have := (hr r hr').2 e he; subst h; simp at this; omega
  -- 1. conversion
  obtain ⟨t1, ht1, r1⟩ := ur_conv_loop (ur_units rows)
    (ur_WF_units rows (by simp [hrows]) hrne hene) (TF (encIn rows) F) [] []
    (by simp [TF, T0, ur_inU_units rows hrne]) (by simp [TF, T0]) (by simp [TF, T0])
    (by simp [TF, T0])
  rw [ur_inU_units rows hrne, ur_outU_units rows hrne] at r1
  rw [ur_inU_units rows hrne] at ht1
  have hfl : (rows.flatMap encC).length + 1 = (encB rows).length := by simp [encB]
  -- 2. end marker
  have r2 := wsym_runs 2 (by decide) runend (by decide)
    ⟨Function.update (TF (encIn rows) F).cells 2 (tapeOf S7 ([] ++ rows.flatMap encC)),
      Function.update (Function.update (TF (encIn rows) F).head 0
        (([] : List Sym7).length + 1 + (encIn rows).length)) 2
        (([] : List Sym7).length + 1 + (rows.flatMap encC).length)⟩
    (rows.flatMap encC) (by simp) (by simp; omega)
  have hC : rows.flatMap encC ++ [runend] = encBs (ur_G 0 rows) := by
    rw [ur_G_zero]; simp [encBs, encB]
  -- 3. rewind
  have r3 := rewind_runs 2
    ⟨Function.update (Function.update (TF (encIn rows) F).cells 2
        (tapeOf S7 ([] ++ rows.flatMap encC))) 2 (tapeOf S7 (rows.flatMap encC ++ [runend])),
      Function.update (Function.update (Function.update (TF (encIn rows) F).head 0
        (([] : List Sym7).length + 1 + (encIn rows).length)) 2
        (([] : List Sym7).length + 1 + (rows.flatMap encC).length)) 2
        ((rows.flatMap encC).length + 2)⟩ (encBs (ur_G 0 rows)) (ur_encBs_ne_st _)
    (by simp [hC])
  -- 4. check
  set T3 : Tapes Sym7 6 :=
    ⟨Function.update (Function.update (TF (encIn rows) F).cells 2
        (tapeOf S7 ([] ++ rows.flatMap encC))) 2 (tapeOf S7 (rows.flatMap encC ++ [runend])),
      Function.update (Function.update (Function.update (Function.update (TF (encIn rows) F).head 0
        (([] : List Sym7).length + 1 + (encIn rows).length)) 2
        (([] : List Sym7).length + 1 + (rows.flatMap encC).length)) 2
        ((rows.flatMap encC).length + 2)) 2 1⟩ with hT3
  have r4 := ur_ucheck_runs T3 e0 rest0 rows' [] [F] (by simp)
    (by intro x hx; simp at hx; subst hx; exact hF)
    (by simp only [hT3, Function.update_self]; rw [hC, ur_G_zero, hrows, hrow0]) (by simp [hT3])
    (by simp [hT3, TF]) (by simp [hT3, TF, T0])
  have hflag : (if rest0 = [] then zero else one) = if 2 ^ 0 < k then one else zero := by
    rw [← hk0, hrow0]
    rcases rest0 with _ | ⟨x, rest⟩ <;> simp
  rw [hflag] at r4
  set T4 : Tapes Sym7 6 := ⟨Function.update T3.cells 5 (tapeOf S7 [if 2 ^ 0 < k then one else zero]),
    T3.head⟩ with hT4
  -- 5. the loop
  obtain ⟨t5, ht5, T', r5, e1, e2, e3, e4⟩ := ur_loop_runs k rows row0 rows' hrows hk0
    (by simp [hrow0]) (4 * ((encIn rows).length + 1))
    (fun p hp => ur_L_bound m k ℓ rows hs' p hp) (Nat.clog 2 k) 0 (by omega) T4 []
    (by simp) (by simp) (by simp [hT4, hT3, TF, T0]) (by simp [hT4]) (by simp [hT4, hT3, TF, T0])
  have hS : ur_S T4 (encBs (ur_G 0 rows)) [] [] 1 1 = T4 := by
    simp only [hT4, hT3, ur_S]
    congr 1 <;> funext l <;> fin_cases l <;> simp [hC, TF, T0]
  rw [hS] at r5
  have hfin := ur_G_final k (Nat.clog 2 k) rows (Nat.le_pow_clog (by norm_num) k)
    (fun r hr' => (hr r hr').1)
  rw [hlen] at hfin
  have hLP := ur_L_bound m k ℓ rows hs' (Nat.clog 2 k) le_rfl
  rw [hfin] at e3 hLP
  refine ⟨_, ?_, T', 2 ^ Nat.clog 2 k - k,
    seq_runs r1 (seq_runs r2 (seq_runs r3 (seq_runs r4 r5))), ?_, ?_, e3, by omega, hLP⟩
  · simp only [Function.update_self]
    have hfl' : (rows.flatMap encC).length = (encIn rows).length + 2 := by omega
    have hℓ : ℓ ≤ (encIn rows).length := by
      have h1 : k * (ℓ + 1) + 1 ≤ m * (k * (ℓ + 1) + 1) := Nat.le_mul_of_pos_left _ hm
      have h2 : ℓ + 1 ≤ k * (ℓ + 1) := Nat.le_mul_of_pos_left _ hk
      omega
    have hP : Nat.clog 2 k * (12 * (4 * ((encIn rows).length + 1)) + 15) ≤
        100 * ((encIn rows).length + 1) * Nat.clog 2 k := by nlinarith
    have he : 100 * ((encIn rows).length + 1) * (Nat.clog 2 k + 1) =
        100 * ((encIn rows).length + 1) * Nat.clog 2 k + 100 * ((encIn rows).length + 1) := by ring
    simp only [List.length_nil, Nat.zero_add] at *
    try simp only [Function.update_self] at *
    omega
  · rw [e1]; simp [hT4, hT3, TF, T0]
  · rw [e2]; simp [hT4, hT3, TF, T0]

end IntMul.Mach.TP

-- ===== TFinal =====


namespace IntMul.Mach.TP

open IntMul IntMul.Mach IntMul.Mach.MS Sym7

theorem tmain_runs (m k ℓ : ℕ) (rows : List (List Ent)) (hs : Shape m k ℓ rows) :
    ∃ t ≤ 199 * ((encIn rows).length + 1) * (Nat.clog 2 (min m k) + 1), ∃ T',
      Runs st tmain ⟨fun i => if i = 0 then tapeOf S7 ((encIn rows).map letter) else tapeOf S7 [],
        fun _ => 0⟩ t T' ∧ T'.cells 1 = tapeOf S7 ((encIn (cols k rows)).map letter) := by
  set w := encIn rows with hw
  have r1 := tinit_runs w
  obtain ⟨t2, ht2, r2⟩ := decideP_runs m k ℓ rows hs
  obtain ⟨hne, hcne⟩ := cols_shape m k ℓ rows hs
  by_cases hmk : m ≤ k
  · rw [if_pos hmk] at r2
    obtain ⟨t3, ht3, T3, r3, c1, h1, c2, h2, hlen⟩ := rmain_runs m k ℓ rows hs one (by decide)
    obtain ⟨t4, ht4, T4, r4, o1⟩ := toutput_false_runs (cols k rows) hne
      (fun c hc => (hcne c hc).1) (fun c hc => (hcne c hc).2) T3 c2 c1 h1
    have ri : Runs st (ite (fun a => decide (a 5 = one)) (seq rmain (toutput false))
        (seq umain (toutput true))) (TF w one) (t3 + t4) T4 :=
      ite_runs_true (by simp [Tapes.read, TF, T0]; rfl) (seq_runs r3 r4)
    refine ⟨_, ?_, T4, seq_runs r1 (seq_runs r2 ri), o1⟩
    rw [min_eq_left hmk]
    generalize Nat.clog 2 m = K at *
    generalize (encIn rows).length = N at *
    nlinarith
  · rw [if_neg hmk] at r2
    obtain ⟨t3, ht3, T3, z, r3, c1, h1, c2, h2, hlen⟩ := umain_runs m k ℓ rows hs zero (by decide)
    obtain ⟨t4, ht4, T4, r4, o1⟩ := toutput_true_runs (cols k rows) m z hne hcne T3 c2 c1 h1
    have ri : Runs st (ite (fun a => decide (a 5 = one)) (seq rmain (toutput false))
        (seq umain (toutput true))) (TF w zero) (t3 + t4) T4 :=
      ite_runs_false (by simp [Tapes.read, TF, T0]; decide) (seq_runs r3 r4)
    refine ⟨_, ?_, T4, seq_runs r1 (seq_runs r2 ri), o1⟩
    rw [min_eq_right (by omega)]
    unfold ufinal at hlen
    generalize Nat.clog 2 k = K at *
    generalize (encIn rows).length = N at *
    nlinarith

end IntMul.Mach.TP

namespace IntMul.TM

open IntMul IntMul.Mach IntMul.Mach.MS IntMul.Mach.TP

theorem transpose_mach :
    ∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧
      ∀ (m k ℓ : ℕ) (A : Fin m → Fin k → List Bool), 1 ≤ m → 1 ≤ k → 1 ≤ ℓ → (∀ i j, (A i j).length = ℓ) →
        let enc : (m' k' : ℕ) → (Fin m' → Fin k' → List Bool) → List (Option Bool) :=
          fun m' k' B => List.intercalate [none, none]
            (List.ofFn fun i : Fin m' => joinSep (List.ofFn fun j : Fin k' => bits (B i j)))
        ∃ t : ℕ,
          (t : ℝ) ≤ c * (((enc m k A).length + 1 : ℕ) : ℝ) *
            ((Nat.clog 2 (min m k) + 1 : ℕ) : ℝ) ∧
          M.HaltsWithOutputW (enc m k A) t (enc k m fun j i => A i j) := by
  refine ⟨TM6, 200, by norm_num, fun m k ℓ A hm hk hl hA => ?_⟩
  intro enc
  have e1 : enc m k A = encIn (List.ofFn fun i => List.ofFn fun j => A i j) := enc_rows m k A
  have e2 : enc k m (fun j i => A i j) = encIn (cols k (List.ofFn fun i => List.ofFn fun j => A i j)) :=
    enc_cols m k A
  rw [e1, e2]
  obtain ⟨t, ht, T', hr, hout⟩ := tmain_runs m k ℓ _ (shape_ofFn m k ℓ A hm hk hl hA)
  refine ⟨t + 1, ?_, compile_haltsWithOutputW tmain _ _ t T' hr hout⟩
  have h1 : 1 ≤ ((encIn (List.ofFn fun i => List.ofFn fun j => A i j)).length + 1) *
      (Nat.clog 2 (min m k) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : t + 1 ≤ 200 * (((encIn (List.ofFn fun i => List.ofFn fun j => A i j)).length + 1) *
      (Nat.clog 2 (min m k) + 1)) := by
    rw [← Nat.mul_assoc] at *; nlinarith
  rw [mul_assoc]; exact_mod_cast h2

end IntMul.TM

open IntMul IntMul.TM in
theorem solution :
    ∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧
      ∀ (m k ℓ : ℕ) (A : Fin m → Fin k → List Bool), 1 ≤ m → 1 ≤ k → 1 ≤ ℓ → (∀ i j, (A i j).length = ℓ) →
        let enc : (m' k' : ℕ) → (Fin m' → Fin k' → List Bool) → List (Option Bool) :=
          fun m' k' B => List.intercalate [none, none]
            (List.ofFn fun i : Fin m' => joinSep (List.ofFn fun j : Fin k' => bits (B i j)))
        ∃ t : ℕ,
          (t : ℝ) ≤ c * (((enc m k A).length + 1 : ℕ) : ℝ) *
            ((Nat.clog 2 (min m k) + 1 : ℕ) : ℝ) ∧
          M.HaltsWithOutputW (enc m k A) t (enc k m fun j i => A i j) :=
  IntMul.TM.transpose_mach
