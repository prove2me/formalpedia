-- Prove2me | solution 1 for IntMul.TM.merge_sort
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T23:51:21.15883+00:00
-- url     : https://prove2.me/submissions/e7a5aa7f-4055-4bfa-a294-f562225a483c

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

-- ===== MSFinal =====


namespace IntMul.TM

open IntMul IntMul.Mach IntMul.Mach.MS

theorem merge_sort_mach : ∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧ ∀ (ℓ q : ℕ) (recs : List (List Bool × List Bool)), (∀ r ∈ recs, r.1.length = ℓ ∧ r.2.length = q) → let enc := fun rs => joinSep (rs.flatMap fun r => [bits r.1, bits r.2]); ∃ t : ℕ, (t : ℝ) ≤ c * (((enc recs).length + 1 : ℕ) : ℝ) * ((Nat.clog 2 recs.length + 1 : ℕ) : ℝ) ∧ M.HaltsWithOutputW (enc recs) t (enc (recs.mergeSort fun a b => decide (val a.1 ≤ val b.1))) := by
  refine ⟨SM, 31, by norm_num, fun ℓ q recs hrec => ?_⟩
  intro enc
  obtain ⟨t, ht, T', hr, hout⟩ := main_runs ℓ q recs hrec
  refine ⟨t + 1, ?_, compile_haltsWithOutputW main (enc' recs) (enc' (recs.mergeSort le7)) t T' hr hout⟩
  have h1 : 1 ≤ ((enc' recs).length + 1) * (Nat.clog 2 recs.length + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : t + 1 ≤ 31 * (((enc' recs).length + 1) * (Nat.clog 2 recs.length + 1)) := by
    rw [← Nat.mul_assoc] at *; nlinarith
  show ((t + 1 : ℕ) : ℝ) ≤ 31 * (((enc' recs).length + 1 : ℕ) : ℝ) * ((Nat.clog 2 recs.length + 1 : ℕ) : ℝ)
  rw [mul_assoc]; exact_mod_cast h2

end IntMul.TM

open IntMul IntMul.TM in
theorem solution : ∃ M : MultitapeTM, ∃ c : ℝ, 0 < c ∧ ∀ (ℓ q : ℕ) (recs : List (List Bool × List Bool)), (∀ r ∈ recs, r.1.length = ℓ ∧ r.2.length = q) → let enc := fun rs => joinSep (rs.flatMap fun r => [bits r.1, bits r.2]); ∃ t : ℕ, (t : ℝ) ≤ c * (((enc recs).length + 1 : ℕ) : ℝ) * ((Nat.clog 2 recs.length + 1 : ℕ) : ℝ) ∧ M.HaltsWithOutputW (enc recs) t (enc (recs.mergeSort fun a b => decide (val a.1 ≤ val b.1))) :=
  IntMul.TM.merge_sort_mach
