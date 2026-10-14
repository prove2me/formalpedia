-- Prove2me | solution 2 for IntMul.TM.karatsuba
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T22:54:29.556863+00:00
-- url     : https://prove2.me/submissions/f43bf97a-cfae-4f33-9e0a-7c9976080e73

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_FlatRecursiveEvaluation
import Theorems.Thm_IntMul_FlatRecursiveEvaluation_native_evaluates_correct

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

-- ===== Arith =====

/-!
# Bit-list arithmetic for `IntMul.val` and `IntMul.bin`
-/

namespace IntMul.Mach

open IntMul

theorem foldl_val_acc (l : List Bool) (a : ℕ) :
    l.foldl (fun a b => 2 * a + b.toNat) a = a * 2 ^ l.length + val l := by
  induction l generalizing a with
  | nil => simp [val]
  | cons b l ih =>
    simp only [List.foldl_cons, val] at ih ⊢
    rw [ih, ih (0 * 2 + b.toNat)]
    simp [pow_succ]; ring

theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat * 2 ^ l.length + val l := by
  have := foldl_val_acc l (2 * 0 + b.toNat)
  simpa [val] using this

theorem val_append_singleton (l : List Bool) (b : Bool) :
    val (l ++ [b]) = 2 * val l + b.toNat := by
  simp [val, List.foldl_append]

theorem val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val]
  | cons b l ih =>
    rw [val_cons]
    simp only [List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem val_replicate_false_append (n : ℕ) (l : List Bool) :
    val (List.replicate n false ++ l) = val l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, val_cons, ih]

theorem testBit_val (l : List Bool) (i : ℕ) (hi : i < l.length) :
    (val l).testBit (l.length - 1 - i) = l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    rw [val_cons]
    rcases i with _ | i
    · simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
      cases b
      · simp [Nat.testBit_eq_false_of_lt (val_lt l)]
      · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (val_lt l)]
    · simp only [List.length_cons, List.getElem_cons_succ] at hi ⊢
      have := ih i (by omega)
      rw [show l.length + 1 - 1 - (i + 1) = l.length - 1 - i by omega]
      cases b
      · simpa using this
      · simp only [Bool.toNat_true, one_mul]
        rw [Nat.testBit_two_pow_add_gt (by omega)]
        exact this

theorem bin_val (l : List Bool) : bin l.length (val l) = l := by
  apply List.ext_getElem
  · simp [bin]
  · intro i h1 h2
    simp only [bin, List.getElem_ofFn]
    exact testBit_val l i h2

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

-- ===== School =====

/-!
# Schoolbook multiplication on four tapes

Tapes: `0` input, `1` output, `2` holds `0ⁿx`, `3` the accumulator `C` (both `2n` bits, most
significant first).  For each bit `b` of `y`, from the most significant one,
`C := 2C + b·x`; the doubling and the addition are finite-state walks from the right end.
-/

namespace IntMul.Mach.School

open IntMul IntMul.Mach

set_option linter.unusedSectionVars false

/-- The alphabet. -/
inductive Sym5
  | blank
  | st
  | zero
  | one
  | sep
  deriving DecidableEq

open Sym5

instance : Fintype Sym5 :=
  ⟨{blank, st, zero, one, sep}, by intro x; cases x <;> simp⟩

def S5 : Syms Sym5 := ⟨blank, st, zero, one, sep, by decide⟩

/-- Bit symbols. -/
def bs (b : Bool) : Sym5 := if b then one else zero

theorem bitSym_S5 : bitSym S5 = bs := rfl

def enc (l : List Bool) : List Sym5 := l.map bs

def dec : Sym5 → Bool
  | one => true
  | _ => false

def isBit : Sym5 → Bool
  | zero => true
  | one => true
  | _ => false

def notSt : Sym5 → Bool
  | st => false
  | _ => true

def notBlank : Sym5 → Bool
  | blank => false
  | _ => true

@[simp] theorem dec_bs (b : Bool) : dec (bs b) = b := by cases b <;> rfl
@[simp] theorem isBit_bs (b : Bool) : isBit (bs b) = true := by cases b <;> rfl
@[simp] theorem notSt_bs (b : Bool) : notSt (bs b) = true := by cases b <;> rfl
@[simp] theorem notBlank_bs (b : Bool) : notBlank (bs b) = true := by cases b <;> rfl
@[simp] theorem bs_ne_st (b : Bool) : bs b ≠ st := by cases b <;> decide
@[simp] theorem bs_ne_blank (b : Bool) : bs b ≠ blank := by cases b <;> decide
@[simp] theorem S5_st : S5.st = st := rfl
@[simp] theorem S5_blank : S5.blank = blank := rfl

@[simp] theorem enc_length (l : List Bool) : (enc l).length = l.length := by simp [enc]

theorem enc_ne_st (l : List Bool) : ∀ x ∈ enc l, x ≠ S5.st := by
  intro x hx
  simp only [enc, List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  exact bs_ne_st b

/-! ## The two transducers -/

/-- Doubling: write the previous bit, remember the current one. -/
def fD (s : Bool) (x : Sym5) : Bool × Sym5 := (dec x, bs s)

/-- Ripple-carry addition of tape `2` into tape `3`. -/
def fA (s : Bool) (x y : Sym5) : Bool × Sym5 :=
  (decide (2 ≤ (dec x).toNat + (dec y).toNat + s.toNat),
    bs (decide (((dec x).toNat + (dec y).toNat + s.toNat) % 2 = 1)))

theorem rwalk_fD (c : List Bool) (b s : Bool) :
    rwalk fD (enc (b :: c)) s = (b, enc (c ++ [s])) := by
  induction c generalizing b with
  | nil => simp [enc, rwalk, fD]
  | cons b' c ih =>
    rw [show enc (b :: b' :: c) = bs b :: enc (b' :: c) from rfl, rwalk, ih b']
    simp [fD, enc]

theorem rwalk_fA (a c : List Bool) (h : a.length = c.length) (s : Bool) :
    ∃ r : List Bool, r.length = c.length ∧
      (rwalk (pairF fA) ((enc a).zip (enc c)) s).2 = (enc a).zip (enc r) ∧
      val r + (rwalk (pairF fA) ((enc a).zip (enc c)) s).1.toNat * 2 ^ c.length =
        val a + val c + s.toNat := by
  induction a generalizing c with
  | nil =>
    rcases c with _ | ⟨c0, c⟩
    · exact ⟨[], rfl, rfl, by simp [rwalk, val, enc]⟩
    · simp at h
  | cons a0 a ih =>
    rcases c with _ | ⟨c0, c⟩
    · simp at h
    · simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      obtain ⟨r, hr, h2, h3⟩ := ih c h
      obtain ⟨q, hq⟩ : ∃ q, (rwalk (pairF fA) ((enc a).zip (enc c)) s).1 = q := ⟨_, rfl⟩
      rw [hq] at h3
      have e : (enc (a0 :: a)).zip (enc (c0 :: c)) = (bs a0, bs c0) :: (enc a).zip (enc c) := rfl
      rw [e]
      refine ⟨decide ((a0.toNat + c0.toNat + q.toNat) % 2 = 1) :: r, by simp [hr], ?_, ?_⟩
      · rw [rwalk, h2, hq]; simp [pairF, fA, enc]
      · rw [rwalk, hq, val_cons, val_cons, val_cons, hr, h]
        simp only [pairF, fA, dec_bs, List.length_cons, pow_succ]
        cases a0 <;> cases c0 <;> cases q <;> simp at h3 ⊢ <;> omega

/-! ## Four tapes -/

def mk4 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) : Tapes Sym5 4 :=
  ⟨![c0, c1, c2, c3], ![h0, h1, h2, h3]⟩

theorem mk4_ext {T : Tapes Sym5 4} {c0 c1 c2 c3 : ℕ → Sym5} {h0 h1 h2 h3 : ℕ}
    (e0 : T.cells 0 = c0) (e1 : T.cells 1 = c1) (e2 : T.cells 2 = c2) (e3 : T.cells 3 = c3)
    (f0 : T.head 0 = h0) (f1 : T.head 1 = h1) (f2 : T.head 2 = h2) (f3 : T.head 3 = h3) :
    T = mk4 c0 c1 c2 c3 h0 h1 h2 h3 := by
  cases T with
  | mk cells head =>
    simp only [mk4, Tapes.mk.injEq]
    constructor <;> funext i <;> fin_cases i <;> simp_all

@[simp] theorem mk4_c0 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).cells 0 = c0 := rfl
@[simp] theorem mk4_c1 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).cells 1 = c1 := rfl
@[simp] theorem mk4_c2 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).cells 2 = c2 := rfl
@[simp] theorem mk4_c3 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).cells 3 = c3 := rfl
@[simp] theorem mk4_h0 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).head 0 = h0 := rfl
@[simp] theorem mk4_h1 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).head 1 = h1 := rfl
@[simp] theorem mk4_h2 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).head 2 = h2 := rfl
@[simp] theorem mk4_h3 (c0 c1 c2 c3 : ℕ → Sym5) (h0 h1 h2 h3 : ℕ) :
    (mk4 c0 c1 c2 c3 h0 h1 h2 h3).head 3 = h3 := rfl

/-! ## The program -/

def zeroF : Sym5 → Sym5 := fun _ => zero

def setup : Prog Sym5 4 :=
  seq (mv 0 Move.right) <| seq (mv 2 Move.right) <| seq (copy 0 2 isBit zeroF) <|
  seq (scanL 0 notSt) <| seq (mv 0 Move.right) <| seq (copy 0 2 isBit id) <|
  seq (scanL 2 notSt) <| seq (mv 2 Move.right) <| seq (mv 3 Move.right) <|
  seq (copy 2 3 isBit zeroF) <| seq (mv 2 Move.left) <| seq (mv 3 Move.left) (mv 0 Move.right)

/-! ## Tape facts -/

theorem notSt_of_ne {x : Sym5} (h : x ≠ st) : notSt x = true := by cases x <;> simp_all [notSt]

theorem enc_map_zeroF (l : List Bool) : (enc l).map zeroF = enc (List.replicate l.length false) := by
  apply List.ext_getElem <;> simp [enc, zeroF, bs]

theorem tapeOf_pre (L R : List Sym5) (p : ℕ) (hp : p < L.length) :
    tapeOf S5 (L ++ R) (1 + p) = L[p] := by
  rw [tapeOf_one_add, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left]

theorem tapeOf_at (L R : List Sym5) (x : Sym5) : tapeOf S5 (L ++ x :: R) (1 + L.length) = x := by
  rw [tapeOf_one_add]; simp

theorem tapeOf_end (L : List Sym5) : tapeOf S5 L (1 + L.length) = blank := by
  rw [tapeOf_one_add]; simp

theorem inp_ne_st (x y : List Bool) (p : ℕ) (hp : 1 ≤ p) :
    tapeOf S5 (enc x ++ sep :: enc y) p ≠ st := by
  apply tapeOf_ne_st S5 (by decide) _ _ p hp
  intro z hz
  simp only [List.mem_append, List.mem_cons] at hz
  rcases hz with hz | hz | hz
  · exact enc_ne_st x z hz
  · subst hz; decide
  · exact enc_ne_st y z hz

theorem encT_ne_st (l : List Bool) (p : ℕ) (hp : 1 ≤ p) : tapeOf S5 (enc l) p ≠ st :=
  tapeOf_ne_st S5 (by decide) _ (enc_ne_st l) p hp

/-! ## Setup -/

section Setup

variable (x y : List Bool)

/-- The input tape. -/
def I : ℕ → Sym5 := tapeOf S5 (enc x ++ sep :: enc y)
def E : ℕ → Sym5 := tapeOf S5 []

theorem setup_runs :
    Runs st setup (mk4 (I x y) E E E 0 0 0 0) (7 * x.length + 10)
      (mk4 (I x y) E (tapeOf S5 (enc (List.replicate x.length false ++ x)))
        (tapeOf S5 (enc (List.replicate (2 * x.length) false)))
        (x.length + 2) 0 (2 * x.length) (2 * x.length)) := by
  set n := x.length with hn
  set Z := tapeOf S5 (enc (List.replicate n false))
  set A := tapeOf S5 (enc (List.replicate n false ++ x))
  set C0 := tapeOf S5 (enc (List.replicate (2 * n) false))
  have h1 := (mv_runs st 0 Move.right (mk4 (I x y) E E E 0 0 0 0) (by simp)).of_eq
    (T'' := mk4 (I x y) E E E 1 0 0 0) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h2 := (mv_runs st 2 Move.right (mk4 (I x y) E E E 1 0 0 0) (by simp)).of_eq
    (T'' := mk4 (I x y) E E E 1 0 1 0) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h3 := (copy_runs S5 (by decide) 0 2 (by decide) (by decide) isBit zeroF
    (fun _ _ => by simp [zeroF]) (enc x) [] (mk4 (I x y) E E E 1 0 1 0)
    (fun p hp => by simp only [mk4_c0, mk4_h0, I]; exact tapeOf_pre _ _ p hp)
    (fun z hz => by simp only [enc, List.mem_map] at hz; obtain ⟨b, _, rfl⟩ := hz; simp)
    (by simp only [mk4_c0, mk4_h0, I, tapeOf_at]; rfl) rfl rfl).of_eq
    (T'' := mk4 (I x y) E Z E (n + 1) 0 (n + 1) 0)
    (by apply mk4_ext <;> simp [Function.update_apply, enc_map_zeroF, Z, hn] <;> omega) rfl
  have h4 := (scanL_runs st 0 notSt (n + 1) (mk4 (I x y) E Z E (n + 1) 0 (n + 1) 0) (by simp)
    (fun p hp => by
      simp only [mk4_c0, mk4_h0]
      exact ⟨notSt_of_ne (inp_ne_st x y _ (by omega)), inp_ne_st x y _ (by omega)⟩)
    (by simp [I, tapeOf_zero, notSt])).of_eq
    (T'' := mk4 (I x y) E Z E 0 0 (n + 1) 0) (by apply mk4_ext <;> simp [Function.update_apply]) rfl
  have h5 := (mv_runs st 0 Move.right (mk4 (I x y) E Z E 0 0 (n + 1) 0) (by simp)).of_eq
    (T'' := mk4 (I x y) E Z E 1 0 (n + 1) 0) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h6 := (copy_runs S5 (by decide) 0 2 (by decide) (by decide) isBit id
    (fun z hz => by cases z <;> simp_all [isBit]) (enc x) (enc (List.replicate n false))
    (mk4 (I x y) E Z E 1 0 (n + 1) 0)
    (fun p hp => by simp only [mk4_c0, mk4_h0, I]; exact tapeOf_pre _ _ p hp)
    (fun z hz => by simp only [enc, List.mem_map] at hz; obtain ⟨b, _, rfl⟩ := hz; simp)
    (by simp only [mk4_c0, mk4_h0, I, tapeOf_at]; rfl) rfl (by simp)).of_eq
    (T'' := mk4 (I x y) E A E (n + 1) 0 (2 * n + 1) 0)
    (by apply mk4_ext <;> simp [Function.update_apply, A, enc, hn] <;> omega) rfl
  have h7 := (scanL_runs st 2 notSt (2 * n + 1) (mk4 (I x y) E A E (n + 1) 0 (2 * n + 1) 0)
    (by simp)
    (fun p hp => by
      simp only [mk4_c2, mk4_h2]
      exact ⟨notSt_of_ne (encT_ne_st _ _ (by omega)), encT_ne_st _ _ (by omega)⟩)
    (by simp [A, tapeOf_zero, notSt])).of_eq
    (T'' := mk4 (I x y) E A E (n + 1) 0 0 0) (by apply mk4_ext <;> simp [Function.update_apply]) rfl
  have h8 := (mv_runs st 2 Move.right (mk4 (I x y) E A E (n + 1) 0 0 0) (by simp)).of_eq
    (T'' := mk4 (I x y) E A E (n + 1) 0 1 0) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h9 := (mv_runs st 3 Move.right (mk4 (I x y) E A E (n + 1) 0 1 0) (by simp)).of_eq
    (T'' := mk4 (I x y) E A E (n + 1) 0 1 1) (by apply mk4_ext <;> simp [moveHead]) rfl
  have hlenA : (enc (List.replicate n false ++ x)).length = 2 * n := by simp [hn]; omega
  have h10 := (copy_runs S5 (by decide) 2 3 (by decide) (by decide) isBit zeroF
    (fun _ _ => by simp [zeroF]) (enc (List.replicate n false ++ x)) []
    (mk4 (I x y) E A E (n + 1) 0 1 1)
    (fun p hp => by simpa [A] using tapeOf_pre (enc (List.replicate n false ++ x)) [] p hp)
    (fun z hz => by simp only [enc, List.mem_map] at hz; obtain ⟨b, _, rfl⟩ := hz; simp)
    (by simp only [mk4_c2, mk4_h2, A]; rw [tapeOf_end]; rfl) rfl rfl).of_eq
    (T'' := mk4 (I x y) E A C0 (n + 1) 0 (2 * n + 1) (2 * n + 1)) (t' := 2 * n)
    (by
      apply mk4_ext <;> simp [Function.update_apply, enc_map_zeroF, C0] <;> try omega
      congr 3; omega) hlenA
  have h11 := (mv_runs st 2 Move.left (mk4 (I x y) E A C0 (n + 1) 0 (2 * n + 1) (2 * n + 1))
    (fun _ => by simp only [mk4_c2, mk4_h2]; exact encT_ne_st _ (2 * n + 1) (by omega))).of_eq
    (T'' := mk4 (I x y) E A C0 (n + 1) 0 (2 * n) (2 * n + 1)) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h12 := (mv_runs st 3 Move.left (mk4 (I x y) E A C0 (n + 1) 0 (2 * n) (2 * n + 1))
    (fun _ => by simp only [mk4_c3, mk4_h3]; exact encT_ne_st _ (2 * n + 1) (by omega))).of_eq
    (T'' := mk4 (I x y) E A C0 (n + 1) 0 (2 * n) (2 * n)) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h13 := (mv_runs st 0 Move.right (mk4 (I x y) E A C0 (n + 1) 0 (2 * n) (2 * n)) (by simp)).of_eq
    (T'' := mk4 (I x y) E A C0 (n + 2) 0 (2 * n) (2 * n)) (by apply mk4_ext <;> simp [moveHead]) rfl
  exact (seq_runs h1 <| seq_runs h2 <| seq_runs h3 <| seq_runs h4 <| seq_runs h5 <| seq_runs h6 <|
    seq_runs h7 <| seq_runs h8 <| seq_runs h9 <| seq_runs h10 <| seq_runs h11 <|
    seq_runs h12 h13).of_eq rfl (by simp [hn]; omega)

end Setup


/-! ## One pass of the main loop -/

def dbl : Prog Sym5 4 :=
  seq (walk1 S5.st 3 false fD) (seq (scanR 3 notBlank) (mv 3 Move.left))

def add : Prog Sym5 4 :=
  seq (walk2 S5.st 2 3 false fA) <| seq (seq (scanR 2 notBlank) (mv 2 Move.left)) <|
    seq (scanR 3 notBlank) (mv 3 Move.left)

def body : Prog Sym5 4 :=
  seq dbl (seq (ite (fun a => dec (a 0)) add skip) (mv 0 Move.right))

def mainLoop : Prog Sym5 4 := loop (fun a => isBit (a 0)) body

theorem notBlank_encT (d : List Bool) (p : ℕ) (hp : p ≤ d.length) :
    notBlank (tapeOf S5 (enc d) p) = true := by
  rcases p with _ | p
  · rfl
  · rw [tapeOf_succ, List.getD_eq_getElem _ _ (by simp; omega)]
    simp [enc]

@[simp] theorem encT_blank (d : List Bool) : tapeOf S5 (enc d) (d.length + 1) = blank := by
  rw [tapeOf_succ, List.getD_eq_default _ _ (by simp)]; rfl

theorem encT_end (d : List Bool) : tapeOf S5 (enc d) (0 + (d.length + 1)) = blank := by
  rw [Nat.zero_add, tapeOf_succ, List.getD_eq_default _ _ (by simp)]; rfl

/-- Rewind tape `i ∈ {2, 3}` from `▷` to the last cell of a `2n`-bit word. -/
theorem rewind_runs (i : Fin 4) (d : List Bool) (T : Tapes Sym5 4)
    (hc : T.cells i = tapeOf S5 (enc d)) (hh : T.head i = 0) :
    Runs st (seq (scanR i notBlank) (mv i Move.left)) T (d.length + 2)
      ⟨T.cells, Function.update T.head i d.length⟩ := by
  have h1 := scanR_runs st i notBlank (d.length + 1) T
    (fun p hp => by rw [hc, hh]; exact notBlank_encT d _ (by omega))
    (by rw [hc, hh, encT_end]; rfl)
  have h2 := mv_runs st i Move.left ⟨T.cells, Function.update T.head i (T.head i + (d.length + 1))⟩
    (fun _ => by simp [hc, hh])
  exact (seq_runs h1 h2).of_eq (by simp [hh, moveHead]) (by omega)

theorem dbl_runs (c0 : ℕ → Sym5) (h0 : ℕ) (A : ℕ → Sym5) (b : Bool) (c : List Bool) :
    Runs st dbl (mk4 c0 E A (tapeOf S5 (enc (b :: c))) h0 0 (c.length + 1) (c.length + 1))
      (2 * c.length + 4)
      (mk4 c0 E A (tapeOf S5 (enc (c ++ [false]))) h0 0 (c.length + 1) (c.length + 1)) := by
  have h1 := walk1_halts S5 3 (by decide) false fD (fun s _ _ => by simp [fD]) (enc (b :: c)) []
    false (mk4 c0 E A (tapeOf S5 (enc (b :: c))) h0 0 (c.length + 1) (c.length + 1))
    (enc_ne_st _) (by simp) (by simp)
  rw [rwalk_fD, List.append_nil] at h1
  have h2 := rewind_runs 3 (c ++ [false])
    ⟨Function.update (mk4 c0 E A (tapeOf S5 (enc (b :: c))) h0 0 (c.length + 1)
          (c.length + 1)).cells 3 (tapeOf S5 (enc (c ++ [false]))),
        Function.update (mk4 c0 E A (tapeOf S5 (enc (b :: c))) h0 0 (c.length + 1)
          (c.length + 1)).head 3 0⟩ (by simp) (by simp)
  exact (seq_runs h1 h2).of_eq
    (by apply mk4_ext <;> simp [Function.update_apply]) (by simp; omega)


theorem add_runs (c0 : ℕ → Sym5) (h0 : ℕ) (a d : List Bool) (hl : a.length = d.length)
    (hs : val a + val d < 2 ^ d.length) :
    ∃ r : List Bool, r.length = d.length ∧ val r = val a + val d ∧
      Runs st add (mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc d)) h0 0 d.length d.length)
        (3 * d.length + 4)
        (mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc r)) h0 0 d.length d.length) := by
  obtain ⟨r, hr, hz, hv⟩ := rwalk_fA a d hl false
  have hq : (rwalk (pairF fA) ((enc a).zip (enc d)) false).1 = false := by
    by_contra hq
    simp only [Bool.not_eq_false] at hq
    rw [hq] at hv
    simp at hv
    omega
  rw [hq] at hv
  simp only [Bool.toNat_false, zero_mul, Nat.add_zero] at hv
  refine ⟨r, hr, hv, ?_⟩
  set T := mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc d)) h0 0 d.length d.length
  have h1 := walk2_halts S5 2 3 (by decide) (by decide) false fA (fun _ _ _ _ => by simp [fA])
    ((enc a).zip (enc d)) [] [] false T
    (fun z hz => by
      obtain ⟨z1, z2⟩ := z
      obtain ⟨h1, h2⟩ := List.of_mem_zip hz
      exact ⟨enc_ne_st a z1 h1, enc_ne_st d z2 h2⟩)
    (by rw [List.map_fst_zip (by simp [hl])]; simp [T])
    (by simp [T, hl])
    (by rw [List.map_snd_zip (by simp [hl])]; simp [T])
    (by simp [T, hl])
  rw [hz, List.map_snd_zip (by simp [hl, hr]), List.append_nil] at h1
  have h2 := rewind_runs 2 a
    ⟨Function.update T.cells 3 (tapeOf S5 (enc r)), Function.update (Function.update T.head 2 0) 3 0⟩
    (by simp [T, Function.update_apply]) (by simp [Function.update_apply])
  have h3 := rewind_runs 3 r
    ⟨Function.update T.cells 3 (tapeOf S5 (enc r)),
      Function.update (Function.update (Function.update T.head 2 0) 3 0) 2 a.length⟩
    (by simp) (by simp [Function.update_apply])
  exact (seq_runs h1 (seq_runs h2 h3)).of_eq
    (T'' := mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc r)) h0 0 d.length d.length)
    (t' := 3 * d.length + 4)
    (by apply mk4_ext <;> simp [T, Function.update_apply, hl, hr]) (by simp [hl, hr]; omega)


theorem body_runs (c0 : ℕ → Sym5) (h0 : ℕ) (b : Bool) (hb : c0 h0 = bs b) (a : List Bool)
    (e : Bool) (c : List Bool) (hl : a.length = c.length + 1)
    (hs : 2 * val (e :: c) + b.toNat * val a < 2 ^ (c.length + 1))
    (hlow : val (e :: c) < 2 ^ c.length) :
    ∃ t, 0 < t ∧ t ≤ 5 * c.length + 12 ∧ ∃ r : List Bool, r.length = c.length + 1 ∧
      val r = 2 * val (e :: c) + b.toNat * val a ∧
      Runs st body (mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc (e :: c))) h0 0 (c.length + 1)
          (c.length + 1)) t
        (mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc r)) (h0 + 1) 0 (c.length + 1)
          (c.length + 1)) := by
  have he : e = false := by
    rw [val_cons] at hlow
    cases e
    · rfl
    · simp at hlow
  have hvd : val (c ++ [false]) = 2 * val (e :: c) := by
    rw [val_append_singleton, val_cons, he]; simp
  have h1 := dbl_runs c0 h0 (tapeOf S5 (enc a)) e c
  have hmv : ∀ r : List Bool, Runs st (mv 0 Move.right)
      (mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc r)) h0 0 (c.length + 1) (c.length + 1)) 1
      (mk4 c0 E (tapeOf S5 (enc a)) (tapeOf S5 (enc r)) (h0 + 1) 0 (c.length + 1)
        (c.length + 1)) := fun r =>
    (mv_runs st 0 Move.right _ (by simp)).of_eq (by apply mk4_ext <;> simp [moveHead]) rfl
  have hlen : (c ++ [false]).length = c.length + 1 := by simp
  cases b
  · refine ⟨2 * c.length + 4 + (0 + 1), by omega, by omega, c ++ [false], hlen, by simp [hvd], ?_⟩
    refine seq_runs h1 (seq_runs (ite_runs_false (by simp [Tapes.read, hb]) (skip_runs _)) (hmv _))
  · obtain ⟨r, hr, hv, h2⟩ := add_runs c0 h0 a (c ++ [false]) (by simp [hl])
      (by rw [hvd, hlen]; simp at hs; omega)
    rw [hlen] at h2 hr
    refine ⟨2 * c.length + 4 + (3 * (c.length + 1) + 4 + 1), by omega, by omega, r, hr,
      by rw [hv, hvd]; simp; omega, ?_⟩
    exact seq_runs h1 (seq_runs (ite_runs_true (by simp [Tapes.read, hb]) h2) (hmv r))


/-! ## The main loop -/

theorem I_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    I x y (x.length + 2 + j) = bs y[j] := by
  rw [I, show x.length + 2 + j = 1 + (x.length + 1 + j) by omega, tapeOf_one_add,
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp [enc, show x.length + 1 + j - x.length = j + 1 by omega]

theorem I_end (x y : List Bool) (hy : y.length = x.length) :
    I x y (x.length + 2 + x.length) = blank := by
  rw [I, show x.length + 2 + x.length = 1 + ((enc x).length + 1 + y.length) by simp; omega,
    tapeOf_one_add, List.getD_eq_default _ _ (by simp; omega)]
  rfl

theorem val_take_succ (y : List Bool) (j : ℕ) (hj : j < y.length) :
    val (y.take (j + 1)) = 2 * val (y.take j) + y[j].toNat := by
  rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, val_append_singleton]

theorem loop_runs (x y : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length) :
    ∀ m j (c : List Bool), j + m = x.length → c.length = 2 * x.length →
      val c = val x * val (y.take j) →
      ∃ t ≤ m * (10 * x.length + 7), ∃ c' : List Bool, c'.length = 2 * x.length ∧
        val c' = val x * val y ∧
        Runs st mainLoop (mk4 (I x y) E (tapeOf S5 (enc (List.replicate x.length false ++ x)))
            (tapeOf S5 (enc c)) (x.length + 2 + j) 0 (2 * x.length) (2 * x.length)) t
          (mk4 (I x y) E (tapeOf S5 (enc (List.replicate x.length false ++ x)))
            (tapeOf S5 (enc c')) (2 * x.length + 2) 0 (2 * x.length) (2 * x.length)) := by
  set n := x.length with hn'
  intro m
  induction m with
  | zero =>
    intro j c hj hc hv
    simp only [Nat.add_zero] at hj
    subst hj
    refine ⟨0, by simp, c, hc, by rw [hv, List.take_of_length_le (by omega)], ?_⟩
    have := loop_stop (st := st) (c := fun a => isBit (a 0)) (B := body)
      (T := mk4 (I x y) E (tapeOf S5 (enc (List.replicate n false ++ x)))
        (tapeOf S5 (enc c)) (n + 2 + n) 0 (2 * n) (2 * n))
      (by have hI : I x y (n + 2 + n) = blank := I_end x y hy
          simp [Tapes.read, hI, isBit])
    rw [show 2 * n + 2 = n + 2 + n by omega]
    exact this
  | succ m ih =>
    intro j c hj hc hv
    have hjn : j < n := by omega
    obtain ⟨e, c'', rfl⟩ : ∃ e c'', c = e :: c'' := by
      rcases c with _ | ⟨e, c''⟩
      · simp at hc; omega
      · exact ⟨e, c'', rfl⟩
    simp only [List.length_cons] at hc
    have hxl := val_lt x
    have hyl : val (y.take j) < 2 ^ j := by
      have := val_lt (y.take j); simpa [List.length_take, show min j y.length = j by omega] using this
    have hbit : (y[j]'(by omega)).toNat ≤ 1 := by cases y[j] <;> simp
    have hstep := val_take_succ y j (by omega)
    have hlow : val (e :: c'') < 2 ^ c''.length := by
      rw [hv]
      calc val x * val (y.take j) < 2 ^ n * 2 ^ j := Nat.mul_lt_mul'' hxl hyl
        _ = 2 ^ (n + j) := (pow_add 2 n j).symm
        _ ≤ 2 ^ c''.length := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hya : val (List.replicate n false ++ x) = val x := val_replicate_false_append n x
    have hs : 2 * val (e :: c'') + (y[j]'(by omega)).toNat * val (List.replicate n false ++ x) <
        2 ^ (c''.length + 1) := by
      rw [hv, hya]
      have h2 : val (y.take (j + 1)) < 2 ^ (j + 1) := by
        have := val_lt (y.take (j + 1))
        simpa [List.length_take, show min (j + 1) y.length = j + 1 by omega] using this
      calc 2 * (val x * val (y.take j)) + (y[j]'(by omega)).toNat * val x
          = val x * val (y.take (j + 1)) := by rw [hstep]; ring
        _ < 2 ^ n * 2 ^ (j + 1) := Nat.mul_lt_mul'' hxl h2
        _ = 2 ^ (n + (j + 1)) := (pow_add 2 n (j + 1)).symm
        _ ≤ 2 ^ (c''.length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨t1, ht1, ht1', r, hr, hvr, h1⟩ := body_runs (I x y) (n + 2 + j) (y[j]'(by omega))
      (I_y x y j (by omega)) (List.replicate n false ++ x) e c'' (by simp; omega) hs hlow
    obtain ⟨t2, ht2, c', hc', hvc', h2⟩ := ih (j + 1) r (by omega) (by omega)
      (by rw [hvr, hv, hya, hstep]; ring)
    refine ⟨t1 + t2, ?_, c', hc', hvc', ?_⟩
    · have : c''.length = 2 * n - 1 := by omega
      rw [this] at ht1'
      have : (m + 1) * (10 * n + 7) = (10 * n + 7) + m * (10 * n + 7) := by ring
      omega
    · rw [show c''.length + 1 = 2 * n by omega] at h1
      rw [show n + 2 + j + 1 = n + 2 + (j + 1) by omega] at h1
      have hIy : I x y (n + 2 + j) = bs (y[j]'(by omega)) := I_y x y j (by omega)
      exact loop_iter (by simp [Tapes.read, hIy]) ht1 h1 h2


/-! ## Output and the whole program -/

def output : Prog Sym5 4 :=
  seq (scanL 3 notSt) (seq (mv 3 Move.right) (seq (mv 1 Move.right) (copy 3 1 isBit id)))

def prog : Prog Sym5 4 := seq setup (seq mainLoop output)

theorem output_runs (c0 A : ℕ → Sym5) (h0 : ℕ) (c : List Bool) :
    ∃ T' : Tapes Sym5 4, T'.cells 1 = tapeOf S5 (enc c) ∧
      Runs st output (mk4 c0 E A (tapeOf S5 (enc c)) h0 0 c.length c.length) (2 * c.length + 2) T' := by
  have h1 := (scanL_runs st 3 notSt c.length (mk4 c0 E A (tapeOf S5 (enc c)) h0 0 c.length c.length)
    (by simp)
    (fun p hp => by
      simp only [mk4_c3, mk4_h3]
      exact ⟨notSt_of_ne (encT_ne_st _ _ (by omega)), encT_ne_st _ _ (by omega)⟩)
    (by simp [tapeOf_zero, notSt])).of_eq
    (T'' := mk4 c0 E A (tapeOf S5 (enc c)) h0 0 c.length 0)
    (by apply mk4_ext <;> simp [Function.update_apply]) rfl
  have h2 := (mv_runs st 3 Move.right (mk4 c0 E A (tapeOf S5 (enc c)) h0 0 c.length 0) (by simp)).of_eq
    (T'' := mk4 c0 E A (tapeOf S5 (enc c)) h0 0 c.length 1) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h3 := (mv_runs st 1 Move.right (mk4 c0 E A (tapeOf S5 (enc c)) h0 0 c.length 1) (by simp)).of_eq
    (T'' := mk4 c0 E A (tapeOf S5 (enc c)) h0 1 c.length 1) (by apply mk4_ext <;> simp [moveHead]) rfl
  have h4 := copy_runs S5 (by decide) 3 1 (by decide) (by decide) isBit id
    (fun z hz => by cases z <;> simp_all [isBit]) (enc c) []
    (mk4 c0 E A (tapeOf S5 (enc c)) h0 1 c.length 1)
    (fun p hp => by simpa using tapeOf_pre (enc c) [] p hp)
    (fun z hz => by simp only [enc, List.mem_map] at hz; obtain ⟨b, _, rfl⟩ := hz; simp)
    (by simp only [mk4_c3, mk4_h3]; rw [show 1 + (enc c).length = c.length + 1 by simp; omega,
      encT_blank]; rfl) rfl rfl
  refine ⟨_, by simp, (seq_runs h1 (seq_runs h2 (seq_runs h3 h4))).of_eq rfl (by simp; omega)⟩

theorem initTapes_eq (hk : 2 ≤ 4) (x y : List Bool) :
    initTapes S5 hk x y = mk4 (I x y) E E E 0 0 0 0 := by
  apply mk4_ext <;> first | rfl | (funext p; cases p <;> rfl)

theorem prog_runs (hk : 2 ≤ 4) (x y : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length) :
    ∃ t ≤ 10 * x.length ^ 2 + 18 * x.length + 12, ∃ T' : Tapes Sym5 4,
      Runs st prog (initTapes S5 hk x y) t T' ∧
      T'.cells 1 = tapeOf S5 ((bin (2 * x.length) (val x * val y)).map (bitSym S5)) := by
  have h1 := setup_runs x y
  obtain ⟨t2, ht2, c, hc, hvc, h2⟩ := loop_runs x y hy hn x.length 0
    (List.replicate (2 * x.length) false) (by omega) (by simp)
    (by
      have := val_replicate_false_append (2 * x.length) []
      simp only [List.append_nil] at this
      simp [this, val_nil])
  obtain ⟨T', hT', h3⟩ := output_runs (I x y)
    (tapeOf S5 (enc (List.replicate x.length false ++ x))) (2 * x.length + 2) c
  rw [hc] at h3
  rw [Nat.add_zero] at h2
  refine ⟨7 * x.length + 10 + (t2 + (2 * (2 * x.length) + 2)), ?_, T', ?_, ?_⟩
  · have : x.length * (10 * x.length + 7) = 10 * x.length ^ 2 + 7 * x.length := by ring
    omega
  · rw [initTapes_eq]
    exact seq_runs h1 (seq_runs h2 h3)
  · rw [hT', ← hvc, ← hc, bin_val]; rfl

end IntMul.Mach.School

namespace IntMul.Mach

open School

/-- The schoolbook machine. -/
def schoolTM : MultitapeTM := compile S5 (by norm_num : 2 ≤ 4) School.prog

theorem schoolTM_multipliesAt (n : ℕ) (hn : 1 ≤ n) :
    MultipliesAt schoolTM n (10 * (n : ℝ) ^ 2 + 18 * n + 13) := by
  intro x y hx hy
  subst hx
  obtain ⟨t, ht, T', hr, hout⟩ := prog_runs (by norm_num) x y (by omega) (by omega)
  refine ⟨t + 1, ?_, ?_⟩
  · have : ((t : ℕ) : ℝ) ≤ ((10 * x.length ^ 2 + 18 * x.length + 12 : ℕ) : ℝ) := by exact_mod_cast ht
    push_cast at this ⊢
    linarith
  · exact compile_haltsWithOutput S5 _ School.prog x y _ t T' hr hout

/-- Schoolbook multiplication: `T(n) = O(n²)` on the platform's multitape model. -/
theorem mulTimeBound_sq : MulTimeBound (fun n => (n : ℝ) ^ 2) := by
  refine ⟨schoolTM, fun n hn => ⟨_, schoolTM_multipliesAt n hn⟩, 41, by norm_num, 1,
    fun n _ hn => ?_⟩
  intro x y hx hy
  obtain ⟨t, ht, h⟩ := schoolTM_multipliesAt n hn x y hx hy
  refine ⟨t, ?_, h⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

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

-- ===== KArith =====

/-!
# Leftward ripple arithmetic as a sweep

Numbers are most-significant-bit first; a leftward sweep reads them from the least significant
end.  A source that runs out reads `▷` (bit `0`) and stays put.
-/

namespace IntMul.Mach

open IntMul IntMul.Mach.School School.Sym5

set_option linter.unusedSectionVars false

/-- The number whose `m`-th least significant bit is `g m`, truncated to `L` bits. -/
def nv (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | L + 1 => (g 0).toNat + 2 * nv (fun m => g (m + 1)) L

theorem nv_succ' (g : ℕ → Bool) (L : ℕ) : nv g (L + 1) = nv g L + (g L).toNat * 2 ^ L := by
  induction L generalizing g with
  | zero => simp [nv]
  | succ L ih =>
    rw [nv, ih (fun m => g (m + 1)), nv]
    simp [pow_succ]; ring

theorem nv_congr {g g' : ℕ → Bool} {L : ℕ} (h : ∀ m < L, g m = g' m) : nv g L = nv g' L := by
  induction L with
  | zero => rfl
  | succ L ih => rw [nv_succ', nv_succ', ih (fun m hm => h m (by omega)), h L (by omega)]

theorem nv_false (L : ℕ) : nv (fun _ => false) L = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simp [nv_succ', ih]

theorem nv_lt (g : ℕ → Bool) (L : ℕ) : nv g L < 2 ^ L := by
  induction L with
  | zero => simp [nv]
  | succ L ih => rw [nv_succ', pow_succ]; cases g L <;> simp <;> omega

/-- Reading a word from its right end. -/
theorem nv_read_exact (w : List Bool) (q : ℕ) (c : ℕ → Sym5)
    (hc : ∀ i (h : i < w.length), c (q + 1 + i) = bs w[i]) :
    nv (fun m => dec (c (q + w.length - m))) w.length = val w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih =>
    simp only [List.length_append, List.length_singleton]
    rw [nv, val_append_singleton]
    have h0 : c (q + (w.length + 1) - 0) = bs b := by
      have := hc w.length (by simp)
      rw [Nat.sub_zero, ← Nat.add_assoc, Nat.add_right_comm q]
      simpa using this
    rw [h0, dec_bs]
    have := ih (fun i h => by
      have := hc i (by simp; omega)
      rwa [List.getElem_append_left h] at this)
    rw [← this]
    have e : (fun m => dec (c (q + (w.length + 1) - (m + 1)))) =
        (fun m => dec (c (q + w.length - m))) := by
      funext m; congr 2; omega
    rw [e]; ring

/-- Reading a word from its right end past its start: `▷` reads as `0`. -/
theorem nv_read_pad (w : List Bool) (c : ℕ → Sym5) (h0 : c 0 = st)
    (hc : ∀ i (h : i < w.length), c (1 + i) = bs w[i]) (L : ℕ) (hL : w.length ≤ L) :
    nv (fun m => dec (c (w.length - m))) L = val w := by
  induction w using List.reverseRecOn generalizing L with
  | nil =>
    simp only [List.length_nil, Nat.zero_sub, h0]
    exact nv_false L
  | append_singleton w b ih =>
    simp only [List.length_append, List.length_singleton] at hL ⊢
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [nv, val_append_singleton]
    have hb : c (w.length + 1 - 0) = bs b := by
      have := hc w.length (by simp)
      simpa [Nat.add_comm] using this
    rw [hb, dec_bs]
    have := ih (fun i h => by
      have := hc i (by simp; omega)
      rwa [List.getElem_append_left h] at this) L (by omega)
    rw [← this]
    have e : (fun m => dec (c (w.length + 1 - (m + 1)))) = (fun m => dec (c (w.length - m))) := by
      funext m; congr 2; omega
    rw [e]; ring

/-- The word written by a leftward sweep. -/
theorem val_ofFn_rev (g : ℕ → Bool) (L : ℕ) :
    val (List.ofFn (fun m : Fin L => g (L - 1 - m))) = nv g L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [List.ofFn_succ, val_cons, nv_succ', ← ih]
    simp only [List.length_ofFn, Fin.val_zero, Fin.val_succ]
    have e : (fun i : Fin L => g (L + 1 - 1 - (i + 1))) = (fun i : Fin L => g (L - 1 - i)) := by
      funext i; congr 1; omega
    rw [e, Nat.add_sub_cancel, Nat.sub_zero]; ring

theorem bin_of_val (w : List Bool) (v : ℕ) (h : val w = v % 2 ^ w.length) :
    w = bin w.length v := by
  conv_lhs => rw [← bin_val w]
  rw [h]
  apply List.ext_getElem
  · simp [bin]
  · intro i h1 h2
    simp only [bin, List.getElem_ofFn]
    rw [Nat.testBit_mod_two_pow]
    simp only [bin, List.length_ofFn] at h1
    rw [decide_eq_true (by omega), Bool.true_and]

/-! ## The arithmetic sweep -/

variable {k : ℕ}

/-- A bitwise transducer lifted to a sweep step reading tapes `src` and `dst`. -/
def arF (src dst : Fin k) (g : Bool → Bool → Bool → Bool × Bool) (s : Bool) (a : Fin k → Sym5) :
    Bool × Sym5 :=
  ((g s (dec (a src)) (dec (a dst))).1, bs (g s (dec (a src)) (dec (a dst))).2)

/-- Leftward ripple sweep of `src` into `dst`, until `dst` scans a non-bit. -/
def arSweep (src dst : Fin k) (g : Bool → Bool → Bool → Bool × Bool) : Prog Sym5 k :=
  sweep (fun i => if i = dst ∨ i = src then Move.left else Move.stay) dst
    (fun a => isBit (a dst)) false (arF src dst g)

theorem isBit_eq_false_of_ne_st {x : Sym5} : isBit x = false → x ≠ zero ∧ x ≠ one := by
  cases x <;> simp [isBit]

theorem tapeOf_S5_eq_st (L : List Sym5) (hL : ∀ x ∈ L, x ≠ st) (p : ℕ) (hp : tapeOf S5 L p = st) :
    p = 0 := by
  by_contra h
  exact tapeOf_ne_st S5 (by decide) L hL p (by omega) hp

theorem enc_getElem (l : List Bool) (i : ℕ) (h : i < (enc l).length) :
    (enc l)[i] = bs (l[i]'(by simpa using h)) := by
  simp [enc]

/-- General leftward ripple, described by the bit sequences it reads and its carries. -/
theorem arSweep_runs (src dst : Fin k) (hsd : src ≠ dst) (hd0 : dst.val ≠ 0)
    (g : Bool → Bool → Bool → Bool × Bool) (T : Tapes Sym5 k)
    (P R : List Sym5) (D A : List Bool) (Rs : List Sym5)
    (hP : ∀ x ∈ P, x ≠ st) (hR : ∀ x ∈ R, x ≠ st) (hRs : ∀ x ∈ Rs, x ≠ st)
    (hcd : T.cells dst = tapeOf S5 (P ++ enc D ++ R)) (hhd : T.head dst = P.length + D.length)
    (hstop : isBit (T.cells dst P.length) = false)
    (hcs : T.cells src = tapeOf S5 (enc A ++ Rs)) (hhs : T.head src = A.length)
    (hAD : A.length ≤ D.length) :
    ∃ a b s o : ℕ → Bool, nv a D.length = val A ∧ nv b D.length = val D ∧ s 0 = false ∧
      (∀ m, s (m + 1) = (g (s m) (a m) (b m)).1) ∧ (∀ m, o m = (g (s m) (a m) (b m)).2) ∧
      Runs st (arSweep src dst g) T D.length
        ⟨Function.update T.cells dst
          (tapeOf S5 (P ++ enc (List.ofFn (fun m : Fin D.length => o (D.length - 1 - m))) ++ R)),
          fun i => if i = dst then P.length else if i = src then A.length - D.length
            else T.head i⟩ := by
  set d : Fin k → Move := fun i => if i = dst ∨ i = src then Move.left else Move.stay with hd
  have hdd : d dst = Move.left := by simp [hd]
  have hds : d src = Move.left := by simp [hd]
  have hrs : ∀ m, rd T d m src = tapeOf S5 (enc A ++ Rs) (A.length - m) := by
    intro m; simp only [rd, hds, offs, hcs, hhs]
  have hrd : ∀ m, rd T d m dst = tapeOf S5 (P ++ enc D ++ R) (P.length + D.length - m) := by
    intro m; simp only [rd, hdd, offs, hcd, hhd]
  have hDm : ∀ m (hm : m < D.length), tapeOf S5 (P ++ enc D ++ R) (P.length + D.length - m) =
      bs (D[D.length - 1 - m]'(by omega)) := by
    intro m hm
    rw [show P.length + D.length - m = (P.length + (D.length - 1 - m)) + 1 by omega]
    simp only [tapeOf]
    rw [getD_three, if_neg (by omega), if_pos (by simp; omega),
      List.getD_eq_getElem _ _ (by simp; omega)]
    simp [enc]
  set a : ℕ → Bool := fun m => dec (rd T d m src) with ha
  set b : ℕ → Bool := fun m => dec (rd T d m dst) with hb
  set s : ℕ → Bool := sst (arF src dst g) (rd T d) false with hs
  refine ⟨a, b, s, fun m => (g (s m) (a m) (b m)).2, ?_, ?_, rfl, fun m => rfl, fun m => rfl, ?_⟩
  · have := nv_read_pad A (tapeOf S5 (enc A ++ Rs)) rfl (fun i h => by
      rw [Nat.add_comm]; simp only [tapeOf]
      rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
      simp [enc]) D.length hAD
    rw [← this]; apply nv_congr; intro m _; simp only [ha, hrs]
  · have := nv_read_exact D P.length (tapeOf S5 (P ++ enc D ++ R)) (fun i h => by
      rw [show P.length + 1 + i = (P.length + i) + 1 by omega]; simp only [tapeOf]
      rw [getD_three, if_neg (by omega), if_pos (by simp; omega),
        List.getD_eq_getElem _ _ (by simp; omega)]
      simp [enc])
    rw [← this]; apply nv_congr; intro m _; simp only [hb, hrd]
  · have hnost : ∀ x ∈ P ++ enc D ++ R, x ≠ st := by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hP x hx
      · exact enc_ne_st D x hx
      · exact hR x hx
    have hnost' : ∀ x ∈ enc A ++ Rs, x ≠ st := by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact enc_ne_st A x hx
      · exact hRs x hx
    have h := sweep_runs st d dst (fun a => isBit (a dst)) false (arF src dst g) T D.length hd0
      (by simp [hdd]) (fun _ => by omega)
      (by
        intro i p hi hp
        by_cases h1 : i = dst
        · subst h1; rw [hcd] at hp; exact tapeOf_S5_eq_st _ hnost p hp
        · by_cases h2 : i = src
          · subst h2; rw [hcs] at hp; exact tapeOf_S5_eq_st _ hnost' p hp
          · simp [hd, h1, h2] at hi)
      (fun m hm => by simp only [hrd, hDm m hm, isBit_bs])
      (by
        simp only [hrd, Nat.add_sub_cancel]
        rw [hcd] at hstop; exact hstop)
      (fun m hm => by simp only [hrd, hDm m hm]; exact bs_ne_st _)
      (fun m _ => by simp only [sout, arF]; exact bs_ne_st _)
    refine Runs.of_eq h ?_ rfl
    congr 1
    · congr 1
      funext p
      rw [hdd, dcells_left _ _ _ _ _ (by omega), hhd, hcd, Nat.add_sub_cancel]
      have := congrFun (tapeOf_write_left S5 P (enc D) R
        (sout (arF src dst g) (rd T d) false)) p
      simp only [enc_length] at this
      rw [this]
      congr 3
      apply List.ext_getElem
      · simp [enc]
      · intro i h1 h2
        simp [enc, sout, arF, hs, ha, hb]
        rfl
    · funext i
      by_cases h1 : i = dst
      · subst h1; simp [hdd, offs, hhd]
      · by_cases h2 : i = src
        · subst h2; simp [hds, offs, hhs, h1]
        · simp [hd, offs, h1, h2]

/-- Full adder: carry, sum bit. -/
def addG (s a b : Bool) : Bool × Bool :=
  (decide (2 ≤ a.toNat + b.toNat + s.toNat), decide ((a.toNat + b.toNat + s.toNat) % 2 = 1))

/-- Full subtractor of `a` from `b`: borrow, difference bit. -/
def subG (s a b : Bool) : Bool × Bool :=
  (decide (b.toNat < a.toNat + s.toNat), decide ((a.toNat + b.toNat + s.toNat) % 2 = 1))

theorem addG_inv (a b s o : ℕ → Bool) (h0 : s 0 = false)
    (hs : ∀ m, s (m + 1) = (addG (s m) (a m) (b m)).1)
    (ho : ∀ m, o m = (addG (s m) (a m) (b m)).2) (L : ℕ) :
    nv o L + (s L).toNat * 2 ^ L = nv a L + nv b L := by
  induction L with
  | zero => simp [nv, h0]
  | succ L ih =>
    rw [nv_succ', nv_succ', nv_succ', hs, ho, pow_succ]
    simp only [addG]
    generalize s L = z at ih ⊢
    generalize nv a L = A at ih ⊢
    generalize nv b L = B at ih ⊢
    generalize nv o L = O at ih ⊢
    cases a L <;> cases b L <;> cases z <;> simp at ih ⊢ <;> omega

theorem subG_inv (a b s o : ℕ → Bool) (h0 : s 0 = false)
    (hs : ∀ m, s (m + 1) = (subG (s m) (a m) (b m)).1)
    (ho : ∀ m, o m = (subG (s m) (a m) (b m)).2) (L : ℕ) :
    nv o L + nv a L = nv b L + (s L).toNat * 2 ^ L := by
  induction L with
  | zero => simp [nv, h0]
  | succ L ih =>
    rw [nv_succ', nv_succ', nv_succ', hs, ho, pow_succ]
    simp only [subG]
    generalize s L = z at ih ⊢
    generalize nv a L = A at ih ⊢
    generalize nv b L = B at ih ⊢
    generalize nv o L = O at ih ⊢
    cases a L <;> cases b L <;> cases z <;> simp at ih ⊢ <;> omega

theorem ofFn_rev_eq_bin (o : ℕ → Bool) (L v : ℕ) (h : nv o L = v % 2 ^ L) :
    List.ofFn (fun m : Fin L => o (L - 1 - m)) = bin L v := by
  have := bin_of_val (List.ofFn (fun m : Fin L => o (L - 1 - m))) v
    (by rw [val_ofFn_rev, h, List.length_ofFn])
  rwa [List.length_ofFn] at this

/-- Leftward addition: `dst := src + dst` (mod `2^|dst|`). -/
theorem addSweep_runs (src dst : Fin k) (hsd : src ≠ dst) (hd0 : dst.val ≠ 0) (T : Tapes Sym5 k)
    (P R : List Sym5) (D A : List Bool) (Rs : List Sym5)
    (hP : ∀ x ∈ P, x ≠ st) (hR : ∀ x ∈ R, x ≠ st) (hRs : ∀ x ∈ Rs, x ≠ st)
    (hcd : T.cells dst = tapeOf S5 (P ++ enc D ++ R)) (hhd : T.head dst = P.length + D.length)
    (hstop : isBit (T.cells dst P.length) = false)
    (hcs : T.cells src = tapeOf S5 (enc A ++ Rs)) (hhs : T.head src = A.length)
    (hAD : A.length ≤ D.length) :
    Runs st (arSweep src dst addG) T D.length
      ⟨Function.update T.cells dst (tapeOf S5 (P ++ enc (bin D.length (val A + val D)) ++ R)),
        fun i => if i = dst then P.length else if i = src then A.length - D.length
          else T.head i⟩ := by
  obtain ⟨a, b, s, o, ha, hb, h0, hs, ho, h⟩ := arSweep_runs src dst hsd hd0 addG T P R D A Rs
    hP hR hRs hcd hhd hstop hcs hhs hAD
  rw [ofFn_rev_eq_bin o D.length (val A + val D)] at h
  · exact h
  · have hi := addG_inv a b s o h0 hs ho D.length
    rw [ha, hb] at hi
    have hl := nv_lt o D.length
    rw [← hi, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]

/-- Leftward subtraction: `dst := dst - src`, when `src ≤ dst`. -/
theorem subSweep_runs (src dst : Fin k) (hsd : src ≠ dst) (hd0 : dst.val ≠ 0) (T : Tapes Sym5 k)
    (P R : List Sym5) (D A : List Bool) (Rs : List Sym5)
    (hP : ∀ x ∈ P, x ≠ st) (hR : ∀ x ∈ R, x ≠ st) (hRs : ∀ x ∈ Rs, x ≠ st)
    (hcd : T.cells dst = tapeOf S5 (P ++ enc D ++ R)) (hhd : T.head dst = P.length + D.length)
    (hstop : isBit (T.cells dst P.length) = false)
    (hcs : T.cells src = tapeOf S5 (enc A ++ Rs)) (hhs : T.head src = A.length)
    (hAD : A.length ≤ D.length) (hle : val A ≤ val D) :
    Runs st (arSweep src dst subG) T D.length
      ⟨Function.update T.cells dst (tapeOf S5 (P ++ enc (bin D.length (val D - val A)) ++ R)),
        fun i => if i = dst then P.length else if i = src then A.length - D.length
          else T.head i⟩ := by
  obtain ⟨a, b, s, o, ha, hb, h0, hs, ho, h⟩ := arSweep_runs src dst hsd hd0 subG T P R D A Rs
    hP hR hRs hcd hhd hstop hcs hhs hAD
  rw [ofFn_rev_eq_bin o D.length (val D - val A)] at h
  · exact h
  · have hi := subG_inv a b s o h0 hs ho D.length
    rw [ha, hb] at hi
    have hl := nv_lt o D.length
    have hD := val_lt D
    have : s D.length = false := by
      cases hsl : s D.length
      · rfl
      · rw [hsl] at hi; simp at hi; omega
    rw [this] at hi
    simp at hi
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end IntMul.Mach

-- ===== KOps =====

/-!
# More sweeps on the five-symbol alphabet: ruler copy, lockstep moves, erasing, writing
-/

namespace IntMul.Mach

open IntMul IntMul.Mach.School School.Sym5

set_option linter.unusedSectionVars false

variable {k : ℕ}

/-! ## Lockstep moves -/

/-- Move the heads in directions `d` while `c` holds, rewriting nothing. -/
def lock (d : Fin k → Move) (j : Fin k) (c : (Fin k → Sym5) → Bool) : Prog Sym5 k :=
  sweep d j c () (fun _ a => ((), a j))

theorem dcells_self (base : ℕ → Sym5) (d : Move) (hd : d ≠ Move.stay) (h L : ℕ)
    (hL : d = Move.left → L ≤ h) :
    dcells base d h (fun m => base (offs d h m)) L = base := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [dcells]
    rw [ih (fun h' => by have := hL h'; omega)]
    exact Function.update_eq_self _ _

theorem lock_runs (d : Fin k → Move) (j : Fin k) (c : (Fin k → Sym5) → Bool) (T : Tapes Sym5 k)
    (L : ℕ) (hj0 : j.val ≠ 0) (hdj : d j ≠ Move.stay) (hjL : d j = Move.left → L ≤ T.head j)
    (hst : ∀ i p, d i = Move.left → T.cells i p = st → p = 0)
    (hc : ∀ m < L, c (rd T d m) = true) (hstop : c (rd T d L) = false)
    (hjst : ∀ m < L, rd T d m j ≠ st) :
    Runs st (lock d j c) T L ⟨T.cells, fun i => offs (d i) (T.head i) L⟩ := by
  have h := sweep_runs st d j c () (fun _ a => ((), a j)) T L hj0 hdj hjL hst hc hstop hjst
    (fun m hm => by simpa [sout] using hjst m hm)
  refine Runs.of_eq h ?_ rfl
  congr 1
  have e : sout (fun _ a => ((), a j)) (rd T d) () = fun m => T.cells j (offs (d j) (T.head j) m) := by
    funext m; rfl
  rw [e, dcells_self _ _ hdj _ _ hjL, Function.update_eq_self]

/-! ## Ruler copy -/

/-- Copy tape `src` onto tape `dst` while tape `r` scans `0`; all three move right. -/
def rcopy (src dst r : Fin k) : Prog Sym5 k :=
  sweep (fun i => if i = src ∨ i = dst ∨ i = r then Move.right else Move.stay) dst
    (fun a => decide (a r = zero)) () (fun _ a => ((), a src))

theorem rcopy_runs (src dst r : Fin k) (h1 : src ≠ dst) (h3 : r ≠ dst) (hd0 : dst.val ≠ 0)
    (T : Tapes Sym5 k) (X : List Sym5) (P M R : List Sym5) (hM : M.length = X.length)
    (hX : ∀ x ∈ X, x ≠ st) (hMs : ∀ x ∈ M, x ≠ st)
    (hsrc : ∀ m (hm : m < X.length), T.cells src (T.head src + m) = X[m])
    (hr : ∀ m < X.length, T.cells r (T.head r + m) = zero)
    (hrE : T.cells r (T.head r + X.length) ≠ zero)
    (hcd : T.cells dst = tapeOf S5 (P ++ M ++ R)) (hhd : T.head dst = P.length + 1) :
    Runs st (rcopy src dst r) T X.length
      ⟨Function.update T.cells dst (tapeOf S5 (P ++ X ++ R)),
        fun i => if i = src ∨ i = dst ∨ i = r then T.head i + X.length else T.head i⟩ := by
  set d : Fin k → Move := fun i => if i = src ∨ i = dst ∨ i = r then Move.right else Move.stay
    with hd
  have hdd : d dst = Move.right := by simp [hd]
  have hds : d src = Move.right := by simp [hd]
  have hdr : d r = Move.right := by simp [hd]
  have hrd : ∀ m, rd T d m dst = tapeOf S5 (P ++ M ++ R) (P.length + 1 + m) := by
    intro m; simp only [rd, hdd, offs, hcd, hhd]
  have hMm : ∀ m (hm : m < X.length), tapeOf S5 (P ++ M ++ R) (P.length + 1 + m) =
      M[m]'(by omega) := by
    intro m hm
    rw [show P.length + 1 + m = (P.length + m) + 1 by omega]
    simp only [tapeOf]
    rw [getD_three, if_neg (by omega), if_pos (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp
  have h := sweep_runs st d dst (fun a => decide (a r = zero)) () (fun _ a => ((), a src)) T
    X.length hd0 (by simp [hdd]) (by simp [hdd])
    (fun i p hi _ => by simp only [hd] at hi; split_ifs at hi)
    (fun m hm => by simp only [rd, hdr, offs]; simp [hr m hm])
    (by simp only [rd, hdr, offs]; simp [hrE])
    (fun m hm => by rw [hrd, hMm m hm]; exact hMs _ (List.getElem_mem _))
    (fun m hm => by
      simp only [sout, rd, hds, offs]
      rw [hsrc m hm]; exact hX _ (List.getElem_mem _))
  refine Runs.of_eq h ?_ rfl
  congr 1
  · congr 1
    funext p
    rw [hdd, dcells_right, hhd, hcd]
    have := congrFun (tapeOf_write_right S5 P M R (sout (fun _ a => ((), a src)) (rd T d) ())) p
    rw [hM] at this
    rw [this]
    congr 3
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_ofFn, sout, rd, hds, offs]
      exact hsrc i (by simpa using hi1)
  · funext i
    simp only [hd]
    split_ifs <;> rfl

/-! ## Erasing -/

/-- Erase tape `i` from the head down to `▷`. -/
def erase (i : Fin k) : Prog Sym5 k :=
  sweep (fun l => if l = i then Move.left else Move.stay) i (fun a => notSt (a i)) ()
    (fun _ _ => ((), blank))

theorem tapeOf_replicate_blank (n : ℕ) : tapeOf S5 (List.replicate n blank) = tapeOf S5 [] := by
  have := tapeOf_append_blanks S5 [] n
  simpa using this

theorem erase_runs (i : Fin k) (hi0 : i.val ≠ 0) (T : Tapes Sym5 k) (W : List Sym5)
    (hW : ∀ x ∈ W, x ≠ st) (hc : T.cells i = tapeOf S5 W) (hh : T.head i = W.length) :
    Runs st (erase i) T W.length
      ⟨Function.update T.cells i (tapeOf S5 []), Function.update T.head i 0⟩ := by
  set d : Fin k → Move := fun l => if l = i then Move.left else Move.stay with hd
  have hdi : d i = Move.left := by simp [hd]
  have hrd : ∀ m, rd T d m i = tapeOf S5 W (W.length - m) := by
    intro m; simp only [rd, hdi, offs, hc, hh]
  have hWm : ∀ m < W.length, tapeOf S5 W (W.length - m) ≠ st :=
    fun m hm => tapeOf_ne_st S5 (by decide) W hW _ (by omega)
  have h := sweep_runs st d i (fun a => notSt (a i)) () (fun _ _ => ((), blank)) T W.length hi0
    (by simp [hdi]) (fun _ => by omega)
    (fun l p hl hp => by
      by_cases h1 : l = i
      · subst h1; rw [hc] at hp; exact tapeOf_S5_eq_st _ hW p hp
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
    have := congrFun (tapeOf_write_left S5 [] W [] (sout (fun _ _ => ((), blank)) (rd T d) ())) p
    simp only [List.length_nil, Nat.zero_add, List.nil_append, List.append_nil] at this
    rw [Nat.sub_self, this]
    have e : (List.ofFn fun m : Fin W.length =>
        sout (fun _ _ => ((), blank)) (rd T d) () (W.length - 1 - m)) =
        List.replicate W.length blank := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2; simp [sout]
    rw [e, tapeOf_replicate_blank]
  · funext l
    by_cases h1 : l = i
    · subst h1; simp [hdi, offs, hh]
    · simp [hd, h1, offs]

/-! ## Writing one symbol -/

/-- Write `s` on tape `i` and move right. -/
def wsym (i : Fin k) (s : Sym5) : Prog Sym5 k := act (fun a => wr1 a i s Move.right)

theorem wsym_runs (i : Fin k) (hi0 : i.val ≠ 0) (s : Sym5) (hs : s ≠ st) (T : Tapes Sym5 k)
    (hT : T.cells i (T.head i) ≠ st) :
    Runs st (wsym i s) T 1
      ⟨Function.update T.cells i (Function.update (T.cells i) (T.head i) s),
        Function.update T.head i (T.head i + 1)⟩ := by
  have h1 := act_runs (st := st) (fun a => wr1 a i s Move.right) T
  rw [fix_wr1 _ _ _ _ (Or.inr ⟨hi0, hT, hs⟩), write_wr1] at h1
  exact h1

/-! ## Common head movements on encoded words -/

theorem rew_runs (i : Fin k) (T : Tapes Sym5 k) (W : List Sym5) (hW : ∀ x ∈ W, x ≠ st)
    (hc : T.cells i = tapeOf S5 W) :
    Runs st (scanL i notSt) T (T.head i) ⟨T.cells, Function.update T.head i 0⟩ := by
  have := scanL_runs st i notSt (T.head i) T le_rfl
    (fun p hp => by
      rw [hc]
      have := tapeOf_ne_st S5 (by decide) W hW (T.head i - p) (by omega)
      exact ⟨notSt_of_ne this, this⟩)
    (by rw [hc, Nat.sub_self]; rfl)
  rwa [Nat.sub_self] at this

/-- From `▷`, go to the last cell of the word. -/
def toEnd (i : Fin k) : Prog Sym5 k :=
  seq (mv i Move.right) (seq (scanR i isBit) (mv i Move.left))

theorem toEnd_runs (i : Fin k) (T : Tapes Sym5 k) (w : List Bool) (R : List Sym5)
    (hR : ∀ x ∈ R, x ≠ st) (hRb : isBit (R.getD 0 blank) = false)
    (hc : T.cells i = tapeOf S5 (enc w ++ R)) (hh : T.head i = 0) :
    Runs st (toEnd i) T (w.length + 2) ⟨T.cells, Function.update T.head i w.length⟩ := by
  have h1 := mv_runs st i Move.right T (by simp)
  have hE : tapeOf S5 (enc w ++ R) (1 + w.length) = R.getD 0 blank := by
    rw [show 1 + w.length = 1 + (enc w).length by simp, tapeOf_one_add,
      List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  have h2 := scanR_runs st i isBit w.length
    ⟨T.cells, Function.update T.head i (moveHead Move.right (T.head i))⟩
    (fun p hp => by
      simp only [Function.update_self, moveHead, hh, hc]
      rw [show 0 + 1 + p = 1 + p by omega, tapeOf_pre _ _ _ (by simpa using hp)]
      simp [enc])
    (by
      simp only [Function.update_self, moveHead, hh, hc]
      rw [show 0 + 1 + w.length = 1 + w.length by omega, hE]; exact hRb)
  have h3 := mv_runs st i Move.left
    ⟨T.cells, Function.update (Function.update T.head i (moveHead Move.right (T.head i))) i
      ((Function.update T.head i (moveHead Move.right (T.head i))) i + w.length)⟩
    (fun _ => by
      simp only [Function.update_self, moveHead, hh, hc]
      rw [show 0 + 1 + w.length = 1 + w.length by omega]
      apply tapeOf_ne_st S5 (by decide) _ _ _ (by omega)
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact enc_ne_st w x hx
      · exact hR x hx)
  refine (seq_runs h1 (seq_runs h2 h3)).of_eq ?_ (by omega)
  simp only [Function.update_idem, Function.update_self, moveHead, hh]
  congr 2; omega

/-- Lockstep right move of tapes `i` and `r` while `r` scans `0`. -/
def skipR (i r : Fin k) : Prog Sym5 k :=
  lock (fun l => if l = i ∨ l = r then Move.right else Move.stay) r (fun a => decide (a r = zero))

theorem skipR_runs (i r : Fin k) (hr0 : r.val ≠ 0) (T : Tapes Sym5 k) (L : ℕ)
    (hr : ∀ m < L, T.cells r (T.head r + m) = zero) (hrE : T.cells r (T.head r + L) ≠ zero) :
    Runs st (skipR i r) T L
      ⟨T.cells, fun l => if l = i ∨ l = r then T.head l + L else T.head l⟩ := by
  have h := lock_runs (fun l => if l = i ∨ l = r then Move.right else Move.stay) r
    (fun a => decide (a r = zero)) T L hr0 (by simp)
    (by simp) (fun l p hl _ => by split_ifs at hl)
    (fun m hm => by simp [rd, offs, hr m hm]) (by simp [rd, offs, hrE])
    (fun m hm => by simp [rd, offs, hr m hm])
  refine h.of_eq ?_ rfl
  congr 1; funext l; split_ifs <;> rfl

/-- Lockstep left move of tapes `i` and `r` until `r` scans `▷`. -/
def skipL (i r : Fin k) : Prog Sym5 k :=
  lock (fun l => if l = i ∨ l = r then Move.left else Move.stay) r (fun a => notSt (a r))

theorem skipL_runs (i r : Fin k) (hir : i ≠ r) (hr0 : r.val ≠ 0) (T : Tapes Sym5 k)
    (Wi Wr : List Sym5) (hWi : ∀ x ∈ Wi, x ≠ st) (hWr : ∀ x ∈ Wr, x ≠ st)
    (hci : T.cells i = tapeOf S5 Wi) (hcr : T.cells r = tapeOf S5 Wr)
    (hhr : T.head r = Wr.length) (hle : Wr.length ≤ T.head i) :
    Runs st (skipL i r) T Wr.length
      ⟨T.cells, fun l => if l = i ∨ l = r then T.head l - Wr.length else T.head l⟩ := by
  have hrr : ∀ m, T.cells r (offs Move.left (T.head r) m) = tapeOf S5 Wr (Wr.length - m) := by
    intro m; simp [offs, hcr, hhr]
  have hdr : (if r = i ∨ r = r then Move.left else Move.stay) = Move.left := by simp
  have h := lock_runs (fun l => if l = i ∨ l = r then Move.left else Move.stay) r
    (fun a => notSt (a r)) T Wr.length hr0 (by simp) (by simp [hhr])
    (fun l p hl hp => by
      by_cases h1 : l = r
      · subst h1; rw [hcr] at hp; exact tapeOf_S5_eq_st _ hWr p hp
      · by_cases h2 : l = i
        · subst h2; rw [hci] at hp; exact tapeOf_S5_eq_st _ hWi p hp
        · simp [h1, h2] at hl)
    (fun m hm => by
      simp only [rd, or_true, if_true]; rw [hrr]
      exact notSt_of_ne (tapeOf_ne_st S5 (by decide) Wr hWr _ (by omega)))
    (by simp only [rd, or_true, if_true]; rw [hrr, Nat.sub_self]; rfl)
    (fun m hm => by
      simp only [rd, or_true, if_true]; rw [hrr]
      exact tapeOf_ne_st S5 (by decide) Wr hWr _ (by omega))
  refine h.of_eq ?_ rfl
  congr 1; funext l; split_ifs <;> rfl

end IntMul.Mach

-- ===== Halve =====

/-!
# Halving sweep

Tape `i` moves right while it scans a symbol satisfying `isB`; on every other step tape `j`
writes `z` and moves right.
-/

namespace IntMul.Mach

/-- Move tape `i` right while `isB` holds; on steps `0, 2, 4, …` write `z` on tape `j` and move
right. -/
def halve {Γ : Type} {k : ℕ} [DecidableEq Γ] (i j : Fin k) (isB : Γ → Bool) (z : Γ) :
    Prog Γ k where
  Q := Bool
  q0 := false
  δ s a := if isB (a i) then some (!s, fun l =>
      if l = i then (a i, Move.right)
      else if l = j ∧ s = false then (z, Move.right) else (a l, Move.stay)) else none

theorem halve_runs {Γ : Type} {k : ℕ} [DecidableEq Γ] (st : Γ) (i j : Fin k) (hij : i ≠ j)
    (hj : j.val ≠ 0) (isB : Γ → Bool) (z : Γ) (hz : z ≠ st) (T : Tapes Γ k) (n : ℕ)
    (hB : ∀ m < n, isB (T.cells i (T.head i + m)) = true)
    (hE : isB (T.cells i (T.head i + n)) = false)
    (hjst : ∀ m < (n + 1) / 2, T.cells j (T.head j + m) ≠ st) :
    Runs st (halve i j isB z) T n
      ⟨Function.update T.cells j (fun p =>
          if T.head j ≤ p ∧ p < T.head j + (n + 1) / 2 then z else T.cells j p),
        Function.update (Function.update T.head i (T.head i + n)) j (T.head j + (n + 1) / 2)⟩ := by
  let Ts : ℕ → Tapes Γ k := fun m =>
    ⟨Function.update T.cells j (fun p =>
          if T.head j ≤ p ∧ p < T.head j + (m + 1) / 2 then z else T.cells j p),
        Function.update (Function.update T.head i (T.head i + m)) j (T.head j + (m + 1) / 2)⟩
  have hji : j ≠ i := fun h => hij h.symm
  have hread : ∀ m, (Ts m).read = fun l =>
      if l = i then T.cells i (T.head i + m)
      else if l = j then T.cells j (T.head j + (m + 1) / 2) else T.cells l (T.head l) := by
    intro m
    funext l
    simp only [Ts, Tapes.read]
    by_cases hl : l = j
    · subst hl
      simp [hji]
    · by_cases hli : l = i
      · subst hli
        simp [hl]
      · simp [hl, hli]
  have hri : ∀ m, (Ts m).read i = T.cells i (T.head i + m) := fun m => by
    rw [hread]; simp
  have hrj : ∀ m, (Ts m).read j = T.cells j (T.head j + (m + 1) / 2) := fun m => by
    rw [hread]; simp [hji]
  have h := halts_of_traj (st := st) (halve i j isB z) n (fun m => Nat.bodd m) Ts ?_ ?_
  · have e0 : Ts 0 = T := by
      have hf : (fun p => if T.head j ≤ p ∧ p < T.head j then z
          else T.cells j p) = T.cells j := by
        funext p; rw [if_neg (by omega)]
      simp only [Ts, Nat.add_zero, Nat.zero_add, Nat.reduceDiv]
      rw [hf]
      simp only [Function.update_eq_self]
    rw [e0] at h
    exact h
  · intro m hm
    refine ⟨fun l => if l = i then ((Ts m).read i, Move.right)
      else if l = j ∧ Nat.bodd m = false then (z, Move.right) else ((Ts m).read l, Move.stay),
      ?_, ?_⟩
    · simp only [halve]
      rw [hri, hB m hm]
      simp [Nat.bodd_succ]
    · have hmod := Nat.mod_two_of_bodd m
      rw [hread m]
      simp only [Tapes.write, Ts]
      congr 1
      · funext l
        by_cases hl : l = j
        · subst hl
          funext p
          rcases hb : Nat.bodd m with _ | _ <;> rw [hb] at hmod <;>
            simp only [Bool.toNat_false, Bool.toNat_true] at hmod
          · have hlt : (m + 1) / 2 < (n + 1) / 2 := by omega
            have hne := hjst _ hlt
            have e : (m + 1 + 1) / 2 = (m + 1) / 2 + 1 := by omega
            simp only [Function.update_self, fix, hji, if_false, if_true, and_self, hne, hz,
              hj, false_or, e]
            by_cases hp : p = T.head l + (m + 1) / 2
            · subst hp
              simp
            · rw [Function.update_of_ne hp]
              split_ifs <;> first | rfl | omega
          · have e : (m + 1 + 1) / 2 = (m + 1) / 2 := by omega
            simp only [Function.update_self, fix, hji, if_false, if_true, e]
            by_cases hp : p = T.head l + (m + 1) / 2
            · subst hp
              split_ifs <;> simp_all
            · rw [Function.update_of_ne hp]
        · rw [Function.update_of_ne hl, Function.update_of_ne hl]
          funext p
          by_cases hli : l = i
          · subst hli
            simp only [Function.update_of_ne hl, Function.update_self, fix, if_true]
            by_cases hp : p = T.head l + m
            · subst hp; split_ifs <;> simp_all
            · rw [Function.update_of_ne hp]
          · simp only [Function.update_of_ne hl, Function.update_of_ne hli, fix, hli, hl,
              if_false, false_and]
            by_cases hp : p = T.head l
            · subst hp; split_ifs <;> simp_all
            · rw [Function.update_of_ne hp]
      · funext l
        by_cases hl : l = j
        · subst hl
          rcases hb : Nat.bodd m with _ | _ <;> rw [hb] at hmod <;>
            simp only [Bool.toNat_false, Bool.toNat_true] at hmod <;>
            simp only [Function.update_self, fix, hji, if_false, if_true, and_true, and_false] <;>
            split_ifs <;> simp_all [moveHead] <;> omega
        · rw [Function.update_of_ne hl, Function.update_of_ne hl]
          by_cases hli : l = i
          · subst hli
            simp only [Function.update_of_ne hl, Function.update_self, fix, if_true]
            split_ifs <;> simp [moveHead] <;> omega
          · rw [Function.update_of_ne hli, Function.update_of_ne hli]
            simp only [fix, hli, hl, if_false, false_and]
            split_ifs <;> simp [moveHead]
  · simp only [halve]
    rw [hri, hE]
    simp

end IntMul.Mach

-- ===== Lift =====

/-!
# Lifting a `k`-tape program to `k'` tapes

Tapes `i < k` are driven by the original program; tapes `≥ k` are left untouched (the scanned
symbol is written back and the head stays).
-/

namespace IntMul.Mach

open IntMul

/-- Lift a `k`-tape program to `k' ≥ k` tapes. -/
def liftProg {Γ : Type} {k k' : ℕ} (hk : k ≤ k') (P : Prog Γ k) : Prog Γ k' where
  Q := P.Q
  q0 := P.q0
  δ q a := (P.δ q (fun i => a (Fin.castLE hk i))).map (fun r =>
    (r.1, fun i => if h : i.val < k then r.2 ⟨i.val, h⟩ else (a i, Move.stay)))

theorem liftProg_halts {Γ : Type} [DecidableEq Γ] (st : Γ) {k k' : ℕ} (hk : k ≤ k') (P : Prog Γ k)
    {q : P.Q} {T T' : Tapes Γ k} {t : ℕ} (h : Halts st P q T t T')
    (U : Tapes Γ k') (hc : ∀ i : Fin k, U.cells (Fin.castLE hk i) = T.cells i)
    (hh : ∀ i : Fin k, U.head (Fin.castLE hk i) = T.head i) :
    Halts st (liftProg hk P) q U t
      ⟨fun i => if h : i.val < k then T'.cells ⟨i.val, h⟩ else U.cells i,
       fun i => if h : i.val < k then T'.head ⟨i.val, h⟩ else U.head i⟩ := by
  induction h generalizing U with
  | @done q T h0 =>
    have hr : (fun i => U.read (Fin.castLE hk i)) = T.read := by
      funext i; simp [Tapes.read, hc, hh]
    have e : (⟨fun i => if h : i.val < k then T.cells ⟨i.val, h⟩ else U.cells i,
        fun i => if h : i.val < k then T.head ⟨i.val, h⟩ else U.head i⟩ : Tapes Γ k') = U := by
      cases U with
      | mk c hd =>
        congr 1
        · funext i; split_ifs with h
          · exact (hc ⟨i.val, h⟩).symm
          · rfl
        · funext i; split_ifs with h
          · exact (hh ⟨i.val, h⟩).symm
          · rfl
    rw [e]
    exact Halts.done (by simp [liftProg, hr, h0])
  | @step q q' T T₁ w t h0 _ ih =>
    have hr : (fun i => U.read (Fin.castLE hk i)) = T.read := by
      funext i; simp [Tapes.read, hc, hh]
    set w' : Fin k' → Γ × Move :=
      fun i => if h : i.val < k then w ⟨i.val, h⟩ else (U.read i, Move.stay) with hw'
    have hδ : (liftProg hk P).δ q U.read = some (q', w') := by
      simp [liftProg, hr, h0, w']
    have hfix : ∀ i : Fin k', fix st U.read w' i =
        if h : i.val < k then fix st T.read w ⟨i.val, h⟩ else (U.read i, Move.stay) := by
      intro i
      by_cases h : i.val < k
      · have hu : U.read i = T.read ⟨i.val, h⟩ := by
          rw [← hr]; rfl
        simp only [fix, w', dif_pos h, hu]
      · simp only [fix, w', dif_neg h]
        split_ifs <;> simp_all
    have := ih (U.write (fix st U.read w'))
      (by
        intro i
        simp only [Tapes.write, hfix, Fin.val_castLE, dif_pos i.isLt, hc, hh])
      (by
        intro i
        simp only [Tapes.write, hfix, Fin.val_castLE, dif_pos i.isLt, hh])
    refine Halts.step hδ ?_
    convert this using 2
    · funext i; split_ifs with h
      · rfl
      · simp [Tapes.write, hfix, h, Tapes.read]
    · funext i; split_ifs with h
      · rfl
      · simp [Tapes.write, hfix, h, moveHead]

theorem liftProg_runs {Γ : Type} [DecidableEq Γ] (st : Γ) {k k' : ℕ} (hk : k ≤ k') (P : Prog Γ k)
    {T T' : Tapes Γ k} {t : ℕ} (h : Runs st P T t T')
    (U : Tapes Γ k') (hc : ∀ i : Fin k, U.cells (Fin.castLE hk i) = T.cells i)
    (hh : ∀ i : Fin k, U.head (Fin.castLE hk i) = T.head i) :
    Runs st (liftProg hk P) U t
      ⟨fun i => if h : i.val < k then T'.cells ⟨i.val, h⟩ else U.cells i,
       fun i => if h : i.val < k then T'.head ⟨i.val, h⟩ else U.head i⟩ :=
  liftProg_halts st hk P h U hc hh

end IntMul.Mach

-- ===== Rec =====

/-!
# Segmented bodies for the flat recursive scheduler

A body is a list of programs `P 0, …, P m`.  When `P i` halts the body either halts
(always for `i = m`, and for `i < m` when `stop i` holds of the scanned symbols) or enters
the request state `i`; the scheduler resumes at the start of `P (i+1)`.
-/

namespace IntMul.Mach

open IntMul IntMul.FlatRecursiveEvaluation IntMul.TrackedBankedSimulation

variable {Γ : Type} {k : ℕ} [DecidableEq Γ] [Fintype Γ]

/-- States of a segmented body; `none` is `HALT`. -/
abbrev BodyK {m : ℕ} (P : Fin (m + 1) → Prog Γ k) := Option ((Σ i : Fin (m + 1), (P i).Q) ⊕ Fin m)

/-- What happens when segment `i` halts on scanned symbols `a`. -/
def segExit {m : ℕ} (P : Fin (m + 1) → Prog Γ k) (stop : Fin (m + 1) → (Fin k → Γ) → Bool)
    (i : Fin (m + 1)) (a : Fin k → Γ) : BodyK P :=
  if h : i.val < m then (if stop i a then none else some (Sum.inr ⟨i.val, h⟩)) else none

/-- Keep every symbol and every head. -/
def keepAll (a : Fin k → Γ) : Fin k → Γ × Move := fun i => (a i, Move.stay)

def bodyδ {m : ℕ} (S : Syms Γ) (P : Fin (m + 1) → Prog Γ k)
    (stop : Fin (m + 1) → (Fin k → Γ) → Bool) (q : BodyK P) (a : Fin k → Γ) :
    BodyK P × (Fin k → Γ × Move) :=
  match q with
  | some (Sum.inl ⟨i, q⟩) => match (P i).δ q a with
    | some r => (some (Sum.inl ⟨i, r.1⟩), fix S.st a r.2)
    | none => (segExit P stop i a, keepAll a)
  | some (Sum.inr j) => (some (Sum.inr j), keepAll a)
  | none => (none, keepAll a)

theorem fix_constraints (st : Γ) (a : Fin k → Γ) (w : Fin k → Γ × Move) (i : Fin k) :
    (a i = st → ((fix st a w i).1 = st ∧ (fix st a w i).2 ≠ Move.left)) ∧
    (a i ≠ st → (fix st a w i).1 ≠ st) ∧ (i.val = 0 → (fix st a w i).1 = a i) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp only [fix, h, if_true]; split_ifs <;> simp_all
  · simp only [fix, h, if_false]; split_ifs <;> simp_all
  · simp only [fix]; split_ifs <;> simp_all

/-- The body machine. -/
def body {m : ℕ} (S : Syms Γ) (hk : 2 ≤ k) (P : Fin (m + 1) → Prog Γ k)
    (stop : Fin (m + 1) → (Fin k → Γ) → Bool) : MultitapeTM where
  Sym := Γ
  blank := S.blank
  startSym := S.st
  zero := S.zero
  one := S.one
  sep := S.sep
  syms_distinct := S.nodup
  K := BodyK P
  qStart := some (Sum.inl ⟨0, (P 0).q0⟩)
  qHalt := none
  start_ne_halt := by simp
  k := k
  two_le_k := hk
  δ := bodyδ S P stop
  start_preserved := by
    intro q a i hi
    rcases q with _ | (⟨j, q⟩ | j)
    · simp [bodyδ, keepAll, hi]
    · simp only [bodyδ]
      rcases h : (P j).δ q a with _ | r <;> simp only [h]
      · simp [keepAll, hi]
      · exact (fix_constraints S.st a r.2 i).1 hi
    · simp [bodyδ, keepAll, hi]
  start_only_at_start := by
    intro q a i hi
    rcases q with _ | (⟨j, q⟩ | j)
    · simpa [bodyδ, keepAll] using hi
    · simp only [bodyδ]
      rcases h : (P j).δ q a with _ | r <;> simp only [h]
      · simpa [keepAll] using hi
      · exact (fix_constraints S.st a r.2 i).2.1 hi
    · simpa [bodyδ, keepAll] using hi
  halt_fixed := fun _ => rfl
  input_readonly := by
    intro q a
    rcases q with _ | (⟨j, q⟩ | j)
    · rfl
    · simp only [bodyδ]
      rcases h : (P j).δ q a with _ | r <;> simp only [h]
      · rfl
      · exact (fix_constraints S.st a r.2 _).2.2 rfl
    · rfl

/-- Request labels. -/
def bodyRequest {m : ℕ} (P : Fin (m + 1) → Prog Γ k) : BodyK P → Option (Fin m)
  | some (Sum.inr j) => some j
  | _ => none

/-- Resume at the start of the next segment. -/
def bodyResume {m : ℕ} (P : Fin (m + 1) → Prog Γ k) (j : Fin m) : BodyK P :=
  some (Sum.inl ⟨j.succ.castLT (by have := j.isLt; simp), (P _).q0⟩)

section Bridge

variable {m : ℕ} (S : Syms Γ) (hk : 2 ≤ k) (P : Fin (m + 1) → Prog Γ k)
  (stop : Fin (m + 1) → (Fin k → Γ) → Bool)

/-- A body configuration from tapes. -/
def bcfg (q : BodyK P) (T : Tapes Γ k) : (body S hk P stop).Cfg := ⟨q, T.cells, T.head⟩

/-- Extents along a trajectory, computed from the start. -/
noncomputable def extFrom (M : MultitapeTM) : M.Cfg → (Fin M.k → ℕ) → ℕ → Fin M.k → ℕ
  | _, E, 0 => E
  | c, E, t + 1 => extFrom M (M.step c) (nextExtent M c E) t

theorem extFrom_succ (M : MultitapeTM) (c : M.Cfg) (E : Fin M.k → ℕ) (t : ℕ) :
    extFrom M c E (t + 1) = extFrom M (M.step c) (nextExtent M c E) t := rfl

theorem body_step_seg (i : Fin (m + 1)) (q q' : (P i).Q) (T : Tapes Γ k) (w : Fin k → Γ × Move)
    (h : (P i).δ q T.read = some (q', w)) :
    (body S hk P stop).step (bcfg S hk P stop (some (Sum.inl ⟨i, q⟩)) T) =
      bcfg S hk P stop (some (Sum.inl ⟨i, q'⟩)) (T.write (fix S.st T.read w)) := by
  have h' : (P i).δ q (fun j => T.cells j (T.head j)) = some (q', w) := h
  simp only [MultitapeTM.step, bcfg, body, bodyδ, h', Tapes.write]
  rfl

theorem body_step_exit (i : Fin (m + 1)) (q : (P i).Q) (T : Tapes Γ k)
    (h : (P i).δ q T.read = none) :
    (body S hk P stop).step (bcfg S hk P stop (some (Sum.inl ⟨i, q⟩)) T) =
      bcfg S hk P stop (segExit P stop i T.read) T := by
  have h' : (P i).δ q (fun j => T.cells j (T.head j)) = none := h
  simp only [MultitapeTM.step, bcfg, body, bodyδ, h']
  congr 1
  funext j; simp [keepAll]

/-- The bridge: a halting run of segment `i` becomes `t + 1` ordinary scheduler steps. -/
theorem evaluates_of_halts {labels : ℕ} (hl : labels = m) (i : Fin (m + 1)) {q : (P i).Q}
    {T T' : Tapes Γ k} {t : ℕ} (h : Halts S.st (P i) q T t T')
    (request : BodyK P → Option (Fin labels)) (hreq : ∀ i q, request (some (Sum.inl ⟨i, q⟩)) = none)
    (resume : Fin labels → BodyK P) (E : Fin k → ℕ) (v w : List Bool) (B : ℕ)
    (hB : Evaluates (body S hk P stop) labels request resume
      (extFrom (body S hk P stop) (bcfg S hk P stop (some (Sum.inl ⟨i, q⟩)) T) E (t + 1))
      (bcfg S hk P stop (segExit P stop i T'.read) T') v w B) :
    Evaluates (body S hk P stop) labels request resume E
      (bcfg S hk P stop (some (Sum.inl ⟨i, q⟩)) T) v w (B + (t + 1)) := by
  induction h generalizing E B with
  | done h0 =>
    refine Evaluates.step _ _ _ _ _ (by simp [bcfg, body]) (hreq _ _) ?_
    rw [body_step_exit S hk P stop _ _ _ h0]
    exact hB
  | step h0 _ ih =>
    rw [← Nat.add_assoc]
    refine Evaluates.step _ _ _ _ _ (by simp [bcfg, body]) (hreq _ _) ?_
    rw [body_step_seg S hk P stop _ _ _ _ _ h0]
    apply ih
    convert hB using 2
    exact (congrArg (fun c => extFrom _ c _ _) (body_step_seg S hk P stop _ _ _ _ _ h0)).symm

end Bridge

end IntMul.Mach

-- ===== KRec =====

namespace IntMul.Mach

/-- The Karatsuba cost bound: children of sizes ⌈n/2⌉, ⌊n/2⌋, ⌈n/2⌉+1 plus linear work. -/
def kb (a b c : ℕ) : ℕ → ℕ
  | n => if n ≤ 3 then c else
      kb a b c (n - n / 2) + kb a b c (n / 2) + kb a b c (n - n / 2 + 1) + a * n + b
termination_by n => n
decreasing_by all_goals omega

lemma kb_small (a b c m : ℕ) (h : m ≤ 3) : kb a b c m = c := by
  rw [kb, if_pos h]

lemma kb_le4 (a b c n : ℕ) (h : n ≤ 4) : kb a b c n ≤ 3 * c + 4 * a + b := by
  by_cases h3 : n ≤ 3
  · rw [kb_small _ _ _ _ h3]; omega
  · obtain rfl : n = 4 := by omega
    rw [kb, if_neg (by norm_num)]
    show kb a b c 2 + kb a b c 2 + kb a b c 3 + a * 4 + b ≤ _
    rw [kb_small a b c 2 (by norm_num), kb_small a b c 3 (by norm_num)]
    omega

lemma kb_aux (a b c : ℕ) (K L : ℝ) (hL : (2 * a + b : ℝ) ≤ L) (hL0 : 0 ≤ L)
    (hK : (3 * c + 4 * a + b : ℝ) + 4 * L ≤ K) (n : ℕ) :
    (kb a b c n : ℝ) ≤ K * (max ((n : ℝ) - 3) 1) ^ Real.logb 2 3 - L * n := by
  have hα : 0 ≤ Real.logb 2 3 := Real.logb_nonneg one_lt_two (by norm_num)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hK0 : 0 ≤ K := by linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hn : n ≤ 4
  · have h1 : ((kb a b c n : ℕ) : ℝ) ≤ ((3 * c + 4 * a + b : ℕ) : ℝ) := by
      exact_mod_cast kb_le4 a b c n hn
    push_cast at h1
    have hn' : (n : ℝ) ≤ 4 := by exact_mod_cast hn
    rw [max_eq_right (by linarith), Real.one_rpow]
    nlinarith
  · push_neg at hn
    have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have key : ∀ m : ℕ, m ≤ n - n / 2 + 1 →
        (max ((m : ℝ) - 3) 1) ^ Real.logb 2 3 ≤ ((n : ℝ) - 3) ^ Real.logb 2 3 / 3 := by
      intro m hm
      have h2 : ((2 * m : ℕ) : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega)
      push_cast at h2
      have hle : max ((m : ℝ) - 3) 1 ≤ ((n : ℝ) - 3) / 2 :=
        max_le (by linarith) (by linarith)
      calc (max ((m : ℝ) - 3) 1) ^ Real.logb 2 3
          ≤ (((n : ℝ) - 3) / 2) ^ Real.logb 2 3 :=
            Real.rpow_le_rpow (le_trans zero_le_one (le_max_right _ _)) hle hα
        _ = ((n : ℝ) - 3) ^ Real.logb 2 3 / 3 := by
            rw [Real.div_rpow (by linarith) (by norm_num),
              Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
    have i1 := ih (n - n / 2) (by omega)
    have i2 := ih (n / 2) (by omega)
    have i3 := ih (n - n / 2 + 1) (by omega)
    have k1 := mul_le_mul_of_nonneg_left (key (n - n / 2) (by omega)) hK0
    have k2 := mul_le_mul_of_nonneg_left (key (n / 2) (by omega)) hK0
    have k3 := mul_le_mul_of_nonneg_left (key (n - n / 2 + 1) (by omega)) hK0
    have hS : ((3 * n + 2 : ℕ) : ℝ) ≤
        ((2 * ((n - n / 2) + n / 2 + (n - n / 2 + 1)) : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    rw [kb, if_neg (by omega), max_eq_left (by linarith)]
    push_cast at hS i1 i2 i3 k1 k2 k3 ⊢
    generalize ((n - n / 2 : ℕ) : ℝ) = x1 at *
    generalize ((n / 2 : ℕ) : ℝ) = x2 at *
    generalize ((kb a b c (n - n / 2) : ℕ) : ℝ) = y1 at *
    generalize ((kb a b c (n / 2) : ℕ) : ℝ) = y2 at *
    generalize ((kb a b c (n - n / 2 + 1) : ℕ) : ℝ) = y3 at *
    generalize ((n : ℝ) - 3) ^ Real.logb 2 3 = Y at *
    have e1 := mul_le_mul_of_nonneg_left hS hL0
    have e2 : 0 ≤ (L - (2 * a + b)) * ((n : ℝ) + 2) := mul_nonneg (by linarith) (by linarith)
    have e3 : 0 ≤ (b : ℝ) * n := mul_nonneg hb (by linarith)
    nlinarith

theorem kb_bound (a b c : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → (kb a b c n : ℝ) ≤ C * (n : ℝ) ^ Real.logb 2 3 := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  set L : ℝ := 2 * a + b with hLdef
  set K : ℝ := (3 * c + 4 * a + b : ℝ) + 4 * L + 1 with hKdef
  refine ⟨K, by positivity, fun n hn => ?_⟩
  have h := kb_aux a b c K L le_rfl (by positivity) (by linarith) n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα : 0 ≤ Real.logb 2 3 := Real.logb_nonneg one_lt_two (by norm_num)
  have hmono : (max ((n : ℝ) - 3) 1) ^ Real.logb 2 3 ≤ (n : ℝ) ^ Real.logb 2 3 :=
    Real.rpow_le_rpow (le_trans zero_le_one (le_max_right _ _))
      (max_le (by linarith) hn') hα
  have hK0 : 0 ≤ K := by positivity
  have hLn : 0 ≤ L * n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hK0]

end IntMul.Mach

-- ===== Kara =====

/-!
# Karatsuba multiplication: the segment programs

Tapes: `0` input, `1` output/packets, `2` ruler `0^u` (`u = ⌈n/2⌉`), `3` `P₁` then the result,
`4` `P₂`, `5` `x_L`, `6` `y_L`.
-/

namespace IntMul.Mach.Kara

open IntMul IntMul.Mach IntMul.Mach.School School.Sym5

set_option linter.unusedSectionVars false

def mk7 (c0 c1 c2 c3 c4 c5 c6 : ℕ → Sym5) (h0 h1 h2 h3 h4 h5 h6 : ℕ) : Tapes Sym5 7 :=
  ⟨![c0, c1, c2, c3, c4, c5, c6], ![h0, h1, h2, h3, h4, h5, h6]⟩

theorem mk7_ext {T : Tapes Sym5 7} {c0 c1 c2 c3 c4 c5 c6 : ℕ → Sym5} {h0 h1 h2 h3 h4 h5 h6 : ℕ}
    (e0 : T.cells 0 = c0) (e1 : T.cells 1 = c1) (e2 : T.cells 2 = c2) (e3 : T.cells 3 = c3)
    (e4 : T.cells 4 = c4) (e5 : T.cells 5 = c5) (e6 : T.cells 6 = c6)
    (f0 : T.head 0 = h0) (f1 : T.head 1 = h1) (f2 : T.head 2 = h2) (f3 : T.head 3 = h3)
    (f4 : T.head 4 = h4) (f5 : T.head 5 = h5) (f6 : T.head 6 = h6) :
    T = mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6 := by
  cases T with
  | mk cells head =>
    simp only [mk7, Tapes.mk.injEq]
    constructor <;> funext i <;> fin_cases i <;> simp_all

section
variable (c0 c1 c2 c3 c4 c5 c6 : ℕ → Sym5) (h0 h1 h2 h3 h4 h5 h6 : ℕ)
@[simp] theorem mk7_c0 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).cells 0 = c0 := rfl
@[simp] theorem mk7_c1 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).cells 1 = c1 := rfl
@[simp] theorem mk7_c2 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).cells 2 = c2 := rfl
@[simp] theorem mk7_c3 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).cells 3 = c3 := rfl
@[simp] theorem mk7_c4 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).cells 4 = c4 := rfl
@[simp] theorem mk7_c5 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).cells 5 = c5 := rfl
@[simp] theorem mk7_c6 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).cells 6 = c6 := rfl
@[simp] theorem mk7_h0 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).head 0 = h0 := rfl
@[simp] theorem mk7_h1 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).head 1 = h1 := rfl
@[simp] theorem mk7_h2 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).head 2 = h2 := rfl
@[simp] theorem mk7_h3 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).head 3 = h3 := rfl
@[simp] theorem mk7_h4 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).head 4 = h4 := rfl
@[simp] theorem mk7_h5 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).head 5 = h5 := rfl
@[simp] theorem mk7_h6 : (mk7 c0 c1 c2 c3 c4 c5 c6 h0 h1 h2 h3 h4 h5 h6).head 6 = h6 := rfl
end

/-! ## Input tape facts -/

section Input
variable (x y : List Bool)

theorem I_x (p : ℕ) (hp : p < x.length) : I x y (1 + p) = bs x[p] := by
  rw [I, tapeOf_pre _ _ _ (by simpa using hp)]; simp [enc]

theorem I_sep : I x y (1 + x.length) = sep := by
  rw [I, show x.length = (enc x).length by simp, tapeOf_at]

theorem I_nost : ∀ z ∈ enc x ++ sep :: enc y, z ≠ st := by
  intro z hz
  simp only [List.mem_append, List.mem_cons] at hz
  rcases hz with hz | rfl | hz
  · exact enc_ne_st x z hz
  · decide
  · exact enc_ne_st y z hz

end Input

theorem tapeOf_get1 (L : List Sym5) (p : ℕ) (hp : p < L.length) : tapeOf S5 L (1 + p) = L[p] := by
  rw [tapeOf_one_add, List.getD_eq_getElem _ _ hp]

theorem enc_replicate_false (n : ℕ) : enc (List.replicate n false) = List.replicate n zero := by
  simp [enc, bs]

theorem E_eq_replicate (n : ℕ) : E = tapeOf S5 ([] ++ List.replicate n blank ++ []) := by
  simp only [List.nil_append, List.append_nil]
  exact (tapeOf_replicate_blank n).symm

theorem nost_enc (w : List Bool) : ∀ z ∈ enc w, z ≠ st := enc_ne_st w

theorem nost_rep (n : ℕ) (s : Sym5) (hs : s ≠ st) : ∀ z ∈ List.replicate n s, z ≠ st := by
  intro z hz; rw [List.eq_of_mem_replicate hz]; exact hs

/-! ## Segment 0, large inputs: the packet `x_H # y_H` -/

def large0 : Prog Sym5 7 :=
  seq (mv 0 Move.right) <| seq (mv 2 Move.right) <| seq (halve 0 2 isBit zero) <|
  seq (scanL 0 notSt) <| seq (mv 0 Move.right) <| seq (scanL 2 notSt) <| seq (mv 2 Move.right) <|
  seq (mv 1 Move.right) <| seq (rcopy 0 1 2) <| seq (wsym 1 sep) <|
  seq (scanR 0 isBit) <| seq (mv 0 Move.right) <| seq (scanL 2 notSt) <|
  seq (mv 2 Move.right) (rcopy 0 1 2)

theorem ruler_eq (u : ℕ) :
    (fun p => if 1 ≤ p ∧ p < 1 + u then zero else E p) = tapeOf S5 (enc (List.replicate u false)) := by
  rw [enc_replicate_false]
  have := tapeOf_write_right S5 [] (List.replicate u blank) [] (fun _ => zero)
  simp only [List.length_nil, Nat.zero_add, List.length_replicate, List.nil_append,
    List.append_nil, tapeOf_replicate_blank] at this
  rw [E, this]
  congr 1
  apply List.ext_getElem <;> simp

theorem large0_runs (x y : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length) :
    Runs st large0 (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0)
      (3 * x.length + 3 * ((x.length + 1) / 2) + 11)
      (mk7 (I x y)
        (tapeOf S5 (enc (x.take ((x.length + 1) / 2)) ++ sep :: enc (y.take ((x.length + 1) / 2))))
        (tapeOf S5 (enc (List.replicate ((x.length + 1) / 2) false))) E E E E
        (x.length + 2 + (x.length + 1) / 2) (2 * ((x.length + 1) / 2) + 2)
        ((x.length + 1) / 2 + 1) 0 0 0 0) := by
  have hu : (x.length + 1) / 2 ≤ x.length := by omega
  have hu1 : 1 ≤ (x.length + 1) / 2 := by omega
  set n := x.length with hn
  set u := (n + 1) / 2 with hu_def
  set Ru := tapeOf S5 (enc (List.replicate u false)) with hRu
  have hRuz : ∀ m < u, Ru (1 + m) = zero := by
    intro m hm; rw [hRu, tapeOf_get1 _ _ (by simpa using hm)]; simp [enc, bs]
  have hRuE : Ru (1 + u) = blank := by
    rw [hRu, show 1 + u = 1 + (enc (List.replicate u false)).length by simp, tapeOf_end]
  have hlx : (x.take u).length = u := by simp; omega
  have hly : (y.take u).length = u := by simp; omega
  have h1 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E 1 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h2 := (mv_runs st 2 Move.right (mk7 (I x y) E E E E E E 1 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E 1 0 1 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h3 := (halve_runs st 0 2 (by decide) (by decide) isBit zero (by decide)
    (mk7 (I x y) E E E E E E 1 0 1 0 0 0 0) n
    (fun m hm => by simp only [mk7_c0, mk7_h0]; rw [I_x x y m hm]; simp)
    (by simp only [mk7_c0, mk7_h0]; rw [I_sep]; rfl)
    (fun m _ => by simp [E, tapeOf, show 1 + m = m + 1 by omega])).of_eq
    (T'' := mk7 (I x y) E Ru E E E E (1 + n) 0 (1 + u) 0 0 0 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply] <;> first | exact ruler_eq _ | omega) rfl
  have h4 := (rew_runs 0 (mk7 (I x y) E Ru E E E E (1 + n) 0 (1 + u) 0 0 0 0) _ (I_nost x y)
    rfl).of_eq (T'' := mk7 (I x y) E Ru E E E E 0 0 (1 + u) 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have h5 := (mv_runs st 0 Move.right (mk7 (I x y) E Ru E E E E 0 0 (1 + u) 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru E E E E 1 0 (1 + u) 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h6 := (rew_runs 2 (mk7 (I x y) E Ru E E E E 1 0 (1 + u) 0 0 0 0) _ (nost_enc _)
    rfl).of_eq (T'' := mk7 (I x y) E Ru E E E E 1 0 0 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have h7 := (mv_runs st 2 Move.right (mk7 (I x y) E Ru E E E E 1 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru E E E E 1 0 1 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h8 := (mv_runs st 1 Move.right (mk7 (I x y) E Ru E E E E 1 0 1 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru E E E E 1 1 1 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h9 := (rcopy_runs 0 1 2 (by decide) (by decide) (by decide)
    (mk7 (I x y) E Ru E E E E 1 1 1 0 0 0 0) (enc (x.take u)) [] (List.replicate u blank) []
    (by simp [hlx]) (nost_enc _) (nost_rep _ _ (by decide))
    (fun m hm => by
      simp only [mk7_c0, mk7_h0]
      simp only [enc_length, hlx] at hm
      rw [I_x x y m (by omega)]; simp [enc])
    (fun m hm => by simp only [mk7_c2, mk7_h2]; simp only [enc_length, hlx] at hm; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, enc_length, hlx, hRuE]; decide)
    (by simp only [mk7_c1]; exact E_eq_replicate u) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.take u))) Ru E E E E (1 + u) (1 + u) (1 + u) 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlx] <;> omega) (t' := u) (by simp [hlx])
  have h10 := (wsym_runs 1 (by decide) sep (by decide)
    (mk7 (I x y) (tapeOf S5 (enc (x.take u))) Ru E E E E (1 + u) (1 + u) (1 + u) 0 0 0 0)
    (by
      simp only [mk7_c1, mk7_h1]
      rw [show 1 + u = 1 + (enc (x.take u)).length by simp [hlx], tapeOf_end]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (1 + u) (2 + u) (1 + u) 0 0 0 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply] <;> try omega
      rw [show 1 + u = (enc (x.take u)).length + 1 by simp [hlx]; omega,
        tapeOf_append_singleton]) rfl
  have h11 := (scanR_runs st 0 isBit (n - u)
    (mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E (1 + u) (2 + u) (1 + u) 0 0 0 0)
    (fun p hp => by simp only [mk7_c0, mk7_h0]; rw [show 1 + u + p = 1 + (u + p) by omega,
      I_x x y _ (by omega)]; simp)
    (by simp only [mk7_c0, mk7_h0]; rw [show 1 + u + (n - u) = 1 + x.length by omega, I_sep];
        rfl)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (1 + n) (2 + u) (1 + u) 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply] <;> omega) rfl
  have h12 := (mv_runs st 0 Move.right (mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (1 + n) (2 + u) (1 + u) 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (n + 2) (2 + u) (1 + u) 0 0 0 0) (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have h13 := (rew_runs 2 (mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (n + 2) (2 + u) (1 + u) 0 0 0 0) _ (nost_enc _) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (n + 2) (2 + u) 0 0 0 0 0) (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have h14 := (mv_runs st 2 Move.right (mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (n + 2) (2 + u) 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E
      (n + 2) (2 + u) 1 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h15 := (rcopy_runs 0 1 2 (by decide) (by decide) (by decide)
    (mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ [sep])) Ru E E E E (n + 2) (2 + u) 1 0 0 0 0)
    (enc (y.take u)) (enc (x.take u) ++ [sep]) (List.replicate u blank) []
    (by simp [hly]) (nost_enc _) (nost_rep _ _ (by decide))
    (fun m hm => by
      simp only [mk7_c0, mk7_h0]
      simp only [enc_length, hly] at hm
      rw [I_y x y m (by omega)]; simp [enc])
    (fun m hm => by simp only [mk7_c2, mk7_h2]; simp only [enc_length, hly] at hm; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, enc_length, hly, hRuE]; decide)
    (by simp only [mk7_c1, List.append_nil]; exact (tapeOf_append_blanks S5 _ u).symm)
    (by simp [hlx]; omega)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.take u) ++ sep :: enc (y.take u))) Ru E E E E
      (n + 2 + u) (2 * u + 2) (u + 1) 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hly] <;> omega) (t' := u) (by simp [hly])
  exact (seq_runs h1 <| seq_runs h2 <| seq_runs h3 <| seq_runs h4 <| seq_runs h5 <|
    seq_runs h6 <| seq_runs h7 <| seq_runs h8 <| seq_runs h9 <| seq_runs h10 <| seq_runs h11 <|
    seq_runs h12 <| seq_runs h13 <| seq_runs h14 h15).of_eq rfl
    (by simp only [mk7_h0, mk7_h1, mk7_h2, enc_length, hlx, hly]; omega)

/-! ## Segment 1: save `P₁`, then the packet `x_L # y_L` -/

def mid1 : Prog Sym5 7 :=
  seq (mv 1 Move.right) <| seq (mv 3 Move.right) <| seq (copy 1 3 isBit id) <|
  seq (mv 1 Move.left) <| seq (erase 1) <|
  seq (mv 0 Move.right) <| seq (mv 2 Move.right) <| seq (skipR 0 2) <|
  seq (mv 1 Move.right) <| seq (copy 0 1 isBit id) <| seq (wsym 1 sep) <| seq (mv 0 Move.right) <|
  seq (scanL 2 notSt) <| seq (mv 2 Move.right) <| seq (skipR 0 2) (copy 0 1 isBit id)

theorem isBit_id (z : Sym5) (hz : isBit z = true) : id z ≠ S5.st := by
  cases z <;> simp_all [isBit]

theorem enc_isBit (w : List Bool) : ∀ z ∈ enc w, isBit z = true := by
  intro z hz; simp only [enc, List.mem_map] at hz; obtain ⟨b, _, rfl⟩ := hz; simp

theorem encT_blank1 (w : List Bool) : tapeOf S5 (enc w) (1 + w.length) = blank := by
  rw [show 1 + w.length = 1 + (enc w).length by simp, tapeOf_end]

theorem mid1_runs (x y w1 : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length) :
    Runs st mid1
      (mk7 (I x y) (tapeOf S5 (enc w1)) (tapeOf S5 (enc (List.replicate ((x.length + 1) / 2) false)))
        E E E E 0 0 0 0 0 0 0)
      (2 * w1.length + 3 * ((x.length + 1) / 2) + 2 * (x.length / 2) + 10)
      (mk7 (I x y)
        (tapeOf S5 (enc (x.drop ((x.length + 1) / 2)) ++ sep :: enc (y.drop ((x.length + 1) / 2))))
        (tapeOf S5 (enc (List.replicate ((x.length + 1) / 2) false))) (tapeOf S5 (enc w1)) E E E
        (2 * x.length + 2) (2 * (x.length / 2) + 2) ((x.length + 1) / 2 + 1) (1 + w1.length)
        0 0 0) := by
  have hu : (x.length + 1) / 2 ≤ x.length := by omega
  have hhu : x.length / 2 + (x.length + 1) / 2 = x.length := by omega
  set n := x.length with hn
  set u := (n + 1) / 2 with hu_def
  set h := n / 2 with hh_def
  set Ru := tapeOf S5 (enc (List.replicate u false)) with hRu
  set W := tapeOf S5 (enc w1) with hW
  have hRuz : ∀ m < u, Ru (1 + m) = zero := by
    intro m hm; rw [hRu, tapeOf_get1 _ _ (by simpa using hm)]; simp [enc, bs]
  have hRuE : Ru (1 + u) = blank := by
    rw [hRu, show 1 + u = 1 + (enc (List.replicate u false)).length by simp, tapeOf_end]
  have hlx : (x.drop u).length = h := by simp; omega
  have hly : (y.drop u).length = h := by simp; omega
  have h1 := (mv_runs st 1 Move.right (mk7 (I x y) W Ru E E E E 0 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) W Ru E E E E 0 1 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h2 := (mv_runs st 3 Move.right (mk7 (I x y) W Ru E E E E 0 1 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) W Ru E E E E 0 1 0 1 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h3 := (copy_runs S5 (by decide) 1 3 (by decide) (by decide) isBit id isBit_id (enc w1) []
    (mk7 (I x y) W Ru E E E E 0 1 0 1 0 0 0)
    (fun p hp => by simp only [mk7_c1, mk7_h1, hW]; rw [tapeOf_get1 _ _ hp])
    (enc_isBit w1)
    (by simp only [mk7_c1, mk7_h1, hW, enc_length]; rw [encT_blank1]; rfl) rfl rfl).of_eq
    (T'' := mk7 (I x y) W Ru W E E E 0 (1 + w1.length) 0 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hW]) (t' := w1.length) (by simp)
  have h4 := (mv_runs st 1 Move.left (mk7 (I x y) W Ru W E E E 0 (1 + w1.length) 0 (1 + w1.length)
      0 0 0) (fun _ => by simp only [mk7_c1, mk7_h1, hW]; rw [encT_blank1]; decide)).of_eq
    (T'' := mk7 (I x y) W Ru W E E E 0 w1.length 0 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have h5 := (erase_runs 1 (by decide) (mk7 (I x y) W Ru W E E E 0 w1.length 0 (1 + w1.length)
      0 0 0) (enc w1) (nost_enc _) rfl (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W E E E 0 0 0 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, E]) (t' := w1.length) (by simp)
  have h6 := (mv_runs st 0 Move.right (mk7 (I x y) E Ru W E E E 0 0 0 (1 + w1.length) 0 0 0)
    (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W E E E 1 0 0 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have h7 := (mv_runs st 2 Move.right (mk7 (I x y) E Ru W E E E 1 0 0 (1 + w1.length) 0 0 0)
    (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W E E E 1 0 1 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have h8 := (skipR_runs 0 2 (by decide) (mk7 (I x y) E Ru W E E E 1 0 1 (1 + w1.length) 0 0 0) u
    (fun m hm => by simp only [mk7_c2, mk7_h2]; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, hRuE]; decide)).of_eq
    (T'' := mk7 (I x y) E Ru W E E E (1 + u) 0 (1 + u) (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp <;> omega) rfl
  have h9 := (mv_runs st 1 Move.right (mk7 (I x y) E Ru W E E E (1 + u) 0 (1 + u) (1 + w1.length)
      0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W E E E (1 + u) 1 (1 + u) (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have h10 := (copy_runs S5 (by decide) 0 1 (by decide) (by decide) isBit id isBit_id
    (enc (x.drop u)) [] (mk7 (I x y) E Ru W E E E (1 + u) 1 (1 + u) (1 + w1.length) 0 0 0)
    (fun p hp => by
      simp only [mk7_c0, mk7_h0]; simp only [enc_length, hlx] at hp
      rw [show 1 + u + p = 1 + (u + p) by omega, I_x x y _ (by omega)]; simp [enc])
    (enc_isBit _)
    (by simp only [mk7_c0, mk7_h0, enc_length, hlx]; rw [show 1 + u + h = 1 + x.length by omega,
        I_sep]; rfl) rfl rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.drop u))) Ru W E E E (1 + n) (1 + h) (1 + u)
      (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlx] <;> omega) (t' := h) (by simp [hlx])
  have h11 := (wsym_runs 1 (by decide) sep (by decide)
    (mk7 (I x y) (tapeOf S5 (enc (x.drop u))) Ru W E E E (1 + n) (1 + h) (1 + u) (1 + w1.length)
      0 0 0)
    (by simp only [mk7_c1, mk7_h1]; rw [← hlx, encT_blank1]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E (1 + n) (2 + h) (1 + u)
      (1 + w1.length) 0 0 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply] <;> try omega
      rw [show 1 + h = (enc (x.drop u)).length + 1 by simp [hlx]; omega,
        tapeOf_append_singleton]) rfl
  have h12 := (mv_runs st 0 Move.right (mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (1 + n) (2 + h) (1 + u) (1 + w1.length) 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (n + 2) (2 + h) (1 + u) (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have h13 := (rew_runs 2 (mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (n + 2) (2 + h) (1 + u) (1 + w1.length) 0 0 0) _ (nost_enc _) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (n + 2) (2 + h) 0 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have h14 := (mv_runs st 2 Move.right (mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (n + 2) (2 + h) 0 (1 + w1.length) 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (n + 2) (2 + h) 1 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have h15 := (skipR_runs 0 2 (by decide) (mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W
      E E E (n + 2) (2 + h) 1 (1 + w1.length) 0 0 0) u
    (fun m hm => by simp only [mk7_c2, mk7_h2]; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, hRuE]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (n + 2 + u) (2 + h) (1 + u) (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp <;> omega) rfl
  have h16 := (copy_runs S5 (by decide) 0 1 (by decide) (by decide) isBit id isBit_id
    (enc (y.drop u)) (enc (x.drop u) ++ [sep])
    (mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ [sep])) Ru W E E E
      (n + 2 + u) (2 + h) (1 + u) (1 + w1.length) 0 0 0)
    (fun p hp => by
      simp only [mk7_c0, mk7_h0]; simp only [enc_length, hly] at hp
      rw [show n + 2 + u + p = x.length + 2 + (u + p) by omega, I_y x y _ (by omega)]; simp [enc])
    (enc_isBit _)
    (by
      simp only [mk7_c0, mk7_h0, enc_length, hly]
      rw [show n + 2 + u + h = x.length + 2 + x.length by omega, I_end x y hy]; rfl)
    rfl (by simp [hlx]; omega)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (x.drop u) ++ sep :: enc (y.drop u))) Ru W E E E
      (2 * n + 2) (2 * h + 2) (u + 1) (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hly, hlx] <;> omega) (t' := h)
    (by simp [hly])
  exact (seq_runs h1 <| seq_runs h2 <| seq_runs h3 <| seq_runs h4 <| seq_runs h5 <|
    seq_runs h6 <| seq_runs h7 <| seq_runs h8 <| seq_runs h9 <| seq_runs h10 <| seq_runs h11 <|
    seq_runs h12 <| seq_runs h13 <| seq_runs h14 <| seq_runs h15 h16).of_eq rfl
    (by simp only [mk7_h2]; clear_value Ru W h u n; omega)

/-! ## Segment 2: save `P₂`, then the packet `(x_H + x_L) # (y_H + y_L)` -/

def mid2 : Prog Sym5 7 :=
  seq (mv 1 Move.right) <| seq (mv 4 Move.right) <| seq (copy 1 4 isBit id) <|
  seq (mv 1 Move.left) <| seq (erase 1) <|
  seq (mv 0 Move.right) <| seq (mv 2 Move.right) <| seq (skipR 0 2) <|
  seq (mv 5 Move.right) <| seq (copy 0 5 isBit id) <|
  seq (mv 1 Move.right) <| seq (wsym 1 zero) <|
  seq (scanL 0 notSt) <| seq (mv 0 Move.right) <| seq (scanL 2 notSt) <| seq (mv 2 Move.right) <|
  seq (rcopy 0 1 2) <| seq (mv 1 Move.left) <| seq (mv 5 Move.left) <| seq (arSweep 5 1 addG) <|
  seq (mv 1 Move.right) <| seq (scanR 1 isBit) <| seq (wsym 1 sep) <|
  seq (scanR 0 isBit) <| seq (mv 0 Move.right) <| seq (scanL 2 notSt) <| seq (mv 2 Move.right) <|
  seq (skipR 0 2) <| seq (mv 6 Move.right) <| seq (copy 0 6 isBit id) <| seq (wsym 1 zero) <|
  seq (scanL 0 notSt) <| seq (mv 0 Move.right) <| seq (scanR 0 isBit) <| seq (mv 0 Move.right) <|
  seq (scanL 2 notSt) <| seq (mv 2 Move.right) <| seq (rcopy 0 1 2) <|
  seq (mv 1 Move.left) <| seq (mv 6 Move.left) (arSweep 6 1 addG)

/-- `bin_{u+1}(val a + val b)`: the padded sum of a high part `b` and a low part `a`. -/
def psum (u : ℕ) (a b : List Bool) : List Bool := bin (u + 1) (val a + val (false :: b))

set_option maxHeartbeats 4000000 in
theorem mid2_runs (x y w1 w2 : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length) :
    Runs st mid2
      (mk7 (I x y) (tapeOf S5 (enc w2)) (tapeOf S5 (enc (List.replicate ((x.length + 1) / 2) false)))
        (tapeOf S5 (enc w1)) E E E 0 0 0 0 0 0 0)
      (2 * w2.length + 4 * x.length + 10 * ((x.length + 1) / 2) + 3 * (x.length / 2) + 32)
      (mk7 (I x y)
        (tapeOf S5 (enc (psum ((x.length + 1) / 2) (x.drop ((x.length + 1) / 2))
            (x.take ((x.length + 1) / 2))) ++
          sep :: enc (psum ((x.length + 1) / 2) (y.drop ((x.length + 1) / 2))
            (y.take ((x.length + 1) / 2)))))
        (tapeOf S5 (enc (List.replicate ((x.length + 1) / 2) false))) (tapeOf S5 (enc w1))
        (tapeOf S5 (enc w2)) (tapeOf S5 (enc (x.drop ((x.length + 1) / 2))))
        (tapeOf S5 (enc (y.drop ((x.length + 1) / 2))))
        (x.length + 2 + (x.length + 1) / 2) ((x.length + 1) / 2 + 2) ((x.length + 1) / 2 + 1) 0
        (1 + w2.length) 0 0) := by
  have hu : (x.length + 1) / 2 ≤ x.length := by omega
  have hhu : x.length / 2 + (x.length + 1) / 2 = x.length := by omega
  have hhle : x.length / 2 ≤ (x.length + 1) / 2 := by omega
  set n := x.length with hn
  set u := (n + 1) / 2 with hu_def
  set h := n / 2 with hh_def
  set Ru := tapeOf S5 (enc (List.replicate u false)) with hRu
  set W1 := tapeOf S5 (enc w1) with hW1
  set W2 := tapeOf S5 (enc w2) with hW2
  set Xl := tapeOf S5 (enc (x.drop u)) with hXl
  set Yl := tapeOf S5 (enc (y.drop u)) with hYl
  set Sx := psum u (x.drop u) (x.take u) with hSx
  set Ty := psum u (y.drop u) (y.take u) with hTy
  have hRuz : ∀ m < u, Ru (1 + m) = zero := by
    intro m hm; rw [hRu, tapeOf_get1 _ _ (by simpa using hm)]; simp [enc, bs]
  have hRuE : Ru (1 + u) = blank := by
    rw [hRu, show 1 + u = 1 + (enc (List.replicate u false)).length by simp, tapeOf_end]
  have hlx : (x.drop u).length = h := by simp; omega
  have hly : (y.drop u).length = h := by simp; omega
  have hlX : (x.take u).length = u := by simp; omega
  have hlY : (y.take u).length = u := by simp; omega
  have hlS : Sx.length = u + 1 := by simp [hSx, psum, bin]
  have hlT : Ty.length = u + 1 := by simp [hTy, psum, bin]
  have k1 := (mv_runs st 1 Move.right (mk7 (I x y) W2 Ru W1 E E E 0 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) W2 Ru W1 E E E 0 1 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have k2 := (mv_runs st 4 Move.right (mk7 (I x y) W2 Ru W1 E E E 0 1 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) W2 Ru W1 E E E 0 1 0 0 1 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have k3 := (copy_runs S5 (by decide) 1 4 (by decide) (by decide) isBit id isBit_id (enc w2) []
    (mk7 (I x y) W2 Ru W1 E E E 0 1 0 0 1 0 0)
    (fun p hp => by simp only [mk7_c1, mk7_h1, hW2]; rw [tapeOf_get1 _ _ hp])
    (enc_isBit w2)
    (by simp only [mk7_c1, mk7_h1, hW2, enc_length]; rw [encT_blank1]; rfl) rfl rfl).of_eq
    (T'' := mk7 (I x y) W2 Ru W1 W2 E E 0 (1 + w2.length) 0 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hW2]) (t' := w2.length) (by simp)
  have k4 := (mv_runs st 1 Move.left (mk7 (I x y) W2 Ru W1 W2 E E 0 (1 + w2.length) 0 0
      (1 + w2.length) 0 0) (fun _ => by simp only [mk7_c1, mk7_h1, hW2]; rw [encT_blank1]; decide)).of_eq
    (T'' := mk7 (I x y) W2 Ru W1 W2 E E 0 w2.length 0 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have k5 := (erase_runs 1 (by decide) (mk7 (I x y) W2 Ru W1 W2 E E 0 w2.length 0 0
      (1 + w2.length) 0 0) (enc w2) (nost_enc _) rfl (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W1 W2 E E 0 0 0 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, E]) (t' := w2.length) (by simp)
  have k6 := (mv_runs st 0 Move.right (mk7 (I x y) E Ru W1 W2 E E 0 0 0 0 (1 + w2.length) 0 0)
    (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W1 W2 E E 1 0 0 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k7 := (mv_runs st 2 Move.right (mk7 (I x y) E Ru W1 W2 E E 1 0 0 0 (1 + w2.length) 0 0)
    (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W1 W2 E E 1 0 1 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k8 := (skipR_runs 0 2 (by decide) (mk7 (I x y) E Ru W1 W2 E E 1 0 1 0 (1 + w2.length) 0 0) u
    (fun m hm => by simp only [mk7_c2, mk7_h2]; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, hRuE]; decide)).of_eq
    (T'' := mk7 (I x y) E Ru W1 W2 E E (1 + u) 0 (1 + u) 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp <;> omega) rfl
  have k9 := (mv_runs st 5 Move.right (mk7 (I x y) E Ru W1 W2 E E (1 + u) 0 (1 + u) 0
      (1 + w2.length) 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W1 W2 E E (1 + u) 0 (1 + u) 0 (1 + w2.length) 1 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k10 := (copy_runs S5 (by decide) 0 5 (by decide) (by decide) isBit id isBit_id
    (enc (x.drop u)) [] (mk7 (I x y) E Ru W1 W2 E E (1 + u) 0 (1 + u) 0 (1 + w2.length) 1 0)
    (fun p hp => by
      simp only [mk7_c0, mk7_h0]; simp only [enc_length, hlx] at hp
      rw [show 1 + u + p = 1 + (u + p) by omega, I_x x y _ (by omega)]; simp [enc])
    (enc_isBit _)
    (by simp only [mk7_c0, mk7_h0, enc_length, hlx]; rw [show 1 + u + h = 1 + x.length by omega,
        I_sep]; rfl) rfl rfl).of_eq
    (T'' := mk7 (I x y) E Ru W1 W2 Xl E (1 + n) 0 (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlx, hXl] <;> omega) (t' := h)
    (by simp [hlx])
  have k11 := (mv_runs st 1 Move.right (mk7 (I x y) E Ru W1 W2 Xl E (1 + n) 0 (1 + u) 0
      (1 + w2.length) (1 + h) 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E Ru W1 W2 Xl E (1 + n) 1 (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k12 := (wsym_runs 1 (by decide) zero (by decide)
    (mk7 (I x y) E Ru W1 W2 Xl E (1 + n) 1 (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (by simp [E, tapeOf])).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E (1 + n) 2 (1 + u) 0 (1 + w2.length)
      (1 + h) 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply]
      exact tapeOf_append_singleton S5 [] zero) rfl
  have k13 := (rew_runs 0 (mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E (1 + n) 2 (1 + u) 0
      (1 + w2.length) (1 + h) 0) _ (I_nost x y) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 0 2 (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have k14 := (mv_runs st 0 Move.right (mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 0 2 (1 + u) 0
      (1 + w2.length) (1 + h) 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 1 2 (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k15 := (rew_runs 2 (mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 1 2 (1 + u) 0
      (1 + w2.length) (1 + h) 0) _ (nost_enc _) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 1 2 0 0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have k16 := (mv_runs st 2 Move.right (mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 1 2 0 0
      (1 + w2.length) (1 + h) 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 1 2 1 0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k17 := (rcopy_runs 0 1 2 (by decide) (by decide) (by decide)
    (mk7 (I x y) (tapeOf S5 [zero]) Ru W1 W2 Xl E 1 2 1 0 (1 + w2.length) (1 + h) 0)
    (enc (x.take u)) [zero] (List.replicate u blank) []
    (by simp [hlX]) (nost_enc _) (nost_rep _ _ (by decide))
    (fun m hm => by
      simp only [mk7_c0, mk7_h0]
      simp only [enc_length, hlX] at hm
      rw [I_x x y m (by omega)]; simp [enc])
    (fun m hm => by simp only [mk7_c2, mk7_h2]; simp only [enc_length, hlX] at hm; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, enc_length, hlX, hRuE]; decide)
    (by simp only [mk7_c1, List.append_nil]; exact (tapeOf_append_blanks S5 _ u).symm) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (false :: x.take u))) Ru W1 W2 Xl E (1 + u) (2 + u) (1 + u)
      0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlX, enc, bs] <;> omega) (t' := u)
    (by simp [hlX])
  have k18 := (mv_runs st 1 Move.left (mk7 (I x y) (tapeOf S5 (enc (false :: x.take u))) Ru W1 W2
      Xl E (1 + u) (2 + u) (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (fun _ => by
      simp only [mk7_c1, mk7_h1]
      rw [show 2 + u = 1 + (false :: x.take u).length by simp [hlX]; omega, encT_blank1]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (false :: x.take u))) Ru W1 W2 Xl E (1 + u) (1 + u)
      (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have k19 := (mv_runs st 5 Move.left (mk7 (I x y) (tapeOf S5 (enc (false :: x.take u))) Ru W1 W2
      Xl E (1 + u) (1 + u) (1 + u) 0 (1 + w2.length) (1 + h) 0)
    (fun _ => by simp only [mk7_c5, mk7_h5, hXl]; rw [← hlx, encT_blank1]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc (false :: x.take u))) Ru W1 W2 Xl E (1 + u) (1 + u)
      (1 + u) 0 (1 + w2.length) h 0)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have k20 := (addSweep_runs 5 1 (by decide) (by decide)
    (mk7 (I x y) (tapeOf S5 (enc (false :: x.take u))) Ru W1 W2 Xl E (1 + u) (1 + u)
      (1 + u) 0 (1 + w2.length) h 0) [] [] (false :: x.take u) (x.drop u) []
    (by simp) (by simp) (by simp) (by simp) (by simp [hlX]; omega) (by simp; rfl)
    (by simp [hXl]) (by simp [hlx]) (by simp [hlx, hlX]; omega)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx)) Ru W1 W2 Xl E (1 + u) 0 (1 + u) 0 (1 + w2.length) 0 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply, hlx, hlX] <;> try omega
      simp [hSx, psum, hlX]) (t' := u + 1) (by simp [hlX])
  have k21 := (mv_runs st 1 Move.right (mk7 (I x y) (tapeOf S5 (enc Sx)) Ru W1 W2 Xl E (1 + u) 0
      (1 + u) 0 (1 + w2.length) 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx)) Ru W1 W2 Xl E (1 + u) 1 (1 + u) 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k22 := (scanR_runs st 1 isBit (u + 1) (mk7 (I x y) (tapeOf S5 (enc Sx)) Ru W1 W2 Xl E
      (1 + u) 1 (1 + u) 0 (1 + w2.length) 0 0)
    (fun p hp => by
      simp only [mk7_c1, mk7_h1]; rw [tapeOf_get1 _ _ (by simp [hlS]; omega)]; simp [enc])
    (by simp only [mk7_c1, mk7_h1]; rw [← hlS, encT_blank1]; rfl)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx)) Ru W1 W2 Xl E (1 + u) (u + 2) (1 + u) 0
      (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply] <;> omega) rfl
  have k23 := (wsym_runs 1 (by decide) sep (by decide) (mk7 (I x y) (tapeOf S5 (enc Sx)) Ru W1 W2
      Xl E (1 + u) (u + 2) (1 + u) 0 (1 + w2.length) 0 0)
    (by simp only [mk7_c1, mk7_h1]; rw [show u + 2 = 1 + Sx.length by omega, encT_blank1];
        decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (1 + u) (u + 3) (1 + u) 0
      (1 + w2.length) 0 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply] <;> try omega
      rw [show u + 2 = (enc Sx).length + 1 by simp [hlS], tapeOf_append_singleton]) rfl
  have k24 := (scanR_runs st 0 isBit h (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E
      (1 + u) (u + 3) (1 + u) 0 (1 + w2.length) 0 0)
    (fun p hp => by simp only [mk7_c0, mk7_h0]; rw [show 1 + u + p = 1 + (u + p) by omega,
      I_x x y _ (by omega)]; simp)
    (by simp only [mk7_c0, mk7_h0]; rw [show 1 + u + h = 1 + x.length by omega, I_sep]; rfl)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (1 + n) (u + 3) (1 + u) 0
      (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply] <;> omega) rfl
  have k25 := (mv_runs st 0 Move.right (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E
      (1 + n) (u + 3) (1 + u) 0 (1 + w2.length) 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (n + 2) (u + 3) (1 + u) 0
      (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have k26 := (rew_runs 2 (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E
      (n + 2) (u + 3) (1 + u) 0 (1 + w2.length) 0 0) _ (nost_enc _) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (n + 2) (u + 3) 0 0
      (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have k27 := (mv_runs st 2 Move.right (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E
      (n + 2) (u + 3) 0 0 (1 + w2.length) 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (n + 2) (u + 3) 1 0
      (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k28 := (skipR_runs 0 2 (by decide) (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E
      (n + 2) (u + 3) 1 0 (1 + w2.length) 0 0) u
    (fun m hm => by simp only [mk7_c2, mk7_h2]; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, hRuE]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (n + 2 + u) (u + 3) (1 + u) 0
      (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp <;> omega) rfl
  have k29 := (mv_runs st 6 Move.right (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E
      (n + 2 + u) (u + 3) (1 + u) 0 (1 + w2.length) 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (n + 2 + u) (u + 3) (1 + u) 0
      (1 + w2.length) 0 1)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k30 := (copy_runs S5 (by decide) 0 6 (by decide) (by decide) isBit id isBit_id
    (enc (y.drop u)) [] (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl E (n + 2 + u) (u + 3)
      (1 + u) 0 (1 + w2.length) 0 1)
    (fun p hp => by
      simp only [mk7_c0, mk7_h0]; simp only [enc_length, hly] at hp
      rw [show n + 2 + u + p = x.length + 2 + (u + p) by omega, I_y x y _ (by omega)]; simp [enc])
    (enc_isBit _)
    (by
      simp only [mk7_c0, mk7_h0, enc_length, hly]
      rw [show n + 2 + u + h = x.length + 2 + x.length by omega, I_end x y hy]; rfl)
    rfl rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep])) Ru W1 W2 Xl Yl (2 * n + 2) (u + 3) (1 + u) 0
      (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [Function.update_apply, hly, hYl] <;> omega) (t' := h)
    (by simp [hly])
  have k31 := (wsym_runs 1 (by decide) zero (by decide) (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep]))
      Ru W1 W2 Xl Yl (2 * n + 2) (u + 3) (1 + u) 0 (1 + w2.length) 0 (1 + h))
    (by
      simp only [mk7_c1, mk7_h1]
      rw [show u + 3 = 1 + (enc Sx ++ [sep]).length by simp [hlS]; omega, tapeOf_end]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl (2 * n + 2) (u + 4)
      (1 + u) 0 (1 + w2.length) 0 (1 + h))
    (by
      apply mk7_ext <;> simp [Function.update_apply] <;> try omega
      rw [show u + 3 = (enc Sx ++ [sep]).length + 1 by simp [hlS] <;> omega,
        tapeOf_append_singleton]; simp) rfl
  have k32 := (rew_runs 0 (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl
      (2 * n + 2) (u + 4) (1 + u) 0 (1 + w2.length) 0 (1 + h)) _ (I_nost x y) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl 0 (u + 4) (1 + u) 0
      (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have k33 := (mv_runs st 0 Move.right (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl
      Yl 0 (u + 4) (1 + u) 0 (1 + w2.length) 0 (1 + h)) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl 1 (u + 4) (1 + u) 0
      (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k34 := (scanR_runs st 0 isBit n (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl
      Yl 1 (u + 4) (1 + u) 0 (1 + w2.length) 0 (1 + h))
    (fun p hp => by simp only [mk7_c0, mk7_h0]; rw [I_x x y _ (by omega)]; simp)
    (by simp only [mk7_c0, mk7_h0]; rw [I_sep]; rfl)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl (1 + n) (u + 4) (1 + u)
      0 (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have k35 := (mv_runs st 0 Move.right (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl
      Yl (1 + n) (u + 4) (1 + u) 0 (1 + w2.length) 0 (1 + h)) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl (n + 2) (u + 4) (1 + u)
      0 (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have k36 := (rew_runs 2 (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl
      (n + 2) (u + 4) (1 + u) 0 (1 + w2.length) 0 (1 + h)) _ (nost_enc _) rfl).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl (n + 2) (u + 4) 0 0
      (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have k37 := (mv_runs st 2 Move.right (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl
      Yl (n + 2) (u + 4) 0 0 (1 + w2.length) 0 (1 + h)) (by simp)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl (n + 2) (u + 4) 1 0
      (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have k38 := (rcopy_runs 0 1 2 (by decide) (by decide) (by decide)
    (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep, zero])) Ru W1 W2 Xl Yl (n + 2) (u + 4) 1 0
      (1 + w2.length) 0 (1 + h))
    (enc (y.take u)) (enc Sx ++ [sep, zero]) (List.replicate u blank) []
    (by simp [hlY]) (nost_enc _) (nost_rep _ _ (by decide))
    (fun m hm => by
      simp only [mk7_c0, mk7_h0]
      simp only [enc_length, hlY] at hm
      rw [I_y x y m (by omega)]; simp [enc])
    (fun m hm => by simp only [mk7_c2, mk7_h2]; simp only [enc_length, hlY] at hm; exact hRuz m hm)
    (by simp only [mk7_c2, mk7_h2, enc_length, hlY, hRuE]; decide)
    (by simp only [mk7_c1, List.append_nil]; exact (tapeOf_append_blanks S5 _ u).symm)
    (by simp [hlS] <;> omega)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep] ++ enc (false :: y.take u))) Ru W1 W2 Xl Yl
      (n + 2 + u) (2 * u + 4) (1 + u) 0 (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [Function.update_apply, hlY, enc, bs] <;> omega) (t' := u)
    (by simp [hlY])
  have k39 := (mv_runs st 1 Move.left (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep] ++
      enc (false :: y.take u))) Ru W1 W2 Xl Yl (n + 2 + u) (2 * u + 4) (1 + u) 0 (1 + w2.length) 0
      (1 + h))
    (fun _ => by
      simp only [mk7_c1, mk7_h1]
      rw [show 2 * u + 4 = 1 + (enc Sx ++ [sep] ++ enc (false :: y.take u)).length by
        simp [hlS, hlY]; omega, tapeOf_end]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep] ++ enc (false :: y.take u))) Ru W1 W2 Xl Yl
      (n + 2 + u) (2 * u + 3) (1 + u) 0 (1 + w2.length) 0 (1 + h))
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have k40 := (mv_runs st 6 Move.left (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep] ++
      enc (false :: y.take u))) Ru W1 W2 Xl Yl (n + 2 + u) (2 * u + 3) (1 + u) 0 (1 + w2.length) 0
      (1 + h))
    (fun _ => by simp only [mk7_c6, mk7_h6, hYl]; rw [← hly, encT_blank1]; decide)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep] ++ enc (false :: y.take u))) Ru W1 W2 Xl Yl
      (n + 2 + u) (2 * u + 3) (1 + u) 0 (1 + w2.length) 0 h)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have k41 := (addSweep_runs 6 1 (by decide) (by decide)
    (mk7 (I x y) (tapeOf S5 (enc Sx ++ [sep] ++ enc (false :: y.take u))) Ru W1 W2 Xl Yl
      (n + 2 + u) (2 * u + 3) (1 + u) 0 (1 + w2.length) 0 h) (enc Sx ++ [sep]) []
    (false :: y.take u) (y.drop u) []
    (by
      intro z hz; simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact enc_ne_st _ z hz
      · decide)
    (by simp) (by simp) (by simp) (by simp [hlY, hlS]; omega)
    (by
      simp only [mk7_c1]
      rw [show (enc Sx ++ [sep]).length = (enc Sx).length + 1 by simp, tapeOf_succ, getD_three,
        if_neg (by omega), if_pos (by simp)]
      simp only [Nat.sub_self, List.getD_cons_zero]; rfl)
    (by simp [hYl]) (by simp [hly]) (by simp [hly, hlY]; omega)).of_eq
    (T'' := mk7 (I x y) (tapeOf S5 (enc Sx ++ sep :: enc Ty)) Ru W1 W2 Xl Yl
      (n + 2 + u) (u + 2) (u + 1) 0 (1 + w2.length) 0 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply, hly, hlY, hlS] <;> try omega
      simp [hTy, psum, hlY]) (t' := u + 1) (by simp [hlY])
  have hall := (seq_runs k1 <| seq_runs k2 <| seq_runs k3 <| seq_runs k4 <| seq_runs k5 <|
    seq_runs k6 <| seq_runs k7 <| seq_runs k8 <| seq_runs k9 <| seq_runs k10 <| seq_runs k11 <|
    seq_runs k12 <| seq_runs k13 <| seq_runs k14 <| seq_runs k15 <| seq_runs k16 <|
    seq_runs k17 <| seq_runs k18 <| seq_runs k19 <| seq_runs k20 <| seq_runs k21 <|
    seq_runs k22 <| seq_runs k23 <| seq_runs k24 <| seq_runs k25 <| seq_runs k26 <|
    seq_runs k27 <| seq_runs k28 <| seq_runs k29 <| seq_runs k30 <| seq_runs k31 <|
    seq_runs k32 <| seq_runs k33 <| seq_runs k34 <| seq_runs k35 <| seq_runs k36 <|
    seq_runs k37 <| seq_runs k38 <| seq_runs k39 <| seq_runs k40 k41)
  clear k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 k24 k25 k26 k27 k28 k29 k30 k31 k32 k33 k34 k35 k36 k37 k38 k39 k40 k41
  refine hall.of_eq rfl ?_
  simp only [mk7_h0, mk7_h2]; ring

end IntMul.Mach.Kara

-- ===== Kara0 =====

/-!
# Karatsuba, segment 0: size test, schoolbook base case, or the first packet
-/

namespace IntMul.Mach.Kara

open IntMul IntMul.Mach IntMul.Mach.School School.Sym5

set_option linter.unusedSectionVars false

def isSep : (Fin 7 → Sym5) → Bool := fun a => decide (a 0 = sep)

/-- The base case: rewind the input, run the schoolbook program on tapes `0–3`, and step tape `5`
off `▷` to signal that the body should halt. -/
def small : Prog Sym5 7 :=
  seq (scanL 0 notSt) (seq (liftProg (by norm_num : 4 ≤ 7) School.prog) (mv 5 Move.right))

def seg0 : Prog Sym5 7 :=
  seq (mv 0 Move.right) <| seq (mv 0 Move.right) <| ite isSep small <|
  seq (mv 0 Move.right) <| ite isSep small <|
  seq (mv 0 Move.right) <| ite isSep small (seq (scanL 0 notSt) large0)

theorem small_runs (x y : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length) (p : ℕ) :
    ∃ t ≤ p + 10 * x.length ^ 2 + 18 * x.length + 13, ∃ T' : Tapes Sym5 7,
      Runs st small (mk7 (I x y) E E E E E E p 0 0 0 0 0 0) t T' ∧
      T'.cells 1 = tapeOf S5 ((bin (2 * x.length) (val x * val y)).map (bitSym S5)) ∧
      T'.read 5 = blank := by
  obtain ⟨t, ht, T', hr, hout⟩ := School.prog_runs (by norm_num) x y hy hn
  rw [initTapes_eq] at hr
  have h1 := (rew_runs 0 (mk7 (I x y) E E E E E E p 0 0 0 0 0 0) _ (I_nost x y) rfl).of_eq
    (T'' := mk7 (I x y) E E E E E E 0 0 0 0 0 0 0) (by apply mk7_ext <;> simp [Function.update_apply])
    rfl
  have h2 := liftProg_runs st (by norm_num : 4 ≤ 7) School.prog hr
    (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  set U : Tapes Sym5 7 := ⟨fun i => if h : i.val < 4 then T'.cells ⟨i.val, h⟩
      else (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0).cells i,
    fun i => if h : i.val < 4 then T'.head ⟨i.val, h⟩
      else (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0).head i⟩ with hU
  have h3 := mv_runs st 5 Move.right U (by simp)
  refine ⟨p + (t + 1), by omega, _, seq_runs h1 (seq_runs h2 h3), ?_, ?_⟩
  · simp only [hU, Function.update_apply]
    simp [hout]
  · simp [Tapes.read, hU, moveHead, E, tapeOf]

theorem I_bit (x y : List Bool) (p : ℕ) (hp : p < x.length) : isSep (fun i => if i = 0 then
    I x y (1 + p) else E 0) = false := by
  simp [isSep, I_x x y p hp, bs]; split <;> decide

theorem seg0_large (x y : List Bool) (hy : y.length = x.length) (hn : 4 ≤ x.length) :
    Runs st seg0 (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0)
      (3 * x.length + 3 * ((x.length + 1) / 2) + 19)
      (mk7 (I x y)
        (tapeOf S5 (enc (x.take ((x.length + 1) / 2)) ++ sep :: enc (y.take ((x.length + 1) / 2))))
        (tapeOf S5 (enc (List.replicate ((x.length + 1) / 2) false))) E E E E
        (x.length + 2 + (x.length + 1) / 2) (2 * ((x.length + 1) / 2) + 2)
        ((x.length + 1) / 2 + 1) 0 0 0 0) := by
  have hb : ∀ q, q < x.length → isSep (mk7 (I x y) E E E E E E (1 + q) 0 0 0 0 0 0).read = false := by
    intro q hq
    simp [isSep, Tapes.read, I_x x y q hq, bs]; split <;> decide
  have h1 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E 1 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h2 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E 1 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E (1 + 1) 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h3 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E (1 + 1) 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E (1 + 2) 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h4 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E (1 + 2) 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E (1 + 3) 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h5 := (rew_runs 0 (mk7 (I x y) E E E E E E (1 + 3) 0 0 0 0 0 0) _ (I_nost x y) rfl).of_eq
    (T'' := mk7 (I x y) E E E E E E 0 0 0 0 0 0 0) (by apply mk7_ext <;> simp [Function.update_apply])
    rfl
  have h6 := large0_runs x y hy (by omega)
  have i3 := ite_runs_false (c := isSep) (P₁ := small) (hb 3 (by omega)) (seq_runs h5 h6)
  have i2 := ite_runs_false (c := isSep) (P₁ := small) (hb 2 (by omega)) (seq_runs h4 i3)
  have i1 := ite_runs_false (c := isSep) (P₁ := small) (hb 1 (by omega)) (seq_runs h3 i2)
  exact (seq_runs h1 (seq_runs h2 i1)).of_eq rfl (by simp only [mk7_h0]; omega)

theorem seg0_small (x y : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length)
    (h3 : x.length ≤ 3) :
    ∃ t ≤ 10 * x.length ^ 2 + 18 * x.length + 22, ∃ T' : Tapes Sym5 7,
      Runs st seg0 (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0) t T' ∧
      T'.cells 1 = tapeOf S5 ((bin (2 * x.length) (val x * val y)).map (bitSym S5)) ∧
      T'.read 5 = blank := by
  have hb : ∀ q, q < x.length → isSep (mk7 (I x y) E E E E E E (1 + q) 0 0 0 0 0 0).read = false := by
    intro q hq
    simp [isSep, Tapes.read, I_x x y q hq, bs]; split <;> decide
  have hs : isSep (mk7 (I x y) E E E E E E (1 + x.length) 0 0 0 0 0 0).read = true := by
    simp [isSep, Tapes.read, I_sep]
  have h1 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E 1 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h2 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E 1 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E (1 + 1) 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h3' := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E (1 + 1) 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E (1 + 2) 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  have h4 := (mv_runs st 0 Move.right (mk7 (I x y) E E E E E E (1 + 2) 0 0 0 0 0 0) (by simp)).of_eq
    (T'' := mk7 (I x y) E E E E E E (1 + 3) 0 0 0 0 0 0) (by apply mk7_ext <;> simp [moveHead]) rfl
  obtain ⟨t, ht, T', hr, hout, hrd⟩ := small_runs x y hy hn (1 + x.length)
  have hb1 := hb 1
  have hb2 := hb 2
  interval_cases hx : x.length
  · exact ⟨_, by omega, T', seq_runs h1 (seq_runs h2 (ite_runs_true hs hr)), hout, hrd⟩
  · exact ⟨_, by omega, T', seq_runs h1 (seq_runs h2 (ite_runs_false (hb1 (by omega))
      (seq_runs h3' (ite_runs_true hs hr)))), hout, hrd⟩
  · exact ⟨_, by omega, T', seq_runs h1 (seq_runs h2 (ite_runs_false (hb1 (by omega))
      (seq_runs h3' (ite_runs_false (hb2 (by omega)) (seq_runs h4 (ite_runs_true hs hr)))))),
      hout, hrd⟩

end IntMul.Mach.Kara

-- ===== Kara3 =====

/-!
# Karatsuba, segment 3: recombination

With `P₃` on the output tape, `P₁` on tape 3 and `P₂` on tape 4: `M := P₃ - P₁ - P₂` on the
output tape, then tape 3 becomes `P₁ ++ P₂` and `M` is added `h = |y_L|` places from its right
end; the result is copied to the cleared output tape.
-/

namespace IntMul.Mach.Kara

open IntMul IntMul.Mach IntMul.Mach.School School.Sym5

set_option linter.unusedSectionVars false

def fin3 : Prog Sym5 7 :=
  seq (toEnd 1) <| seq (toEnd 3) <| seq (arSweep 3 1 subG) <|
  seq (toEnd 1) <| seq (toEnd 4) <| seq (arSweep 4 1 subG) <|
  seq (mv 3 Move.right) <| seq (scanR 3 isBit) <| seq (mv 4 Move.right) <|
  seq (copy 4 3 isBit id) <| seq (mv 3 Move.left) <| seq (toEnd 6) <| seq (skipL 3 6) <|
  seq (toEnd 1) <| seq (arSweep 1 3 addG) <| seq (toEnd 1) <| seq (erase 1) <|
  seq (mv 3 Move.right) <| seq (mv 1 Move.right) (copy 3 1 isBit id)

theorem val_bin (L v : ℕ) (h : v < 2 ^ L) : val (bin L v) = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · have := testBit_val (bin L v) (L - 1 - i) (by simp [bin]; omega)
    simp only [bin, List.length_ofFn, List.getElem_ofFn] at this
    rw [show L - 1 - (L - 1 - i) = i by omega] at this
    simpa [bin] using this
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (val_lt _) (by
      simp only [bin, List.length_ofFn]; exact Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem bin_length (L v : ℕ) : (bin L v).length = L := by simp [bin]

/-- The middle coefficient `P₃ - P₁ - P₂`. -/
def midW (w1 w2 w3 : List Bool) : List Bool :=
  bin w3.length (val (bin w3.length (val w3 - val w1)) - val w2)

/-- The recombined product. -/
def combW (w1 w2 w3 : List Bool) (h : ℕ) : List Bool :=
  bin ((w1 ++ w2).take (w1.length + w2.length - h)).length
    (val (midW w1 w2 w3) + val ((w1 ++ w2).take (w1.length + w2.length - h))) ++
    (w1 ++ w2).drop (w1.length + w2.length - h)

theorem nost_append {a b : List Sym5} (ha : ∀ z ∈ a, z ≠ st) (hb : ∀ z ∈ b, z ≠ st) :
    ∀ z ∈ a ++ b, z ≠ st := by
  intro z hz; simp only [List.mem_append] at hz; rcases hz with hz | hz
  · exact ha z hz
  · exact hb z hz

set_option maxHeartbeats 4000000 in
theorem fin3_runs (c0 c2 c5 : ℕ → Sym5) (w1 w2 w3 yl : List Bool)
    (h13 : w1.length ≤ w3.length) (h23 : w2.length ≤ w3.length)
    (hv : val w1 + val w2 ≤ val w3) (hyl : yl.length ≤ w1.length + w2.length)
    (hD : w3.length ≤ w1.length + w2.length - yl.length) :
    Runs st fin3
      (mk7 c0 (tapeOf S5 (enc w3)) c2 (tapeOf S5 (enc w1)) (tapeOf S5 (enc w2)) c5
        (tapeOf S5 (enc yl)) 0 0 0 0 0 0 0)
      (7 * w3.length + 4 * w1.length + 4 * w2.length + yl.length + 19)
      (mk7 c0 (tapeOf S5 (enc (combW w1 w2 w3 yl.length))) c2
        (tapeOf S5 (enc (combW w1 w2 w3 yl.length))) (tapeOf S5 (enc w2)) c5 (tapeOf S5 (enc yl))
        0 (1 + (w1.length + w2.length)) 0 (1 + (w1.length + w2.length)) (1 + w2.length) 0 0) := by
  set W1 := tapeOf S5 (enc w1) with hW1
  set W2 := tapeOf S5 (enc w2) with hW2
  set W3 := tapeOf S5 (enc w3) with hW3
  set Yl := tapeOf S5 (enc yl) with hYl
  set M1 := bin w3.length (val w3 - val w1) with hM1
  set M := midW w1 w2 w3 with hM
  set L := w1.length + w2.length - yl.length with hL
  set Dl := (w1 ++ w2).take L with hDl
  set Rl := (w1 ++ w2).drop L with hRl
  set Z := combW w1 w2 w3 yl.length with hZ
  have hlM1 : M1.length = w3.length := bin_length _ _
  have hlM : M.length = w3.length := bin_length _ _
  have hlD : Dl.length = L := by simp [hDl]; omega
  have hlZ : Z.length = w1.length + w2.length := by
    simp only [hZ, combW, List.length_append, bin_length]; simp <;> omega
  have hvM1 : val M1 = val w3 - val w1 := val_bin _ _ (by have := val_lt w3; omega)
  have q1 := (toEnd_runs 1 (mk7 c0 W3 c2 W1 W2 c5 Yl 0 0 0 0 0 0 0) w3 [] (by simp) rfl
    (by simp [hW3]) rfl).of_eq
    (T'' := mk7 c0 W3 c2 W1 W2 c5 Yl 0 w3.length 0 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have q2 := (toEnd_runs 3 (mk7 c0 W3 c2 W1 W2 c5 Yl 0 w3.length 0 0 0 0 0) w1 [] (by simp) rfl
    (by simp [hW1]) rfl).of_eq
    (T'' := mk7 c0 W3 c2 W1 W2 c5 Yl 0 w3.length 0 w1.length 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have q3 := (subSweep_runs 3 1 (by decide) (by decide)
    (mk7 c0 W3 c2 W1 W2 c5 Yl 0 w3.length 0 w1.length 0 0 0) [] [] w3 w1 [] (by simp) (by simp)
    (by simp) (by simp [hW3]) (by simp) (by simp; rfl) (by simp [hW1]) (by simp) h13
    (by omega)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M1)) c2 W1 W2 c5 Yl 0 0 0 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hM1] <;> omega) rfl
  have q4 := (toEnd_runs 1 (mk7 c0 (tapeOf S5 (enc M1)) c2 W1 W2 c5 Yl 0 0 0 0 0 0 0) M1 []
    (by simp) rfl (by simp) rfl).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M1)) c2 W1 W2 c5 Yl 0 w3.length 0 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlM1]) (by rw [hlM1])
  have q5 := (toEnd_runs 4 (mk7 c0 (tapeOf S5 (enc M1)) c2 W1 W2 c5 Yl 0 w3.length 0 0 0 0 0) w2
    [] (by simp) rfl (by simp [hW2]) rfl).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M1)) c2 W1 W2 c5 Yl 0 w3.length 0 0 w2.length 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have eM : bin w3.length (val M1 - val w2) = M := by rw [hM, midW, ← hM1]
  have q6 := (subSweep_runs 4 1 (by decide) (by decide)
    (mk7 c0 (tapeOf S5 (enc M1)) c2 W1 W2 c5 Yl 0 w3.length 0 0 w2.length 0 0) [] [] M1 w2 []
    (by simp) (by simp) (by simp) (by simp) (by simp [hlM1]) (by simp; rfl) (by simp [hW2])
    (by simp) (by rw [hlM1]; exact h23) (by rw [hvM1]; omega)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl 0 0 0 0 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, eM, hlM1, Nat.sub_eq_zero_of_le h23])
    (t' := w3.length) hlM1
  have q7 := (mv_runs st 3 Move.right (mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl 0 0 0 0 0 0 0)
    (by simp)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl 0 0 0 1 0 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have q8 := (scanR_runs st 3 isBit w1.length (mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl
      0 0 0 1 0 0 0)
    (fun p hp => by
      simp only [mk7_c3, mk7_h3, hW1]; rw [tapeOf_get1 _ _ (by simpa using hp)]; simp [enc])
    (by simp only [mk7_c3, mk7_h3, hW1]; rw [encT_blank1]; rfl)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl 0 0 0 (1 + w1.length) 0 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have q9 := (mv_runs st 4 Move.right (mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl
      0 0 0 (1 + w1.length) 0 0 0) (by simp)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl 0 0 0 (1 + w1.length) 1 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have q10 := (copy_runs S5 (by decide) 4 3 (by decide) (by decide) isBit id isBit_id (enc w2)
    (enc w1) (mk7 c0 (tapeOf S5 (enc M)) c2 W1 W2 c5 Yl 0 0 0 (1 + w1.length) 1 0 0)
    (fun p hp => by simp only [mk7_c4, mk7_h4, hW2]; rw [tapeOf_get1 _ _ hp])
    (enc_isBit w2)
    (by simp only [mk7_c4, mk7_h4, hW2, enc_length]; rw [encT_blank1]; rfl) rfl
    (by simp; omega)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 0 0 (1 + (w1.length + w2.length)) (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, enc] <;> omega) (t' := w2.length)
    (by simp)
  have q11 := (mv_runs st 3 Move.left (mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2)))
      W2 c5 Yl 0 0 0 (1 + (w1.length + w2.length)) (1 + w2.length) 0 0)
    (fun _ => by
      simp only [mk7_c3, mk7_h3]
      rw [show w1.length + w2.length = (w1 ++ w2).length by simp, encT_blank1]; decide)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 0 0 (w1.length + w2.length) (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead] <;> omega) rfl
  have q12 := (toEnd_runs 6 (mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 0 0 (w1.length + w2.length) (1 + w2.length) 0 0) yl [] (by simp) rfl
    (by simp [hYl]) rfl).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 0 0 (w1.length + w2.length) (1 + w2.length) 0 yl.length)
    (by apply mk7_ext <;> simp [Function.update_apply]) rfl
  have q13 := (skipL_runs 3 6 (by decide) (by decide) (mk7 c0 (tapeOf S5 (enc M)) c2
      (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl 0 0 0 (w1.length + w2.length) (1 + w2.length) 0
      yl.length) (enc (w1 ++ w2)) (enc yl) (nost_enc _) (nost_enc _) rfl (by simp [hYl])
      (by simp) (by simp; omega)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 0 0 L (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp <;> omega) (t' := yl.length) (by simp)
  have q14 := (toEnd_runs 1 (mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 0 0 L (1 + w2.length) 0 0) M [] (by simp) rfl (by simp) rfl).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 w3.length 0 L (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlM]) (by rw [hlM])
  have hsplit : enc (w1 ++ w2) = [] ++ enc Dl ++ enc Rl := by
    simp only [List.nil_append, enc, ← List.map_append, hDl, hRl, List.take_append_drop]
  have q15 := (addSweep_runs 1 3 (by decide) (by decide)
    (mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc (w1 ++ w2))) W2 c5 Yl
      0 w3.length 0 L (1 + w2.length) 0 0) [] (enc Rl) Dl M []
    (by simp) (nost_enc _) (by simp) (by simp only [mk7_c3]; rw [hsplit]) (by simp [hlD])
    (by simp; rfl) (by simp) (by simp [hlM]) (by rw [hlM, hlD]; exact hD)).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc Z)) W2 c5 Yl
      0 0 0 0 (1 + w2.length) 0 0)
    (by
      apply mk7_ext <;> simp [Function.update_apply, hlM, hlD] <;> try omega
      simp [hZ, combW, enc, hDl, hRl, hL, hM]) (t' := L) hlD
  have q16 := (toEnd_runs 1 (mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc Z)) W2 c5 Yl
      0 0 0 0 (1 + w2.length) 0 0) M [] (by simp) rfl (by simp) rfl).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc Z)) W2 c5 Yl
      0 w3.length 0 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlM]) (by rw [hlM])
  have q17 := (erase_runs 1 (by decide) (mk7 c0 (tapeOf S5 (enc M)) c2 (tapeOf S5 (enc Z)) W2 c5 Yl
      0 w3.length 0 0 (1 + w2.length) 0 0) (enc M) (nost_enc _) rfl (by simp [hlM])).of_eq
    (T'' := mk7 c0 E c2 (tapeOf S5 (enc Z)) W2 c5 Yl 0 0 0 0 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, E]) (t' := w3.length) (by simp [hlM])
  have q18 := (mv_runs st 3 Move.right (mk7 c0 E c2 (tapeOf S5 (enc Z)) W2 c5 Yl
      0 0 0 0 (1 + w2.length) 0 0) (by simp)).of_eq
    (T'' := mk7 c0 E c2 (tapeOf S5 (enc Z)) W2 c5 Yl 0 0 0 1 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have q19 := (mv_runs st 1 Move.right (mk7 c0 E c2 (tapeOf S5 (enc Z)) W2 c5 Yl
      0 0 0 1 (1 + w2.length) 0 0) (by simp)).of_eq
    (T'' := mk7 c0 E c2 (tapeOf S5 (enc Z)) W2 c5 Yl 0 1 0 1 (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [moveHead]) rfl
  have q20 := (copy_runs S5 (by decide) 3 1 (by decide) (by decide) isBit id isBit_id (enc Z) []
    (mk7 c0 E c2 (tapeOf S5 (enc Z)) W2 c5 Yl 0 1 0 1 (1 + w2.length) 0 0)
    (fun p hp => by simp only [mk7_c3, mk7_h3]; rw [tapeOf_get1 _ _ hp])
    (enc_isBit Z)
    (by simp only [mk7_c3, mk7_h3, enc_length]; rw [encT_blank1]; rfl) rfl rfl).of_eq
    (T'' := mk7 c0 (tapeOf S5 (enc Z)) c2 (tapeOf S5 (enc Z)) W2 c5 Yl
      0 (1 + (w1.length + w2.length)) 0 (1 + (w1.length + w2.length)) (1 + w2.length) 0 0)
    (by apply mk7_ext <;> simp [Function.update_apply, hlZ]) (t' := Z.length) (by simp)
  have hall := (seq_runs q1 <| seq_runs q2 <| seq_runs q3 <| seq_runs q4 <| seq_runs q5 <|
    seq_runs q6 <| seq_runs q7 <| seq_runs q8 <| seq_runs q9 <| seq_runs q10 <| seq_runs q11 <|
    seq_runs q12 <| seq_runs q13 <| seq_runs q14 <| seq_runs q15 <| seq_runs q16 <|
    seq_runs q17 <| seq_runs q18 <| seq_runs q19 q20)
  clear q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20
  refine hall.of_eq rfl ?_
  clear hall
  clear_value W1 W2 W3 Yl M1 M Dl Rl Z L
  rw [hlZ, hL]
  clear * - hyl
  omega

end IntMul.Mach.Kara

-- ===== KaraMath =====

/-!
# Karatsuba arithmetic: the recombined product is correct
-/

namespace IntMul.Mach.Kara

open IntMul IntMul.Mach

theorem val_append' (a b : List Bool) : val (a ++ b) = val a * 2 ^ b.length + val b := by
  induction a with
  | nil => simp [val]
  | cons c a ih =>
    simp only [List.cons_append, val_cons, List.length_append, ih, pow_add]; ring

theorem val_split (l : List Bool) (k : ℕ) :
    val l = val (l.take k) * 2 ^ (l.drop k).length + val (l.drop k) := by
  conv_lhs => rw [← List.take_append_drop k l]
  exact val_append' _ _

theorem val_false_cons (b : List Bool) : val (false :: b) = val b := by
  simp [val_cons]

theorem val_psum (u : ℕ) (a b : List Bool) (h : val a + val b < 2 ^ (u + 1)) :
    val (psum u a b) = val a + val b := by
  unfold psum; rw [val_false_cons]; exact val_bin _ _ h

theorem comb_gen (x y : List Bool) (u h : ℕ) (hlen : x.length = u + h)
    (hy : y.length = x.length) (huh : h ≤ u) :
    val (bin (2 * u) (val (x.take u) * val (y.take u))) +
      val (bin (2 * h) (val (x.drop u) * val (y.drop u))) ≤
    val (bin (2 * (u + 1))
      (val (psum u (x.drop u) (x.take u)) * val (psum u (y.drop u) (y.take u)))) ∧
    combW (bin (2 * u) (val (x.take u) * val (y.take u)))
      (bin (2 * h) (val (x.drop u) * val (y.drop u)))
      (bin (2 * (u + 1))
        (val (psum u (x.drop u) (x.take u)) * val (psum u (y.drop u) (y.take u)))) h =
    bin (2 * (u + h)) (val x * val y) := by
  have hxs := val_split x u
  have hys := val_split y u
  have hxd : (x.drop u).length = h := by simp; omega
  have hyd : (y.drop u).length = h := by simp; omega
  have hxt : (x.take u).length = u := by simp; omega
  have hyt : (y.take u).length = u := by simp; omega
  have ha := val_lt (x.take u)
  have hb := val_lt (x.drop u)
  have hc := val_lt (y.take u)
  have hd := val_lt (y.drop u)
  rw [hxd] at hxs hb; rw [hyd] at hys hd; rw [hxt] at ha; rw [hyt] at hc
  have hx := val_lt x
  have hyl := val_lt y
  rw [hlen] at hx; rw [hy, hlen] at hyl
  have hhu : (2:ℕ) ^ h ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) huh
  have hpu : (2:ℕ) ^ (u + 1) = 2 * 2 ^ u := by rw [pow_succ]; ring
  rw [val_psum u _ _ (by omega), val_psum u _ _ (by omega)]
  generalize val (x.take u) = a at *
  generalize val (x.drop u) = b at *
  generalize val (y.take u) = c at *
  generalize val (y.drop u) = d at *
  have h1 : a * c < 2 ^ (2 * u) := by rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' ha hc
  have h2 : b * d < 2 ^ (2 * h) := by rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' hb hd
  have h3 : (b + a) * (d + c) < 2 ^ (2 * (u + 1)) := by
    rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' (by omega) (by omega)
  have hP3 : (b + a) * (d + c) = a * c + b * d + (a * d + b * c) := by ring
  have hxy : val x * val y = a * c * 2 ^ h * 2 ^ h + (a * d + b * c) * 2 ^ h + b * d := by
    rw [hxs, hys]; ring
  have hxyl : val x * val y < 2 ^ (2 * (u + h)) := by
    rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' hx hyl
  rw [val_bin _ _ h1, val_bin _ _ h2, val_bin _ _ h3]
  refine ⟨by rw [hP3]; omega, ?_⟩
  unfold combW midW
  simp only [bin_length, val_bin _ _ h1, val_bin _ _ h2, val_bin _ _ h3]
  generalize hY : bin (2 * u) (a * c) ++ bin (2 * h) (b * d) = Y
  have hYv : val Y = a * c * 2 ^ h * 2 ^ h + b * d := by
    rw [← hY, val_append', val_bin _ _ h1, val_bin _ _ h2, bin_length, two_mul, pow_add]; ring
  have hYl : Y.length = 2 * u + 2 * h := by rw [← hY]; simp [bin_length]
  have hYs := val_split Y (2 * u + 2 * h - h)
  have hDl : (Y.drop (2 * u + 2 * h - h)).length = h := by simp; omega
  have hTl : (Y.take (2 * u + 2 * h - h)).length = 2 * u + h := by simp; omega
  have hD := val_lt (Y.drop (2 * u + 2 * h - h))
  rw [hDl] at hYs hD
  rw [hTl]
  generalize Y.take (2 * u + 2 * h - h) = T at *
  generalize Y.drop (2 * u + 2 * h - h) = D at *
  rw [hP3] at h3 ⊢
  generalize a * c = P1 at *
  generalize b * d = P2 at *
  generalize a * d + b * c = M at *
  rw [show P1 + P2 + M - P1 = P2 + M by omega, val_bin (2 * (u + 1)) (P2 + M) (by omega),
    show P2 + M - P2 = M by omega, val_bin (2 * (u + 1)) M (by omega)]
  generalize val x * val y = V at *
  have hV : V = (M + val T) * 2 ^ h + val D := by
    have := hYs.symm.trans hYv; rw [hxy, add_mul]; linarith
  have hMT : M + val T < 2 ^ (2 * u + h) := by
    have : (M + val T) * 2 ^ h < 2 ^ (2 * u + h) * 2 ^ h := by
      rw [← pow_add, show 2 * u + h + h = 2 * (u + h) by ring]; omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hlen' : (bin (2 * u + h) (M + val T) ++ D).length = 2 * (u + h) := by
    simp only [List.length_append, bin_length, hDl]; ring
  refine (bin_of_val _ _ ?_).trans (by rw [hlen'])
  rw [hlen', Nat.mod_eq_of_lt hxyl, val_append', val_bin _ _ hMT, hDl, hV]

theorem kara_le (x y : List Bool) (hy : y.length = x.length) (hn : 4 ≤ x.length) :
    val (bin (2 * ((x.length + 1) / 2)) (val (x.take ((x.length + 1) / 2)) * val (y.take ((x.length + 1) / 2)))) +
      val (bin (2 * (x.length / 2)) (val (x.drop ((x.length + 1) / 2)) * val (y.drop ((x.length + 1) / 2)))) ≤
    val (bin (2 * ((x.length + 1) / 2 + 1))
      (val (psum ((x.length + 1) / 2) (x.drop ((x.length + 1) / 2)) (x.take ((x.length + 1) / 2))) *
       val (psum ((x.length + 1) / 2) (y.drop ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2))))) :=
  (comb_gen x y ((x.length + 1) / 2) (x.length / 2) (by omega) hy (by omega)).1

theorem kara_comb (x y : List Bool) (hy : y.length = x.length) (hn : 4 ≤ x.length) :
    combW (bin (2 * ((x.length + 1) / 2)) (val (x.take ((x.length + 1) / 2)) * val (y.take ((x.length + 1) / 2))))
      (bin (2 * (x.length / 2)) (val (x.drop ((x.length + 1) / 2)) * val (y.drop ((x.length + 1) / 2))))
      (bin (2 * ((x.length + 1) / 2 + 1))
        (val (psum ((x.length + 1) / 2) (x.drop ((x.length + 1) / 2)) (x.take ((x.length + 1) / 2))) *
         val (psum ((x.length + 1) / 2) (y.drop ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2)))))
      (x.length / 2) =
    bin (2 * x.length) (val x * val y) := by
  rw [(comb_gen x y ((x.length + 1) / 2) (x.length / 2) (by omega) hy (by omega)).2]
  congr 1; omega

end IntMul.Mach.Kara

-- ===== KaraEval =====

/-!
# The Karatsuba body and its recursive evaluation certificate
-/

namespace IntMul.Mach.Kara

open IntMul IntMul.Mach IntMul.Mach.School School.Sym5
open IntMul.FlatRecursiveEvaluation IntMul.FlatRecursiveCall IntMul.TrackedBankedSimulation
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankCleanup (span)
open IntMul.FlatRecursiveReturn (returnedHeads)
open IntMul.FlatRecursiveScheduler (machine)

set_option linter.unusedSectionVars false

/-! ## The machine -/

def segs : Fin 4 → Prog Sym5 7 := ![seg0, mid1, mid2, fin3]

def kstop : Fin 4 → (Fin 7 → Sym5) → Bool := fun i a => decide (i = 0 ∧ a 5 ≠ st)

theorem hk7 : 2 ≤ 7 := by norm_num

/-- The Karatsuba body machine. -/
def KM : MultitapeTM := body S5 hk7 segs kstop

def kreq : KM.K → Option (Fin 3) := bodyRequest segs
def kres : Fin 3 → KM.K := bodyResume segs

abbrev kcfg (q : KM.K) (T : Tapes Sym5 7) : KM.Cfg := bcfg S5 hk7 segs kstop q T

/-! ## Generic facts about the platform model -/

theorem step_head_le (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

theorem nextExtent_le (M : MultitapeTM) (c : M.Cfg) (E : Fin M.k → ℕ) (j : Fin M.k) :
    nextExtent M c E j ≤ max (E j) (c.head j) := by
  unfold nextExtent
  by_cases h : c.state = M.qHalt
  · simp [h]
  · simp [h]

theorem extFrom_le (M : MultitapeTM) (t : ℕ) :
    ∀ (c : M.Cfg) (E : Fin M.k → ℕ) (j : Fin M.k), extFrom M c E t j ≤ max (E j) (c.head j + t) := by
  induction t with
  | zero => intro c E j; simp [extFrom]
  | succ t ih =>
    intro c E j
    rw [extFrom_succ]
    refine (ih _ _ j).trans ?_
    have h1 := step_head_le M c j
    have h2 := nextExtent_le M c E j
    omega

theorem span_le (M : MultitapeTM) (f : Fin M.k → ℕ) (B : ℕ) (h : ∀ j, f j ≤ B) : span M f ≤ B :=
  Finset.sup_le (fun j _ => h j)

theorem callCost_le (M : MultitapeTM) (n : ℕ) (E : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (B : ℕ) (hE : ∀ j, E j ≤ B) (hh : c.head M.outTape ≤ B) (hv : v.length ≤ B)
    (hw : (inputWord M x y).length ≤ B) : callCost M n E c v x y ≤ 7 * B + n + 18 := by
  have hs : span M (TrackedBankReservation.distance M E (parentAfterInput M c).head) ≤ B + 1 :=
    span_le _ _ _ (fun j => by
      simp only [TrackedBankReservation.distance]; have := hE j; omega)
  simp only [callCost]
  have : max (c.head M.outTape) (v.length + 1) ≤ B + 1 := by omega
  have : max (inputWord M x y).length v.length ≤ B := by omega
  omega

theorem resumeCost_le (M : MultitapeTM) (n : ℕ) (E : Fin M.k → ℕ) (w : List Bool)
    (B : ℕ) (hE : ∀ j, E j ≤ B) (hw : w.length ≤ B) : resumeCost M n E w ≤ 4 * B + n + 13 := by
  have hs : span M (fun j => E j + 1) ≤ B + 1 := span_le _ _ _ (fun j => by have := hE j; omega)
  simp only [resumeCost]
  have : max w.length (E M.outTape) ≤ B := by have := hE M.outTape; omega
  omega

theorem returnCost_le (M : MultitapeTM) (E : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (B : ℕ) (hE : ∀ j, E j ≤ B) (hh : ∀ j, c.head j ≤ B) (hv : v.length ≤ B) (hw : w.length ≤ B) :
    returnCost M E c v w ≤ 7 * B + 13 := by
  have hs : span M E ≤ B := span_le _ _ _ hE
  have hr : span M (returnedHeads M c) ≤ B := span_le _ _ _ (fun j => by
    simp only [returnedHeads]; split <;> [omega; exact hh j])
  simp only [returnCost]
  have : max (c.head M.outTape) (v.length + 1) ≤ B + 1 := by have := hh M.outTape; omega
  have : max w.length v.length ≤ B := by omega
  omega

theorem halts_head_le {Γ : Type} [DecidableEq Γ] {k : ℕ} {st' : Γ} {P : Prog Γ k} {q : P.Q}
    {T T' : Tapes Γ k} {t : ℕ} (h : Halts st' P q T t T') : ∀ j, T'.head j ≤ T.head j + t := by
  induction h with
  | done _ => intro j; omega
  | step _ _ ih =>
    intro j
    have := ih j
    simp only [Tapes.write, moveHead] at this
    split at this <;> omega

/-! ## The model's view of our tapes -/

theorem KM_tapeOf (w : List Sym5) : KM.tapeOf w = tapeOf S5 w := by
  funext p; cases p <;> rfl

theorem KM_bitSym : KM.bitSym = bs := by
  funext b; cases b <;> rfl

theorem KM_initCfg (x y : List Bool) :
    KM.initCfg x y = kcfg (some (Sum.inl ⟨0, (segs 0).q0⟩)) (mk7 (I x y) E E E E E E 0 0 0 0 0 0 0) := by
  simp only [MultitapeTM.initCfg, kcfg, bcfg]
  congr 1
  · funext i
    fin_cases i <;> simp [KM_tapeOf, KM_bitSym, I, E, enc, mk7] <;> rfl
  · funext i; fin_cases i <;> rfl

theorem KM_inputWord (x y : List Bool) : inputWord KM x y = enc x ++ sep :: enc y := by
  simp only [inputWord, KM_bitSym, enc]; rfl

theorem KM_parentAfterChild (j : Fin 3) (q : KM.K) (T : Tapes Sym5 7) (w : List Bool) :
    parentAfterChild KM 3 kres j (kcfg q T) w =
      kcfg (kres j) ⟨fun i => if i = 1 then tapeOf S5 (enc w) else T.cells i, fun _ => 0⟩ := by
  simp only [parentAfterChild, kcfg, bcfg, KM_tapeOf, KM_bitSym, enc]
  rfl

theorem KM_inputWord_length (x y : List Bool) :
    (inputWord KM x y).length = x.length + y.length + 1 := by
  simp [inputWord]; omega

theorem KM_out (w : List Bool) : KM.tapeOf (w.map KM.bitSym) = tapeOf S5 (enc w) := by
  erw [KM_tapeOf, KM_bitSym]; rfl

/-! ## Certificate building blocks -/

/-- An evaluation certificate whose budget is at most `X`. -/
def EvB (E : Fin KM.k → ℕ) (c : KM.Cfg) (v w : List Bool) (X : ℕ) : Prop :=
  ∃ Bd ≤ X, Evaluates KM 3 kreq kres E c v w Bd

theorem seg_eval (i : Fin 4) {T T' : Tapes Sym5 7} {t : ℕ} (hr : Runs st (segs i) T t T')
    (hT : ∀ j, T.head j = 0) (v w : List Bool) (B X : ℕ) (ht : t + 1 ≤ B)
    (hcont : ∀ E' : Fin KM.k → ℕ, (∀ j, E' j ≤ B) →
      EvB E' (kcfg (segExit segs kstop i T'.read) T') v w X)
    (E : Fin KM.k → ℕ) (hE : ∀ j, E j ≤ B) :
    EvB E (kcfg (some (Sum.inl ⟨i, (segs i).q0⟩)) T) v w (X + (t + 1)) := by
  obtain ⟨Bd, hBd, hev⟩ := hcont (extFrom KM (kcfg (some (Sum.inl ⟨i, (segs i).q0⟩)) T) E (t + 1))
    (fun j => by
      have h1 := extFrom_le KM (t + 1) (kcfg (some (Sum.inl ⟨i, (segs i).q0⟩)) T) E j
      have h0 : (kcfg (some (Sum.inl ⟨i, (segs i).q0⟩)) T).head j = 0 := hT j
      have := hE j
      omega)
  exact ⟨Bd + (t + 1), by omega,
    evaluates_of_halts S5 hk7 segs kstop (labels := 3) rfl i hr kreq (fun _ _ => rfl) kres E v w Bd hev⟩

theorem call_eval (label : Fin 3) (T T'' : Tapes Sym5 7) (a b cw v w : List Bool) (B Xc X : ℕ)
    (hpk : T.cells 1 = tapeOf S5 (enc a ++ sep :: enc b))
    (hh : ∀ j, T.head j ≤ B) (hv : v.length ≤ B) (hab : a.length + b.length + 1 ≤ B)
    (hcw : cw.length ≤ B)
    (child : EvB (initialExtent KM a b) (KM.initCfg a b) [] cw Xc)
    (hc'' : ∀ i, T''.cells i = if i = 1 then tapeOf S5 (enc cw) else T.cells i)
    (hh'' : ∀ i, T''.head i = 0)
    (hcont : ∀ E' : Fin KM.k → ℕ, (∀ j, E' j ≤ B) → EvB E' (kcfg (kres label) T'') cw w X)
    (E : Fin KM.k → ℕ) (hE : ∀ j, E j ≤ B) :
    EvB E (kcfg (some (Sum.inr label)) T) v w (11 * B + Xc + X + 37) := by
  have eT : T'' = ⟨fun i => if i = 1 then tapeOf S5 (enc cw) else T.cells i, fun _ => 0⟩ := by
    cases T''; simp only [Tapes.mk.injEq]; exact ⟨funext hc'', funext hh''⟩
  subst eT
  obtain ⟨Bc, hBc, hc⟩ := child
  obtain ⟨Bp, hBp, hp⟩ := hcont (parentAfterChildExtent KM E cw) (fun j => by
    simp only [parentAfterChildExtent]; split
    · exact hcw
    · exact hE j)
  rw [← KM_parentAfterChild] at hp
  have hw : (inputWord KM a b).length ≤ B := by
    rw [KM_inputWord_length]; omega
  have h1 := callCost_le KM 3 E (kcfg (some (Sum.inr label)) T) v a b B hE (hh 1) hv hw
  have h2 := resumeCost_le KM 3 E cw B hE hcw
  refine ⟨_, ?_, Evaluates.call E (kcfg (some (Sum.inr label)) T) v a b cw w label Bc Bp
    (by simp [kcfg, bcfg, KM, body]) rfl ?_ hc hp⟩
  · omega
  · rw [KM_inputWord, KM_tapeOf]; exact hpk

theorem halt_eval (T : Tapes Sym5 7) (v w : List Bool) (B : ℕ)
    (hout : T.cells 1 = tapeOf S5 (enc w)) (hh : ∀ j, T.head j ≤ B) (hv : v.length ≤ B)
    (hw : w.length ≤ B) (E : Fin KM.k → ℕ) (hE : ∀ j, E j ≤ B) :
    EvB E (kcfg none T) v w (7 * B + 13) :=
  ⟨_, returnCost_le KM E (kcfg none T) v w B hE hh hv hw,
    Evaluates.halt E (kcfg none T) v w rfl (hout.trans (KM_out w).symm)⟩

theorem segExit_run (i : Fin 4) (hi : i.val < 3) (a : Fin 7 → Sym5) (ha : a 5 = st) :
    segExit segs kstop i a = some (Sum.inr ⟨i.val, hi⟩) := by
  simp [segExit, hi, kstop, ha]

theorem segExit_three (a : Fin 7 → Sym5) : segExit segs kstop 3 a = none := by
  simp [segExit]

theorem segExit_small (a : Fin 7 → Sym5) (ha : a 5 = blank) : segExit segs kstop 0 a = none := by
  simp [segExit, kstop, ha]

end IntMul.Mach.Kara

-- ===== KaraCert =====

/-!
# The recursive evaluation certificate for the Karatsuba body
-/

namespace IntMul.Mach.Kara

open IntMul IntMul.Mach IntMul.Mach.School School.Sym5
open IntMul.FlatRecursiveEvaluation IntMul.FlatRecursiveCall IntMul.TrackedBankedSimulation
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.FlatRecursiveScheduler (machine)

set_option linter.unusedSectionVars false

theorem mk7_head0 (c0 c1 c2 c3 c4 c5 c6 : ℕ → Sym5) :
    ∀ j, (mk7 c0 c1 c2 c3 c4 c5 c6 0 0 0 0 0 0 0).head j = 0 := by
  intro j; fin_cases j <;> rfl

theorem init_ext_le (x y : List Bool) (B : ℕ) (h : x.length + y.length + 1 ≤ B) :
    ∀ j, initialExtent KM x y j ≤ B := by
  intro j; simp only [initialExtent]; split
  · have := KM_inputWord_length x y; omega
  · omega

theorem small_eval (x y : List Bool) (hy : y.length = x.length) (hn : 1 ≤ x.length)
    (h3 : x.length ≤ 3) :
    EvB (initialExtent KM x y) (KM.initCfg x y) [] (bin (2 * x.length) (val x * val y)) 3000 := by
  obtain ⟨t, ht, T', hr, hout, hrd⟩ := seg0_small x y hy hn h3
  have hsq : x.length ^ 2 ≤ 9 := by
    have := Nat.pow_le_pow_left h3 2; simpa using this
  rw [KM_initCfg]
  obtain ⟨Bd, hBd, hev⟩ := seg_eval 0 hr (mk7_head0 _ _ _ _ _ _ _) []
    (bin (2 * x.length) (val x * val y)) 260 (7 * 260 + 13) (by omega)
    (fun E' hE' => by
      rw [segExit_small _ hrd]
      exact halt_eval T' [] _ 260 hout
        (fun j => by have := halts_head_le hr j; rw [mk7_head0] at this; omega) (by simp)
        (by rw [bin_length]; omega) E' hE')
    _ (init_ext_le x y 260 (by omega))
  exact ⟨Bd, by omega, hev⟩

/-- The large case, given certificates for the three children. -/
theorem large_eval (x y : List Bool) (hy : y.length = x.length) (hn : 4 ≤ x.length) (X1 X2 X3 : ℕ)
    (c1 : EvB (initialExtent KM (x.take ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2)))
      (KM.initCfg (x.take ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2))) []
      (bin (2 * ((x.length + 1) / 2)) (val (x.take ((x.length + 1) / 2)) * val (y.take ((x.length + 1) / 2))))
      X1)
    (c2 : EvB (initialExtent KM (x.drop ((x.length + 1) / 2)) (y.drop ((x.length + 1) / 2)))
      (KM.initCfg (x.drop ((x.length + 1) / 2)) (y.drop ((x.length + 1) / 2))) []
      (bin (2 * (x.length / 2)) (val (x.drop ((x.length + 1) / 2)) * val (y.drop ((x.length + 1) / 2))))
      X2)
    (c3 : EvB (initialExtent KM (psum ((x.length + 1) / 2) (x.drop ((x.length + 1) / 2)) (x.take ((x.length + 1) / 2)))
        (psum ((x.length + 1) / 2) (y.drop ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2))))
      (KM.initCfg (psum ((x.length + 1) / 2) (x.drop ((x.length + 1) / 2)) (x.take ((x.length + 1) / 2)))
        (psum ((x.length + 1) / 2) (y.drop ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2)))) []
      (bin (2 * ((x.length + 1) / 2 + 1))
        (val (psum ((x.length + 1) / 2) (x.drop ((x.length + 1) / 2)) (x.take ((x.length + 1) / 2))) *
         val (psum ((x.length + 1) / 2) (y.drop ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2)))))
      X3) :
    EvB (initialExtent KM x y) (KM.initCfg x y) [] (bin (2 * x.length) (val x * val y))
      (X1 + X2 + X3 + 900 * x.length + 9000) := by
  have hle := kara_le x y hy hn
  have hcomb := kara_comb x y hy hn
  have hlx : (x.take ((x.length + 1) / 2)).length = (x.length + 1) / 2 := by simp; omega
  have hly : (y.take ((x.length + 1) / 2)).length = (x.length + 1) / 2 := by simp; omega
  have hdx : (x.drop ((x.length + 1) / 2)).length = x.length / 2 := by simp; omega
  have hyl : (y.drop ((x.length + 1) / 2)).length = x.length / 2 := by simp; omega
  generalize hpX : psum ((x.length + 1) / 2) (x.drop ((x.length + 1) / 2)) (x.take ((x.length + 1) / 2)) = pX
    at c3 hle hcomb
  generalize hpY : psum ((x.length + 1) / 2) (y.drop ((x.length + 1) / 2)) (y.take ((x.length + 1) / 2)) = pY
    at c3 hle hcomb
  have hpXl : pX.length = (x.length + 1) / 2 + 1 := by rw [← hpX, psum, bin_length]
  have hpYl : pY.length = (x.length + 1) / 2 + 1 := by rw [← hpY, psum, bin_length]
  generalize hw1 : bin (2 * ((x.length + 1) / 2)) (val (x.take ((x.length + 1) / 2)) *
    val (y.take ((x.length + 1) / 2))) = w1 at c1 hle hcomb
  generalize hw2 : bin (2 * (x.length / 2)) (val (x.drop ((x.length + 1) / 2)) *
    val (y.drop ((x.length + 1) / 2))) = w2 at c2 hle hcomb
  generalize hw3 : bin (2 * ((x.length + 1) / 2 + 1)) (val pX * val pY) = w3 at c3 hle hcomb
  have l1 : w1.length = 2 * ((x.length + 1) / 2) := by rw [← hw1, bin_length]
  have l2 : w2.length = 2 * (x.length / 2) := by rw [← hw2, bin_length]
  have l3 : w3.length = 2 * ((x.length + 1) / 2 + 1) := by rw [← hw3, bin_length]
  have lW : (bin (2 * x.length) (val x * val y)).length = 2 * x.length := bin_length _ _
  generalize hB : 20 * x.length + 200 = B
  -- segment 3 and the final halt
  have H3 := fun E' hE' => seg_eval 3
    (fin3_runs (I x y) (tapeOf S5 (enc (List.replicate ((x.length + 1) / 2) false)))
      (tapeOf S5 (enc (x.drop ((x.length + 1) / 2)))) w1 w2 w3 (y.drop ((x.length + 1) / 2))
      (by omega) (by omega) hle (by omega) (by omega))
    (mk7_head0 _ _ _ _ _ _ _) w3 (bin (2 * x.length) (val x * val y)) B (7 * B + 13) (by omega)
    (fun E'' hE'' => by
      rw [segExit_three]
      refine halt_eval _ w3 _ B ?_ ?_ (by omega) (by omega) E'' hE''
      · simp only [mk7_c1]; rw [hyl, hcomb]
      · intro j; fin_cases j <;> simp <;> omega)
    E' hE'
  -- segment 2 and the third call
  have H2 := fun E' hE' => seg_eval 2 (mid2_runs x y w1 w2 hy (by omega)) (mk7_head0 _ _ _ _ _ _ _)
    w2 (bin (2 * x.length) (val x * val y)) B _ (by omega)
    (fun E'' hE'' => by
      rw [segExit_run 2 (by decide) _ rfl]
      refine call_eval 2 _ _ pX pY w3 w2 _ B X3 _ (by rw [hpX, hpY]; rfl) ?_ (by omega) (by omega)
        (by omega) c3 (fun i => by fin_cases i <;> rfl) (mk7_head0 _ _ _ _ _ _ _) H3 E'' hE''
      intro j; fin_cases j <;> simp <;> omega)
    E' hE'
  -- segment 1 and the second call
  have H1 := fun E' hE' => seg_eval 1 (mid1_runs x y w1 hy (by omega)) (mk7_head0 _ _ _ _ _ _ _)
    w1 (bin (2 * x.length) (val x * val y)) B _ (by omega)
    (fun E'' hE'' => by
      rw [segExit_run 1 (by decide) _ rfl]
      refine call_eval 1 _ _ _ _ w2 w1 _ B X2 _ rfl ?_ (by omega) (by omega)
        (by omega) c2 (fun i => by fin_cases i <;> rfl) (mk7_head0 _ _ _ _ _ _ _) H2 E'' hE''
      intro j; fin_cases j <;> simp <;> omega)
    E' hE'
  -- segment 0 and the first call
  have H0 := seg_eval 0 (seg0_large x y hy hn) (mk7_head0 _ _ _ _ _ _ _)
    [] (bin (2 * x.length) (val x * val y)) B _ (by omega)
    (fun E'' hE'' => by
      rw [segExit_run 0 (by decide) _ rfl]
      refine call_eval 0 _ _ _ _ w1 [] _ B X1 _ rfl ?_ (by simp) (by omega)
        (by omega) c1 (fun i => by fin_cases i <;> rfl) (mk7_head0 _ _ _ _ _ _ _) H1 E'' hE''
      intro j; fin_cases j <;> simp <;> omega)
    (initialExtent KM x y) (init_ext_le x y B (by omega))
  rw [KM_initCfg]
  obtain ⟨Bd, hBd, hev⟩ := H0
  exact ⟨Bd, by omega, hev⟩

theorem kara_eval : ∀ n : ℕ, ∀ x y : List Bool, x.length = n → y.length = n → 1 ≤ n →
    EvB (initialExtent KM x y) (KM.initCfg x y) [] (bin (2 * n) (val x * val y)) (kb 900 9000 3000 n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hx hy hn
    subst hx
    by_cases h3 : x.length ≤ 3
    · rw [kb_small _ _ _ _ h3]
      exact small_eval x y hy hn h3
    · have h4 : 4 ≤ x.length := by omega
      rw [kb, if_neg h3, show x.length - x.length / 2 = (x.length + 1) / 2 by omega]
      have e := large_eval x y hy h4 _ _ _
        (ih ((x.length + 1) / 2) (by omega) _ _ (by simp; omega) (by simp; omega) (by omega))
        (ih (x.length / 2) (by omega) _ _ (by simp; omega) (by simp; omega) (by omega))
        (ih ((x.length + 1) / 2 + 1) (by omega) _ _ (by rw [psum, bin_length]) (by rw [psum, bin_length])
          (by omega))
      obtain ⟨Bd, hBd, hev⟩ := e
      exact ⟨Bd, by omega, hev⟩

theorem one_le_logb : (1 : ℝ) ≤ Real.logb 2 3 := by
  rw [← Real.logb_self_eq_one (b := 2) (by norm_num)]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)

/-- **Karatsuba**: integer multiplication in time `O(n^{log₂ 3})` on the platform model. -/
theorem karatsuba : MulTimeBound fun n => (n : ℝ) ^ Real.logb 2 3 := by
  obtain ⟨C, hC, hCb⟩ := kb_bound 900 9000 3000
  have key : ∀ n, 1 ≤ n → ∀ x y : List Bool, x.length = n → y.length = n →
      ∃ t : ℕ, t ≤ kb 900 9000 3000 n + 18 * n + 23 ∧
        (machine KM 3 kreq kres).HaltsWithOutput x y t (bin (2 * n) (val x * val y)) := by
    intro n hn x y hx hy
    obtain ⟨Bd, hBd, hev⟩ := kara_eval n x y hx hy hn
    obtain ⟨t, ht, -, hh⟩ := native_evaluates_correct KM 3 kreq kres x y _ Bd hev
    refine ⟨t, ?_, hh⟩
    rw [KM_inputWord_length, bin_length] at ht
    omega
  refine ⟨machine KM 3 kreq kres, fun n hn => ⟨(kb 900 9000 3000 n + 18 * n + 23 : ℕ), ?_⟩,
    C + 41, by positivity, 1, fun n _ hn => ?_⟩
  · intro x y hx hy
    obtain ⟨t, ht, hh⟩ := key n hn x y hx hy
    exact ⟨t, by exact_mod_cast ht, hh⟩
  · intro x y hx hy
    obtain ⟨t, ht, hh⟩ := key n hn x y hx hy
    refine ⟨t, ?_, hh⟩
    have hkb := hCb n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ Real.logb 2 3 := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ Real.logb 2 3 := Real.rpow_le_rpow_of_exponent_le hn1 one_le_logb
    have ht' : (t : ℝ) ≤ (kb 900 9000 3000 n : ℝ) + 18 * n + 23 := by exact_mod_cast ht
    nlinarith

end IntMul.Mach.Kara


theorem solution : IntMul.MulTimeBound fun n => (n : ℝ) ^ Real.logb 2 3 := IntMul.Mach.Kara.karatsuba
