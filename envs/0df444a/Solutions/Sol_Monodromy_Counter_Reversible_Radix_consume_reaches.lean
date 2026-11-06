-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Radix.consume_reaches
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:12:54.264803+00:00
-- url     : https://prove2.me/submissions/d5320d2a-78b9-47cd-be40-cfd21a3664ab

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Radix
variable (p : ℕ) [NeZero p]

private theorem compatible_not_both_local {n : ℕ} {first second : Action n}
    (compatible : Action.Compatible first second) (values : Fin n → ℤ) :
    ¬ (first.enabled values ∧ second.enabled values) := by
  cases first <;> cases second <;> simp only [Action.Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  rename_i firstZero secondZero
  cases firstZero <;> cases secondZero <;> simp_all [Action.enabled]

private theorem enabled_index_unique_local {n q e : ℕ} (table : Table n q e)
    (deterministic : Deterministic table) {first second : Fin e} {state : State n q}
    (first_enabled : (table first).enabled state)
    (second_enabled : (table second).enabled state) : first = second := by
  by_contra different
  have compatible := deterministic first second different
    (first_enabled.1.trans second_enabled.1.symm)
  exact (compatible_not_both_local compatible state.2) ⟨first_enabled.2, second_enabled.2⟩

private theorem stepRel_deterministic_local {n q e : ℕ} (table : Table n q e)
    (deterministic : Deterministic table) {initial first second : State n q}
    (left : StepRel table initial first) (right : StepRel table initial second) :
    first = second := by
  obtain ⟨left_index, left_enabled, rfl⟩ := left
  obtain ⟨right_index, right_enabled, rfl⟩ := right
  rw [enabled_index_unique_local table deterministic left_enabled right_enabled]

private theorem step_iff_local {n q e : ℕ} (table : Table n q e)
    (deterministic : Deterministic table) {first last : State n q} :
    Reversible.step table first = some last ↔ StepRel table first last := by
  unfold Reversible.step
  split_ifs with available
  · constructor
    · intro result
      exact ⟨_, Fin.find_spec available, Option.some.inj result⟩
    · intro result
      exact congrArg some (stepRel_deterministic_local table deterministic
        ⟨_, Fin.find_spec available, rfl⟩ result)
  · simp only [false_iff]
    rintro ⟨index, enabled, _⟩
    exact available ⟨index, enabled⟩

private theorem residue_small_local (remainder : Fin p) :
    Counter.DivMod.residue p remainder.val = remainder := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt remainder.isLt

private theorem update_left_local (left right value : ℤ) :
    Function.update ![left, right] 0 value = ![value, right] := by
  funext index
  fin_cases index <;> simp

private theorem update_right_local (left right value : ℤ) :
    Function.update ![left, right] 1 value = ![left, value] := by
  funext index
  fin_cases index <;> simp

private theorem move_local (arc : Arc p) (first last : State 2 (size p))
    (enabled : (table p (arcEquiv p arc)).enabled first)
    (result : (table p (arcEquiv p arc)).execute first = last) :
    StateTransition.Reaches (step (table p)) first last := by
  apply Relation.ReflTransGen.single
  exact (step_iff_local (table p) (deterministic p)).mpr ⟨arcEquiv p arc, enabled, result⟩

private theorem consume_step_local (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
      (point p (nodeEquiv p (next p remainder)) input accumulator) := by
  have reading : StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
      (point p (block p remainder 1) (input + 1 : ℕ) accumulator) := by
    apply move_local p (.inr (remainder, 1))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
      omega
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  apply reading.trans
  apply move_local p (.inr (remainder, 2))
  · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
  · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block,
      update_left_local]

private theorem carry_reaches_local (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (block p 0 0) input (accumulator + 1 : ℕ)) := by
  have increment : StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (global p 2) input (accumulator + 1 : ℕ)) := by
    apply move_local p (.inl 1)
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, global,
        update_right_local]
  apply increment.trans
  apply move_local p (.inl 2)
  · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    omega
  · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]

/-- The quotient accumulates in the second register; the remainder stays in finite control. -/
theorem solution (input accumulator : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) input accumulator)
      (point p (block p (Counter.DivMod.residue p (input + remainder.val)) 2) 0
        (accumulator + (input + remainder.val) / p : ℕ)) := by
  change Relation.ReflTransGen (fun first last => last ∈ step (table p) first) _ _
  induction input generalizing accumulator remainder with
  | zero =>
      have stopped : StateTransition.Reaches (step (table p))
          (point p (block p remainder 0) 0 accumulator)
          (point p (block p remainder 2) 0 accumulator) := by
        apply move_local p (.inr (remainder, 0))
        · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
        · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
      simpa only [StateTransition.Reaches, Nat.zero_add, residue_small_local,
        Nat.div_eq_of_lt remainder.isLt, Nat.add_zero, Int.natCast_zero] using stopped
  | succ input recursive =>
      by_cases bound : remainder.val + 1 < p
      · let successor : Fin p := ⟨remainder.val + 1, bound⟩
        have consumed : StateTransition.Reaches (step (table p))
            (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
            (point p (block p successor 0) input accumulator) := by
          simpa only [next, dite_eq_left bound, block] using
            consume_step_local p remainder input accumulator
        have run := consumed.trans (recursive accumulator successor)
        have same_sum : input + successor.val = input + 1 + remainder.val := by
          dsimp [successor]
          omega
        simpa only [same_sum] using run
      · have last : remainder.val + 1 = p := by omega
        have consumed : StateTransition.Reaches (step (table p))
            (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
            (point p (global p 1) input accumulator) := by
          simpa only [next, dite_eq_right bound, global] using
            consume_step_local p remainder input accumulator
        have run := consumed.trans
          ((carry_reaches_local p input accumulator).trans (recursive (accumulator + 1) 0))
        have same_sum : input + 1 + remainder.val = input + p := by omega
        have residue_eq : Counter.DivMod.residue p (input + p) =
            Counter.DivMod.residue p input := by
          apply Fin.ext
          exact Nat.add_mod_right input p
        simpa only [Fin.val_zero, Nat.add_zero, same_sum, residue_eq,
          Nat.add_div_right input (Nat.pos_of_ne_zero (NeZero.ne p)),
          Nat.add_assoc, Nat.add_comm 1 (input / p)] using run
