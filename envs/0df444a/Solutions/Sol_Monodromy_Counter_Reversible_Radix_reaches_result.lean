-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Radix.reaches_result
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:33:52.65262+00:00
-- url     : https://prove2.me/submissions/0817361e-b805-41e1-a92a-a2bbd0087ff7

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

private theorem residue_small_aux (remainder : Fin p) :
    Counter.DivMod.residue p remainder.val = remainder := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt remainder.isLt

section StepCharacterization

variable {n q e : ℕ}

private theorem compatible_not_both_aux {first second : Action n}
    (compatible : Action.Compatible first second) (values : Fin n → ℤ) :
    ¬ (Action.enabled first values ∧ Action.enabled second values) := by
  cases first <;> cases second <;> simp only [Action.Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  rename_i firstZero secondZero
  cases firstZero <;> cases secondZero <;> simp_all [Action.enabled]

private theorem enabled_index_unique_aux (table : Table n q e)
    (deterministic : Deterministic table) {first second : Fin e} {state : State n q}
    (first_enabled : (table first).enabled state)
    (second_enabled : (table second).enabled state) : first = second := by
  by_contra different
  have compatible := deterministic first second different
    (first_enabled.1.trans second_enabled.1.symm)
  exact (compatible_not_both_aux compatible state.2) ⟨first_enabled.2, second_enabled.2⟩

private theorem stepRel_deterministic_aux (table : Table n q e)
    (deterministic : Deterministic table) {initial first second : State n q}
    (left : StepRel table initial first) (right : StepRel table initial second) :
    first = second := by
  obtain ⟨left_index, left_enabled, rfl⟩ := left
  obtain ⟨right_index, right_enabled, rfl⟩ := right
  rw [enabled_index_unique_aux table deterministic left_enabled right_enabled]

private theorem step_iff_aux (table : Table n q e) (deterministic : Deterministic table)
    {first last : State n q} : step table first = some last ↔ StepRel table first last := by
  unfold Reversible.step
  split_ifs with available
  · constructor
    · intro result
      exact ⟨_, Fin.find_spec available, Option.some.inj result⟩
    · intro result
      exact congrArg some (stepRel_deterministic_aux table deterministic
        ⟨_, Fin.find_spec available, rfl⟩ result)
  · simp only [false_iff]
    rintro ⟨index, enabled, _⟩
    exact available ⟨index, enabled⟩

end StepCharacterization

private theorem update_left (left right value : ℤ) :
    Function.update ![left, right] 0 value = ![value, right] := by
  funext index
  fin_cases index <;> simp

private theorem update_right (left right value : ℤ) :
    Function.update ![left, right] 1 value = ![left, value] := by
  funext index
  fin_cases index <;> simp

private theorem move (arc : Arc p) (first last : State 2 (size p))
    (enabled : (table p (arcEquiv p arc)).enabled first)
    (result : (table p (arcEquiv p arc)).execute first = last) :
    StateTransition.Reaches (step (table p)) first last := by
  apply Relation.ReflTransGen.single
  exact (step_iff_aux (table p) (deterministic p)).mpr ⟨arcEquiv p arc, enabled, result⟩

/-- Consuming one unit reaches the next remainder port, before any quotient carry. -/
theorem consume_step (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
      (point p (nodeEquiv p (next p remainder)) input accumulator) := by
  have reading : StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
      (point p (block p remainder 1) (input + 1 : ℕ) accumulator) := by
    apply move p (.inr (remainder, 1))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
      omega
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  apply reading.trans
  apply move p (.inr (remainder, 2))
  · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
  · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, update_left]

/-- A completed radix block increments the quotient and re-enters remainder zero. -/
theorem carry_reaches (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (block p 0 0) input (accumulator + 1 : ℕ)) := by
  have increment : StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (global p 2) input (accumulator + 1 : ℕ)) := by
    apply move p (.inl 1)
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, global, update_right]
  apply increment.trans
  apply move p (.inl 2)
  · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    omega
  · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]

/-- The quotient accumulates in the second register; the remainder stays in finite control. -/
theorem consume_reaches (input accumulator : ℕ) (remainder : Fin p) :
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
        apply move p (.inr (remainder, 0))
        · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
        · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
      simpa only [StateTransition.Reaches, Nat.zero_add, residue_small_aux,
        Nat.div_eq_of_lt remainder.isLt, Nat.add_zero, Int.natCast_zero] using stopped
  | succ input recursive =>
      by_cases bound : remainder.val + 1 < p
      · let successor : Fin p := ⟨remainder.val + 1, bound⟩
        have consumed : StateTransition.Reaches (step (table p))
            (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
            (point p (block p successor 0) input accumulator) := by
          simpa only [next, dite_eq_left bound, block] using consume_step p remainder input accumulator
        have run := consumed.trans (recursive accumulator successor)
        have same_sum : input + successor.val = input + 1 + remainder.val := by
          dsimp [successor]
          omega
        simpa only [same_sum] using run
      · have last : remainder.val + 1 = p := by omega
        have consumed : StateTransition.Reaches (step (table p))
            (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
            (point p (global p 1) input accumulator) := by
          simpa only [next, dite_eq_right bound, global] using consume_step p remainder input accumulator
        have run := consumed.trans
          ((carry_reaches p input accumulator).trans (recursive (accumulator + 1) 0))
        have same_sum : input + 1 + remainder.val = input + p := by omega
        have residue_eq : Counter.DivMod.residue p (input + p) = Counter.DivMod.residue p input := by
          apply Fin.ext
          exact Nat.add_mod_right input p
        simpa only [Fin.val_zero, Nat.add_zero, same_sum, residue_eq,
          Nat.add_div_right input (Nat.pos_of_ne_zero (NeZero.ne p)),
          Nat.add_assoc, Nat.add_comm 1 (input / p)] using run

/-- One transfer cycle preserves the remainder address and returns one unit to the first register. -/
theorem transfer_cycle (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator (input + 1 : ℕ))
      (point p (block p remainder 3) (accumulator + 1 : ℕ) input) := by
  have reading : StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator (input + 1 : ℕ))
      (point p (block p remainder 4) accumulator (input + 1 : ℕ)) := by
    apply move p (.inr (remainder, 5))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
      omega
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  have decrement : StateTransition.Reaches (step (table p))
      (point p (block p remainder 4) accumulator (input + 1 : ℕ))
      (point p (block p remainder 5) accumulator input) := by
    apply move p (.inr (remainder, 6))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block, update_right]
  have increment : StateTransition.Reaches (step (table p))
      (point p (block p remainder 5) accumulator input)
      (point p (block p remainder 6) (accumulator + 1 : ℕ) input) := by
    apply move p (.inr (remainder, 7))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block, update_left]
  have returning : StateTransition.Reaches (step (table p))
      (point p (block p remainder 6) (accumulator + 1 : ℕ) input)
      (point p (block p remainder 3) (accumulator + 1 : ℕ) input) := by
    apply move p (.inr (remainder, 8))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
      omega
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  exact reading.trans (decrement.trans (increment.trans returning))

/-- Transferring the quotient back clears the second register. -/
theorem transfer_reaches (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator input)
      (point p (finish p remainder) (accumulator + input : ℕ) 0) := by
  change Relation.ReflTransGen (fun first last => last ∈ step (table p) first) _ _
  induction input generalizing accumulator with
  | zero =>
      have stopped : StateTransition.Reaches (step (table p))
          (point p (block p remainder 3) accumulator 0)
          (point p (finish p remainder) accumulator 0) := by
        apply move p (.inr (remainder, 4))
        · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
        · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, finish, block]
      simpa only [StateTransition.Reaches, Nat.add_zero, Int.natCast_zero] using stopped
  | succ input recursive =>
      have run := (transfer_cycle p remainder input accumulator).trans (recursive (accumulator + 1))
      simpa only [Nat.add_assoc, Nat.add_comm 1 input] using run

/-- One fixed table computes quotient and remainder for every natural input. -/
theorem solution (input : ℕ) :
    StateTransition.Reaches (step (table p)) (point p (entry p) input 0)
      (point p (finish p (Counter.DivMod.residue p input)) (input / p : ℕ) 0) := by
  have entering : StateTransition.Reaches (step (table p))
      (point p (entry p) input 0) (point p (block p 0 0) input 0) := by
    apply move p (.inl 0)
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, entry, global]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  have consumed := consume_reaches p input 0 0
  simp only [Fin.val_zero, Nat.add_zero, Nat.zero_add] at consumed
  have transfer_entry : StateTransition.Reaches (step (table p))
      (point p (block p (Counter.DivMod.residue p input) 2) 0 (input / p : ℕ))
      (point p (block p (Counter.DivMod.residue p input) 3) 0 (input / p : ℕ)) := by
    apply move p (.inr (Counter.DivMod.residue p input, 3))
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, block]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
  have transferred := transfer_reaches p (Counter.DivMod.residue p input) (input / p) 0
  simp only [Nat.zero_add] at transferred
  exact entering.trans (consumed.trans (transfer_entry.trans transferred))
