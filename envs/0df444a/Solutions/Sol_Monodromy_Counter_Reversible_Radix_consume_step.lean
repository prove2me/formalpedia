-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Radix.consume_step
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:07:55.706593+00:00
-- url     : https://prove2.me/submissions/bb932ecd-0e83-4079-b8cd-c1cee4642329

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Computability.StateTransition
public import Mathlib.Tactic.FinCases

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Radix
variable (p : ℕ) [NeZero p]

private theorem execute_eq_of_deterministic {n q e : ℕ} {table : Table n q e}
    (deterministic : Deterministic table) {state : State n q} {first second : Fin e}
    (first_enabled : (table first).enabled state)
    (second_enabled : (table second).enabled state) :
    (table first).execute state = (table second).execute state := by
  by_cases same : first = second
  · subst second
    rfl
  · have compatible := deterministic first second same
      (first_enabled.1.trans second_enabled.1.symm)
    cases first_action : (table first).action with
    | shift register amount =>
        cases second_action : (table second).action with
        | shift other amount' => simp [Action.Compatible, first_action, second_action] at compatible
        | test other atZero => simp [Action.Compatible, first_action, second_action] at compatible
    | test register atZero =>
        cases second_action : (table second).action with
        | shift other amount => simp [Action.Compatible, first_action, second_action] at compatible
        | test other secondZero =>
            simp only [Action.Compatible, first_action, second_action] at compatible
            obtain ⟨rfl, different⟩ := compatible
            have first_guard := first_enabled.2
            have second_guard := second_enabled.2
            rw [first_action] at first_guard
            rw [second_action] at second_guard
            simp only [Action.enabled] at first_guard second_guard
            have same_bool : atZero = true ↔ secondZero = true :=
              first_guard.symm.trans second_guard
            have : atZero = secondZero := by cases atZero <;> cases secondZero <;> simp_all
            exact (different this).elim

private theorem step_eq_of_deterministic {n q e : ℕ} {table : Table n q e}
    (deterministic : Deterministic table) {state : State n q} (index : Fin e)
    (enabled : (table index).enabled state) :
    Reversible.step table state = some ((table index).execute state) := by
  have available : ∃ other, (table other).enabled state := ⟨index, enabled⟩
  rw [Reversible.step, dif_pos available]
  congr 1
  exact execute_eq_of_deterministic deterministic (Fin.find_spec available) enabled

theorem solution (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 0) (input + 1 : ℕ) accumulator)
      (point p (nodeEquiv p (next p remainder)) input accumulator) := by
  let firstState := point p (block p remainder 0) (input + 1 : ℕ) accumulator
  let middleState := point p (block p remainder 1) (input + 1 : ℕ) accumulator
  have first_enabled : ((table p) (arcEquiv p (.inr (remainder, (1 : Fin 9))))).enabled firstState := by
    simp [table_arc, origin, operation, firstState, point, block, Edge.enabled, Action.enabled]
    omega
  have first_step : step (table p) firstState = some middleState := by
    rw [step_eq_of_deterministic (deterministic p) _ first_enabled]
    simp [table_arc, destination, operation, middleState, point, block, Edge.execute, Action.apply]
    rfl
  have second_enabled : ((table p) (arcEquiv p (.inr (remainder, (2 : Fin 9))))).enabled middleState := by
    simp [table_arc, origin, operation, middleState, point, block, Edge.enabled, Action.enabled]
  have second_step : step (table p) middleState =
      some (point p (nodeEquiv p (next p remainder)) input accumulator) := by
    rw [step_eq_of_deterministic (deterministic p) _ second_enabled]
    simp [table_arc, destination, operation, middleState, point, Edge.execute, Action.apply]
    funext register
    fin_cases register <;> simp
  apply Relation.ReflTransGen.head (b := middleState)
  · rw [first_step]
    rfl
  · apply Relation.ReflTransGen.single
    rw [second_step]
    rfl
