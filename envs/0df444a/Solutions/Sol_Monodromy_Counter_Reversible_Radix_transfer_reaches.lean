-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Radix.transfer_reaches
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:10:06.232287+00:00
-- url     : https://prove2.me/submissions/24911bff-bdd2-491a-ac6f-8fb646beac7a

import Definitions.Def_Monodromy_Counter
import Mathlib.Computability.StateTransition
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Radix

private theorem compatible_not_both_enabled {n : ℕ} {first second : Action n}
    {values : Fin n → ℤ} (compatible : Action.Compatible first second) :
    ¬ (Action.enabled first values ∧ Action.enabled second values) := by
  cases first with
  | shift register amount => simp [Action.Compatible] at compatible
  | test register atZero =>
      cases second with
      | shift other amount => simp [Action.Compatible] at compatible
      | test other otherZero =>
          simp only [Action.Compatible] at compatible
          rcases compatible with ⟨rfl, different⟩
          cases atZero <;> cases otherZero <;> simp_all [Action.enabled]

private theorem step_of_enabled {n q e : ℕ} (table : Table n q e)
    (deterministic : Deterministic table) (index : Fin e) (state : State n q)
    (enabled : (table index).enabled state) :
    step table state = some ((table index).execute state) := by
  have available : ∃ index, (table index).enabled state := ⟨index, enabled⟩
  rw [Reversible.step, dif_pos available]
  let chosen := Fin.find (fun index => (table index).enabled state) available
  have chosenEnabled : (table chosen).enabled state := Fin.find_spec available
  have same : chosen = index := by
    by_contra different
    have compatible := deterministic chosen index different
      (chosenEnabled.1.trans enabled.1.symm)
    exact compatible_not_both_enabled compatible ⟨chosenEnabled.2, enabled.2⟩
  change some ((table chosen).execute state) = some ((table index).execute state)
  rw [same]

private theorem transfer_cycle_direct (p : ℕ) [NeZero p]
    (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator (input + 1 : ℕ))
      (point p (block p remainder 3) (accumulator + 1 : ℕ) input) := by
  have firstEnabled :
      (table p (arcEquiv p (.inr (remainder, (5 : Fin 9))))).enabled
        (point p (block p remainder 3) accumulator (input + 1 : ℕ)) := by
    simp [table_arc, Edge.enabled, origin, operation, block, point, Action.enabled]
    omega
  have firstStep :
      step (table p) (point p (block p remainder 3) accumulator (input + 1 : ℕ)) =
        some (point p (block p remainder 4) accumulator (input + 1 : ℕ)) := by
    rw [step_of_enabled (table p) (deterministic p) _ _ firstEnabled]
    simp [Edge.execute, table_arc, destination, operation, block, point, Action.apply]
  have secondEnabled :
      (table p (arcEquiv p (.inr (remainder, (6 : Fin 9))))).enabled
        (point p (block p remainder 4) accumulator (input + 1 : ℕ)) := by
    simp [table_arc, Edge.enabled, origin, operation, block, point, Action.enabled]
  have secondStep :
      step (table p) (point p (block p remainder 4) accumulator (input + 1 : ℕ)) =
        some (point p (block p remainder 5) accumulator input) := by
    rw [step_of_enabled (table p) (deterministic p) _ _ secondEnabled]
    simp [Edge.execute, table_arc, destination, operation, block, point, Action.apply]
    funext i
    fin_cases i <;> simp
  have thirdEnabled :
      (table p (arcEquiv p (.inr (remainder, (7 : Fin 9))))).enabled
        (point p (block p remainder 5) accumulator input) := by
    simp [table_arc, Edge.enabled, origin, operation, block, point, Action.enabled]
  have thirdStep :
      step (table p) (point p (block p remainder 5) accumulator input) =
        some (point p (block p remainder 6) (accumulator + 1 : ℕ) input) := by
    rw [step_of_enabled (table p) (deterministic p) _ _ thirdEnabled]
    simp [Edge.execute, table_arc, destination, operation, block, point, Action.apply]
    funext i
    fin_cases i <;> simp
  have fourthEnabled :
      (table p (arcEquiv p (.inr (remainder, (8 : Fin 9))))).enabled
        (point p (block p remainder 6) (accumulator + 1 : ℕ) input) := by
    simp [table_arc, Edge.enabled, origin, operation, block, point, Action.enabled]
    omega
  have fourthStep :
      step (table p) (point p (block p remainder 6) (accumulator + 1 : ℕ) input) =
        some (point p (block p remainder 3) (accumulator + 1 : ℕ) input) := by
    rw [step_of_enabled (table p) (deterministic p) _ _ fourthEnabled]
    simp [Edge.execute, table_arc, destination, operation, block, point, Action.apply]
  apply Relation.ReflTransGen.head (b := point p (block p remainder 4) accumulator (input + 1 : ℕ))
  · rw [firstStep]
    rfl
  apply Relation.ReflTransGen.head (b := point p (block p remainder 5) accumulator input)
  · rw [secondStep]
    rfl
  apply Relation.ReflTransGen.head
    (b := point p (block p remainder 6) (accumulator + 1 : ℕ) input)
  · rw [thirdStep]
    rfl
  apply Relation.ReflTransGen.head
    (b := point p (block p remainder 3) (accumulator + 1 : ℕ) input)
  · rw [fourthStep]
    rfl
  exact Relation.ReflTransGen.refl

theorem solution (p : ℕ) [NeZero p] (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator input)
      (point p (finish p remainder) (accumulator + input : ℕ) 0) := by
  induction input generalizing accumulator with
  | zero =>
      simp only [Nat.cast_zero, Nat.add_zero]
      have enabled :
          (table p (arcEquiv p (.inr (remainder, (4 : Fin 9))))).enabled
            (point p (block p remainder 3) accumulator 0) := by
        simp [table_arc, Edge.enabled, origin, operation, block, point, Action.enabled]
      have finalStep :
          step (table p) (point p (block p remainder 3) accumulator 0) =
            some (point p (finish p remainder) accumulator 0) := by
        rw [step_of_enabled (table p) (deterministic p) _ _ enabled]
        simp [Edge.execute, table_arc, destination, operation, block, point, finish,
          Action.apply]
      apply Relation.ReflTransGen.head
        (b := point p (finish p remainder) accumulator 0)
      · rw [finalStep]
        rfl
      exact Relation.ReflTransGen.refl
  | succ input ih =>
      apply Relation.ReflTransGen.trans
        (transfer_cycle_direct p remainder input accumulator)
      change StateTransition.Reaches (step (table p))
        (point p (block p remainder 3) (accumulator + 1 : ℕ) input)
        (point p (finish p remainder) (accumulator + (input + 1) : ℕ) 0)
      rw [show accumulator + (input + 1) = accumulator + 1 + input by omega]
      exact ih (accumulator + 1)
