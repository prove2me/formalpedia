-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Radix.carry_reaches
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:35:50.284691+00:00
-- url     : https://prove2.me/submissions/5839d7d2-c90f-4142-a62a-98ddc841135d

module

public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases

@[expose] public section

open Monodromy
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Radix

private theorem compatible_not_both {n : ℕ} {first second : Action n}
    (compatible : Action.Compatible first second) (values : Fin n → ℤ) :
    ¬ (Action.enabled first values ∧ Action.enabled second values) := by
  cases first <;> cases second <;> simp only [Action.Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  rename_i firstZero secondZero
  cases firstZero <;> cases secondZero <;> simp_all [Action.enabled]

private theorem enabled_index_unique {n q e : ℕ} (table : Table n q e)
    (deterministic : Deterministic table) {first second : Fin e} {state : State n q}
    (first_enabled : (table first).enabled state)
    (second_enabled : (table second).enabled state) : first = second := by
  by_contra different
  have compatible := deterministic first second different
    (first_enabled.1.trans second_enabled.1.symm)
  exact (compatible_not_both compatible state.2) ⟨first_enabled.2, second_enabled.2⟩

private theorem stepRel_deterministic {n q e : ℕ} (table : Table n q e)
    (deterministic : Deterministic table) {initial first second : State n q}
    (left : StepRel table initial first) (right : StepRel table initial second) :
    first = second := by
  obtain ⟨left_index, left_enabled, rfl⟩ := left
  obtain ⟨right_index, right_enabled, rfl⟩ := right
  rw [enabled_index_unique table deterministic left_enabled right_enabled]

private theorem step_iff_aux {n q e : ℕ} (table : Table n q e)
    (deterministic : Deterministic table) {first last : State n q} :
    step table first = some last ↔ StepRel table first last := by
  unfold step
  split_ifs with available
  · constructor
    · intro result
      exact ⟨_, Fin.find_spec available, Option.some.inj result⟩
    · intro result
      exact congrArg some (stepRel_deterministic table deterministic
        ⟨_, Fin.find_spec available, rfl⟩ result)
  · simp only [false_iff]
    rintro ⟨index, enabled, _⟩
    exact available ⟨index, enabled⟩

private theorem update_right (left right value : ℤ) :
    Function.update ![left, right] 1 value = ![left, value] := by
  funext index
  fin_cases index <;> simp

private theorem move (p : ℕ) [NeZero p] (arc : Arc p) (first last : State 2 (size p))
    (enabled : (table p (arcEquiv p arc)).enabled first)
    (result : (table p (arcEquiv p arc)).execute first = last) :
    StateTransition.Reaches (step (table p)) first last := by
  apply Relation.ReflTransGen.single
  exact (step_iff_aux (table p) (deterministic p)).mpr
    ⟨arcEquiv p arc, enabled, result⟩

theorem solution (p : ℕ) [NeZero p] (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (block p 0 0) input (accumulator + 1 : ℕ)) := by
  have increment : StateTransition.Reaches (step (table p))
      (point p (global p 1) input accumulator)
      (point p (global p 2) input (accumulator + 1 : ℕ)) := by
    apply move p (.inl 1)
    · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, global,
        update_right]
  apply increment.trans
  apply move p (.inl 2)
  · simp [table_arc, origin, operation, Edge.enabled, Action.enabled, point, global]
    omega
  · simp [table_arc, destination, operation, Edge.execute, Action.apply, point, block]
