-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Radix.transfer_cycle
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:10:24.123392+00:00
-- url     : https://prove2.me/submissions/23bc9558-cf4c-4b81-8c3a-ce779267e372

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

private theorem enabled_unique {n q e : ℕ} {table : Table n q e}
    (deterministic : Deterministic table) {state : State n q} {first second : Fin e}
    (first_enabled : (table first).enabled state)
    (second_enabled : (table second).enabled state) : first = second := by
  by_contra different
  have same_source : (table first).source = (table second).source :=
    first_enabled.1.trans second_enabled.1.symm
  have compatible := deterministic first second different same_source
  cases first_action : (table first).action with
  | shift =>
      cases second_action : (table second).action <;>
        simp_all [Action.Compatible, Action.enabled]
  | test register atZero =>
      cases second_action : (table second).action with
      | shift => simp_all [Action.Compatible, Action.enabled]
      | test other otherZero =>
          cases atZero <;> cases otherZero <;>
            simp_all [Edge.enabled, Action.Compatible, Action.enabled]

private theorem step_eq_of_enabled {n q e : ℕ} {table : Table n q e}
    (deterministic : Deterministic table) {state : State n q} {index : Fin e}
    (enabled : (table index).enabled state) :
    step table state = some ((table index).execute state) := by
  unfold Monodromy.Counter.Reversible.step
  split_ifs with available
  · have selected_enabled := Fin.find_spec
      (p := fun index => (table index).enabled state) available
    rw [enabled_unique deterministic selected_enabled enabled]
  · exact (available ⟨index, enabled⟩).elim

theorem solution (p : ℕ) [NeZero p] (remainder : Fin p) (input accumulator : ℕ) :
    StateTransition.Reaches (step (table p))
      (point p (block p remainder 3) accumulator (input + 1 : ℕ))
      (point p (block p remainder 3) (accumulator + 1 : ℕ) input) := by
  let s₀ := point p (block p remainder 3) accumulator (input + 1 : ℕ)
  let s₁ := point p (block p remainder 4) accumulator (input + 1 : ℕ)
  let s₂ := point p (block p remainder 5) accumulator input
  let s₃ := point p (block p remainder 6) (accumulator + 1 : ℕ) input
  let s₄ := point p (block p remainder 3) (accumulator + 1 : ℕ) input
  have h₁ : step (table p) s₀ = some s₁ := by
    let arc : Arc p := .inr (remainder, (5 : Fin 9))
    calc
      step (table p) s₀ = some ((table p (arcEquiv p arc)).execute s₀) :=
        step_eq_of_enabled (deterministic p) (by
          simp [arc, s₀, table_arc, Edge.enabled, origin, operation, Action.enabled, point,
            block] <;> omega)
      _ = some s₁ := by
        simp [arc, s₀, s₁, table_arc, Edge.execute, origin, destination, operation,
          Action.apply, point, block]
  have h₂ : step (table p) s₁ = some s₂ := by
    let arc : Arc p := .inr (remainder, (6 : Fin 9))
    calc
      step (table p) s₁ = some ((table p (arcEquiv p arc)).execute s₁) :=
        step_eq_of_enabled (deterministic p) (by
          simp [arc, s₁, table_arc, Edge.enabled, origin, operation, Action.enabled, point,
            block])
      _ = some s₂ := by
        simp [arc, s₁, s₂, table_arc, Edge.execute, origin, destination, operation,
          Action.apply, point, block]
        funext i
        fin_cases i <;> rfl
  have h₃ : step (table p) s₂ = some s₃ := by
    let arc : Arc p := .inr (remainder, (7 : Fin 9))
    calc
      step (table p) s₂ = some ((table p (arcEquiv p arc)).execute s₂) :=
        step_eq_of_enabled (deterministic p) (by
          simp [arc, s₂, table_arc, Edge.enabled, origin, operation, Action.enabled, point,
            block])
      _ = some s₃ := by
        simp [arc, s₂, s₃, table_arc, Edge.execute, origin, destination, operation,
          Action.apply, point, block]
        funext i
        fin_cases i <;> rfl
  have h₄ : step (table p) s₃ = some s₄ := by
    let arc : Arc p := .inr (remainder, (8 : Fin 9))
    calc
      step (table p) s₃ = some ((table p (arcEquiv p arc)).execute s₃) :=
        step_eq_of_enabled (deterministic p) (by
          simp [arc, s₃, table_arc, Edge.enabled, origin, operation, Action.enabled, point,
            block] <;> omega)
      _ = some s₄ := by
        simp [arc, s₃, s₄, table_arc, Edge.execute, origin, destination, operation,
          Action.apply, point, block]
  change Relation.ReflTransGen (fun a b => b ∈ Monodromy.Counter.Reversible.step (table p) a) s₀ s₄
  refine Relation.ReflTransGen.head
    (r := fun a b => b ∈ Monodromy.Counter.Reversible.step (table p) a) h₁ ?_
  refine Relation.ReflTransGen.head
    (r := fun a b => b ∈ Monodromy.Counter.Reversible.step (table p) a) h₂ ?_
  refine Relation.ReflTransGen.head
    (r := fun a b => b ∈ Monodromy.Counter.Reversible.step (table p) a) h₃ ?_
  exact Relation.ReflTransGen.single h₄
