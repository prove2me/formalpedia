-- Prove2me | solution 1 for Monodromy.Counter.Reversible.RegisterRelocation.step_embed
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:14:58.067086+00:00
-- url     : https://prove2.me/submissions/4bf87fe2-47b2-4b4c-bdfd-a96153cda9b2

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
open Monodromy.Counter.Reversible.RegisterRelocation
variable {n m q e : ℕ}

theorem solution (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (valid : Deterministic source)
    (state : State n q) :
    step (mapTable register source) (embed register background state) =
      (step source state).map (embed register background) := by
  classical
  have extend_update (values : Fin n → ℤ) (index : Fin n) (value : ℤ) :
      Function.extend register (Function.update values index value) background =
        Function.update (Function.extend register values background) (register index) value := by
    funext target
    by_cases inRange : ∃ sourceIndex, register sourceIndex = target
    · obtain ⟨sourceIndex, rfl⟩ := inRange
      by_cases same : sourceIndex = index
      · subst sourceIndex
        simp [faithful.extend_apply]
      · have mappedDifferent : register sourceIndex ≠ register index :=
          fun equality => same (faithful equality)
        simp [faithful.extend_apply, same, mappedDifferent]
    · have different : register index ≠ target := by
        intro equality
        exact inRange ⟨index, equality⟩
      rw [Function.extend_apply' _ _ _ inRange, Function.update_of_ne different.symm,
        Function.extend_apply' _ _ _ inRange]
  have action_enabled_embed (action : Action n) :
      (mapAction register action).enabled (Function.extend register state.2 background) ↔
        action.enabled state.2 := by
    cases action <;> simp [mapAction, Action.enabled, faithful.extend_apply]
  have action_execute_embed (action : Action n) :
      (mapAction register action).apply (Function.extend register state.2 background) =
        Function.extend register (action.apply state.2) background := by
    cases action with
    | shift index amount =>
        simp only [mapAction, Action.apply]
        rw [extend_update, faithful.extend_apply]
    | test index atZero => rfl
  have enabled_embed (edge : Fin e) :
      ((mapTable register source) edge).enabled (embed register background state) ↔
        (source edge).enabled state := by
    exact and_congr Iff.rfl (action_enabled_embed (source edge).action)
  have execute_embed (edge : Fin e) :
      ((mapTable register source) edge).execute (embed register background state) =
        embed register background ((source edge).execute state) := by
    exact Prod.ext rfl (action_execute_embed (source edge).action)
  simp only [Reversible.step, enabled_embed, execute_embed, Option.map]
  split_ifs <;> rfl
