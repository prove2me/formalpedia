-- Prove2me | solution 2 for Monodromy.CoupledContinuation.execute_B_left_zero
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:58:08.165646+00:00
-- url     : https://prove2.me/submissions/7ceacca7-33b1-4769-ba25-54e8e7c9045b

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Continuation
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.CoupledContinuation
theorem solution (state : Memory) (zero : state.val.1.1.val = 1) :
    (execute B_left state).val.2 = state.val.2 + NestedContinuation.period 1 := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  have left_zero : left = 0 := NestedContinuation.firstRoot_injective (by
    simpa only [prepare, NestedContinuation.firstRoot, NestedContinuation.period,
      Int.cast_zero, zero_mul, add_zero] using zero)
  subst left
  rw [execute_B_left]
  change upperRoot 0 right (control + if (0 : ℤ) = 0 then 1 else 0) =
    upperRoot 0 right control + NestedContinuation.period 1
  simp only [ite_true]
  simp only [upperRoot, NestedContinuation.period, Int.cast_add, Int.cast_one]
  ring
