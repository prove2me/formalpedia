-- Prove2me | solution 2 for Monodromy.CounterContinuation.step_bind_step_encode
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:02:57.18662+00:00
-- url     : https://prove2.me/submissions/58fb3c26-70ab-4e25-a55e-de68cc061c00

-- Generated mechanically from the frozen source; no own-target import.
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
public import Theorems.Thm_Monodromy_CounterContinuation_simulates
public import Theorems.Thm_Monodromy_CounterContinuation_two_returns

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.CounterContinuation
variable {m : ℕ} [NeZero m]
theorem solution (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    ((compile program).step (encode state)).bind (compile program).step =
      (Counter.step program state).map encode := by
  cases source_step : Counter.step program state with
  | none =>
      have stopped := StateTransition.fun_respects.mp (simulates program) (a₁ := state)
      rw [source_step] at stopped
      change (compile program).step (encode state) = none at stopped
      rw [stopped]
      rfl
  | some result =>
      obtain ⟨middle, first_return, second_return⟩ := two_returns program state result source_step
      rw [first_return]
      exact second_return
