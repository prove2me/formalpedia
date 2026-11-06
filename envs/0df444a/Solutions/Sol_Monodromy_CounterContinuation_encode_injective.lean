-- Prove2me | solution 1 for Monodromy.CounterContinuation.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:23:30.782351+00:00
-- url     : https://prove2.me/submissions/7ecfbdc2-a957-4c21-85f0-3ab49fc10b10

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
open Monodromy.CounterContinuation
open CoupledContinuation
variable {m : ℕ}

theorem solution : Function.Injective (@encode m) := by
  intro state state' same
  have prepared :
      (((state.counters 0 : ℤ), (state.counters 1 : ℤ)), label state.pc 0) =
        (((state'.counters 0 : ℤ), (state'.counters 1 : ℤ)), label state'.pc 0) :=
    prepare_injective same
  have left : state.counters 0 = state'.counters 0 := by
    have leftInt := congrArg (fun labels : ((ℤ × ℤ) × ℤ) => labels.1.1) prepared
    change (state.counters 0 : ℤ) = (state'.counters 0 : ℤ) at leftInt
    exact_mod_cast leftInt
  have right : state.counters 1 = state'.counters 1 := by
    have rightInt := congrArg (fun labels : ((ℤ × ℤ) × ℤ) => labels.1.2) prepared
    change (state.counters 1 : ℤ) = (state'.counters 1 : ℤ) at rightInt
    exact_mod_cast rightInt
  have pc : state.pc = state'.pc := by
    have sameLabel := congrArg Prod.snd prepared
    simp only [label] at sameLabel
    have sameValue :
        (finProdFinEquiv (state.pc, (0 : Fin 3))).val =
          (finProdFinEquiv (state'.pc, (0 : Fin 3))).val := by
      exact_mod_cast sameLabel
    have samePair := finProdFinEquiv.injective (Fin.ext sameValue)
    exact congrArg Prod.fst samePair
  cases state with
  | mk position counters =>
    cases state' with
    | mk position' counters' =>
      cases pc
      congr
      funext register
      fin_cases register
      · exact left
      · exact right
