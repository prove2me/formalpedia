-- Prove2me | solution 1 for Monodromy.ReversibleReturn.inverse_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:07:14.947197+00:00
-- url     : https://prove2.me/submissions/b39f7f2d-1665-45ef-a792-f0393c03d4e1

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

open Monodromy
open Monodromy.ReversibleReturn
variable {State : Type*}

theorem solution {advance backward : State → State} {boundary : State → Prop}
    (inverse : Function.LeftInverse backward advance) {first last : State}
    (run : FirstReturn advance boundary first last) :
    FirstReturn backward boundary last first := by
  rcases run with ⟨count, count_pos, reaches_last, first_boundary, last_boundary, first_time⟩
  refine ⟨count, count_pos, ?_, last_boundary, first_boundary, ?_⟩
  · rw [← reaches_last]
    exact inverse.iterate count first
  · intro middle middle_pos middle_lt backward_boundary
    have retraces : backward^[middle] last = advance^[count - middle] first := by
      calc
        backward^[middle] last = backward^[middle] (advance^[count] first) := by rw [reaches_last]
        _ = backward^[middle] (advance^[middle + (count - middle)] first) := by
          congr 2
          omega
        _ = backward^[middle] (advance^[middle] (advance^[count - middle] first)) := by
          rw [Function.iterate_add_apply]
        _ = advance^[count - middle] first := inverse.iterate middle _
    apply first_time (count - middle) (by omega) (by omega)
    rwa [← retraces]
