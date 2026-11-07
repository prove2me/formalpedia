-- Prove2me | solution 2 for Monodromy.ReversibleReturn.inverse_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:59:02.1865+00:00
-- url     : https://prove2.me/submissions/5cc8b2ce-44a1-4b03-81ed-9a99e0c612a3

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
open Monodromy.ReversibleReturn
variable {State : Type*}
theorem solution {advance backward : State → State} {boundary : State → Prop}
    (inverse : Function.LeftInverse backward advance) {first last : State}
    (run : FirstReturn advance boundary first last) :
    FirstReturn backward boundary last first := by
  obtain ⟨count, positive, reached, marked_first, marked_last, inside⟩ := run
  have retraced (round : ℕ) (bound : round ≤ count) :
      backward^[round] last = advance^[count - round] first := by
    have parts : round + (count - round) = count := by omega
    have decompose : last = advance^[round] (advance^[count - round] first) := by
      rw [← Function.iterate_add_apply, parts]
      exact reached.symm
    rw [decompose]
    exact (inverse.iterate round) _
  refine ⟨count, positive, ?_, marked_last, marked_first, ?_⟩
  · simpa only [Nat.sub_self, Function.iterate_zero_apply] using retraced count (by omega)
  · intro middle after_start before_end marked
    rw [retraced middle (by omega)] at marked
    exact inside (count - middle) (by omega) (by omega) marked
