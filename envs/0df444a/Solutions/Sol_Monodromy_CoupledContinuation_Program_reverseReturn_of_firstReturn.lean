-- Prove2me | solution 1 for Monodromy.CoupledContinuation.Program.reverseReturn_of_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:57:45.838432+00:00
-- url     : https://prove2.me/submissions/1a90cc76-165c-446b-a237-f00596f420f3

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
open Monodromy.CoupledContinuation.Program
variable {degree : ℕ} [NeZero degree]
theorem solution (forward backward boundary : Program degree)
    (inverse : Function.LeftInverse backward.advance forward.advance)
    {first after last : Memory} (initial : forward.step first = some after)
    (interior : Relation.ReflTransGen
      (fun left right => forward.step left = some right ∧ boundary.haltSignal left ≠ 1)
      after last)
    (marked : boundary.haltSignal first = 1) :
    reverseReturn backward boundary last = Part.some first := by
  have undo : ∀ {left right}, forward.step left = some right → backward.advance right = left := by
    intro left right edge
    unfold step at edge
    split at edge
    · contradiction
    · exact (congrArg backward.advance (Option.some.inj edge)).symm.trans (inverse left)
  have retraced : ∃ previous, backward.advance last = previous ∧
      StateTransition.Reaches (boundaryInverse backward boundary).step previous first := by
    induction interior with
    | refl => exact ⟨first, undo initial, Relation.ReflTransGen.refl⟩
    | @tail left right _ edge previous =>
        obtain ⟨before, arrived, rest⟩ := previous
        refine ⟨left, undo edge.1, Relation.ReflTransGen.head ?_ rest⟩
        change (if boundary.haltSignal left = 1 then none else some (backward.advance left)) =
          some before
        rw [ite_eq_right edge.2, arrived]
  obtain ⟨previous, arrived, rest⟩ := retraced
  unfold reverseReturn
  rw [arrived]
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr ⟨rest, by
    change (if boundary.haltSignal first = 1 then none else some (backward.advance first)) = none
    rw [ite_eq_left marked]⟩
