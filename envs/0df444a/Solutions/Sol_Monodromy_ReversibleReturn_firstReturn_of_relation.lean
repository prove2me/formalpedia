-- Prove2me | solution 1 for Monodromy.ReversibleReturn.firstReturn_of_relation
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:59:00.761755+00:00
-- url     : https://prove2.me/submissions/c48d83f0-7f8b-4d4a-ba6a-6368914c8e53

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
theorem solution {advance : State → State} {boundary : State → Prop}
    {transition : State → State → Prop}
    (executes : ∀ {left right}, transition left right → advance left = right)
    {first after last : State} (initial : transition first after)
    (interior : Relation.ReflTransGen
      (fun left right => transition left right ∧ ¬ boundary left) after last)
    (marked_first : boundary first) (marked_last : boundary last) :
    FirstReturn advance boundary first last := by
  have traced : ∃ count : ℕ, 0 < count ∧ advance^[count] first = last ∧
      ∀ middle : ℕ, 0 < middle → middle < count → ¬ boundary (advance^[middle] first) := by
    clear marked_first marked_last
    induction interior with
    | refl =>
        refine ⟨1, by omega, executes initial, ?_⟩
        intro middle positive before
        omega
    | @tail left right _ edge previous =>
        obtain ⟨count, positive, reached, inside⟩ := previous
        refine ⟨count + 1, by omega, ?_, ?_⟩
        · rw [Function.iterate_succ_apply', reached]
          exact executes edge.1
        · intro middle after_start before_end
          by_cases before : middle < count
          · exact inside middle after_start before
          · have equal : middle = count := by omega
            rw [equal, reached]
            exact edge.2
  obtain ⟨count, positive, reached, inside⟩ := traced
  exact ⟨count, positive, reached, marked_first, marked_last, inside⟩
