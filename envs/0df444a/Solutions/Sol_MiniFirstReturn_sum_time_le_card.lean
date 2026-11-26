-- Prove2me | solution 1 for MiniFirstReturn.sum_time_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:07:53.190816+00:00
-- url     : https://prove2.me/submissions/8d38b4ac-1ffd-44a6-b4ce-9ba30fb2a1d8

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_MiniFirstReturn_intervalPoint_injective

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
variable (d : ℕ) [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] graphAdjDecidable
attribute [local instance] vertexDecidableEq
open MiniFirstReturn
open scoped BigOperators
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace MiniFirstReturn
theorem _root_.solution {I : Type*} [Fintype I]
    (p : Equiv.Perm X) (B : Finset X) (bases : I → B)
    (hbases : Function.Injective bases) :
    ∑ i : I, time p B (bases i) ≤ Fintype.card X := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_le_of_injective (intervalPoint p B bases)
      (intervalPoint_injective p B bases hbases)
end MiniFirstReturn
