-- Prove2me | solution 1 for NonbacktrackingWalk.card_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:18.826167+00:00
-- url     : https://prove2.me/submissions/605023d6-b3ca-4bf6-a4d8-c6a99c776f3a

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_NonbacktrackingWalk_card_extension

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
open NonbacktrackingWalk
variable {G : SimpleGraph V} {start : OrientedEdge G}
namespace NonbacktrackingWalk
theorem _root_.solution {d : ℕ} (hG : IsRegularOfDegree G d) (k : ℕ) :
    Nat.card (NonbacktrackingWalk G start (k + 2)) =
      (d - 1) * Nat.card (NonbacktrackingWalk G start (k + 1)) := by
  classical
  let : Fintype (NonbacktrackingWalk G start (k + 1)) := Fintype.ofFinite _
  let : ∀ w : NonbacktrackingWalk G start (k + 1), Fintype (Extension w) :=
    fun _ ↦ Fintype.ofFinite _
  rw [Nat.card_congr (appendEquiv k), Nat.card_sigma]
  simp_rw [card_extension hG]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp [mul_comm]
end NonbacktrackingWalk
