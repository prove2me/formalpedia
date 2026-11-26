-- Prove2me | solution 1 for NonbacktrackingWalk.card_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:36.106071+00:00
-- url     : https://prove2.me/submissions/e609b6b1-8e12-415d-8b04-9a41effce01b

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution

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
theorem _root_.solution {d : ℕ} (hG : IsRegularOfDegree G d) {k : ℕ}
    (w : NonbacktrackingWalk G start (k + 1)) : Nat.card (Extension w) = d - 1 := by
  classical
  rw [Nat.card_congr (extensionEquivLegalNeighbor w)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl
    (fun x : G.neighborSet w.endVertex ↦ x = w.previousNeighbor)]
  have hn : Fintype.card (G.neighborSet w.endVertex) = d := by
    simpa only [Nat.card_eq_fintype_card] using hG w.endVertex
  rw [hn]
  simp
end NonbacktrackingWalk
