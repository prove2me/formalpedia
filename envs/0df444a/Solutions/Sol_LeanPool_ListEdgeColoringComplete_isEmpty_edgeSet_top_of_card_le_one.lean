-- Prove2me | solution 1 for LeanPool.ListEdgeColoringComplete.isEmpty_edgeSet_top_of_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:48:01.613116+00:00
-- url     : https://prove2.me/submissions/85f4fa56-3110-4d34-8542-f3c831b0641a

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Main

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
omit [DecidableEq V]
namespace LeanPool.ListEdgeColoringComplete
theorem _root_.solution [Fintype V] (h : Fintype.card V ≤ 1) :
    IsEmpty (⊤ : SimpleGraph V).edgeSet := by
  constructor
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using he
    exact hab (Fintype.card_le_one_iff.mp h a b)
end LeanPool.ListEdgeColoringComplete
