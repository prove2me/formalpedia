-- Prove2me | solution 1 for GridHam.pnext_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:45:14.469936+00:00
-- url     : https://prove2.me/submissions/2354ff8e-1548-411a-98dd-015b547ff656

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_chainAdjacent_suffix


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {x y : Coord} (hch : chainAdjacent p = true)
    (h : PNext p x y) : Adjacent x y := by
  obtain ⟨l1, l2, e⟩ := h
  rw [e] at hch
  have hc := chainAdjacent_suffix l1 _ hch
  have hc' : (adjacentB x y && chainAdjacent (y :: l2)) = true := by
    simpa [chainAdjacent] using hc
  simp at hc'
  unfold adjacentB at hc'
  exact of_decide_eq_true hc'.1
end GridHam
