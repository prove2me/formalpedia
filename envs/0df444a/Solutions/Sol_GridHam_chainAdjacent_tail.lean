-- Prove2me | solution 1 for GridHam.chainAdjacent_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:22.575719+00:00
-- url     : https://prove2.me/submissions/6c3d96b6-71be-4d34-9e1b-f16ed42b04a7

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (x : Coord) (L : List Coord) (h : chainAdjacent (x :: L) = true) :
    chainAdjacent L = true := by
  cases L with
  | nil => rfl
  | cons z r =>
    have hc' : (adjacentB x z && chainAdjacent (z :: r)) = true := by
      simpa [chainAdjacent] using h
    simp at hc'
    exact hc'.2
end GridHam
