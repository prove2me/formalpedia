-- Prove2me | solution 1 for GridHam.cnt1_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:24:15.971809+00:00
-- url     : https://prove2.me/submissions/5d3c6f21-3703-417a-827f-e4ccd109602a

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (l1 l2 : List Coord) : cnt1 (l1 ++ l2) = cnt1 l1 + cnt1 l2 := by
  unfold cnt1
  simp [List.countP_append]
end GridHam
