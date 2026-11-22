-- Prove2me | solution 1 for GridHam.adjacent_swapXY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:22:07.697357+00:00
-- url     : https://prove2.me/submissions/4c8906bc-54ab-4016-a891-9342989cec2d

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {v w : Coord} (h : Adjacent v w) : Adjacent (swapXY v) (swapXY w) := by
  unfold Adjacent at h ⊢
  unfold swapXY
  dsimp only
  omega
end GridHam
