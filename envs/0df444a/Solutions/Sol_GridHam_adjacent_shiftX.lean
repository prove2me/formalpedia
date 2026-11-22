-- Prove2me | solution 1 for GridHam.adjacent_shiftX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:20:25.904076+00:00
-- url     : https://prove2.me/submissions/c83274f6-6c10-41c2-a36b-ff1be410a7e1

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (d : ℕ) {v w : Coord} (h : Adjacent v w) :
    Adjacent (shiftX d v) (shiftX d w) := by
  unfold Adjacent at h ⊢
  unfold shiftX
  dsimp only
  omega
end GridHam
