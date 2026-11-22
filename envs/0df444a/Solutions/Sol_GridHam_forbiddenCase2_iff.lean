-- Prove2me | solution 1 for GridHam.forbiddenCase2_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:22:55.081113+00:00
-- url     : https://prove2.me/submissions/78df963f-7ef2-4f07-8097-850d0ef7802d

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith
public import Theorems.Thm_GridHam_isCorner_iff

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) :
    ForbiddenCase2 w h (sx, sy) (tx, ty) ↔ F2A w h sx sy tx ty := by
  unfold ForbiddenCase2 F2A
  rw [isCorner_iff, isCorner_iff]
end GridHam
