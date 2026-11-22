-- Prove2me | solution 1 for GridHam.forbiddenCase1_w1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:23.412327+00:00
-- url     : https://prove2.me/submissions/b92a7f3d-0a30-49f4-9084-8266c0eba85a

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (height : ℕ) (s t : Coord) :
    ForbiddenCase1 1 height s t ↔
      ¬ ((s = (0, 0) ∧ t = (0, height - 1)) ∨ (s = (0, height - 1) ∧ t = (0, 0))) := by
  unfold ForbiddenCase1
  simp
end GridHam
