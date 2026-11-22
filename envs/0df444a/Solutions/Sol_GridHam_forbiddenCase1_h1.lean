-- Prove2me | solution 1 for GridHam.forbiddenCase1_h1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:36.254807+00:00
-- url     : https://prove2.me/submissions/4e49dad0-5a36-43c6-b39b-85296b886e34

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width : ℕ) (s t : Coord) (hw : ¬ width = 1) :
    ForbiddenCase1 width 1 s t ↔
      ¬ ((s = (0, 0) ∧ t = (width - 1, 0)) ∨ (s = (width - 1, 0) ∧ t = (0, 0))) := by
  unfold ForbiddenCase1
  simp [hw]
end GridHam
