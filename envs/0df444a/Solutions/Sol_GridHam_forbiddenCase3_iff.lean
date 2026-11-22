-- Prove2me | solution 1 for GridHam.forbiddenCase3_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:50:56.566094+00:00
-- url     : https://prove2.me/submissions/69c8c52c-b18e-4c58-8948-35a955aa50ae

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) :
    ForbiddenCase3 w h (sx, sy) (tx, ty) ↔ F3A w h sx sy tx ty := by
  unfold ForbiddenCase3 F3A G3 parity
  dsimp only
  split_ifs <;> constructor <;> intro h <;> omega
end GridHam
