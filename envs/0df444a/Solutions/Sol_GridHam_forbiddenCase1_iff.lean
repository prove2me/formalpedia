-- Prove2me | solution 1 for GridHam.forbiddenCase1_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:42.488862+00:00
-- url     : https://prove2.me/submissions/e69d1817-f6f4-4ae5-84ee-fbdfd512a664

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h sx sy tx ty : ℕ) :
    ForbiddenCase1 w h (sx, sy) (tx, ty) ↔ F1A w h sx sy tx ty := by
  unfold ForbiddenCase1 F1A
  dsimp only
  split_ifs <;> simp only [Prod.mk.injEq] <;> constructor <;> intro h <;> omega
end GridHam
