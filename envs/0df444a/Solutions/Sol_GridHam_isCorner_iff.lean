-- Prove2me | solution 1 for GridHam.isCorner_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:20:06.915271+00:00
-- url     : https://prove2.me/submissions/4220cfa0-5b4a-4f3f-9763-36d485ef7a56

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_Arith

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h x y : ℕ) : IsCorner w h (x, y) ↔ cornerA w h x y := by
  unfold IsCorner cornerA
  simp only [Prod.mk.injEq]
  constructor <;> intro h <;> omega
end GridHam
