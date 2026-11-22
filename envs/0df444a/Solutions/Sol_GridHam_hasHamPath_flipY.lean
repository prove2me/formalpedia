-- Prove2me | solution 1 for GridHam.hasHamPath_flipY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:35:56.599556+00:00
-- url     : https://prove2.me/submissions/68e3ae2b-00f6-46ba-b6bd-9545dcda2129

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Theorems.Thm_GridHam_hasHamPath_reflect
public import Theorems.Thm_GridHam_hasHamPath_transpose


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {w h : ℕ} {s t : Coord} (hp : HasHamPath w h s t) :
    HasHamPath w h (s.1, h - 1 - s.2) (t.1, h - 1 - t.2) :=
  hasHamPath_transpose (hasHamPath_reflect (hasHamPath_transpose hp))
end GridHam
