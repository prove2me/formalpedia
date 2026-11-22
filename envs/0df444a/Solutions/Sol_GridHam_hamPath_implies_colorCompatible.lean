-- Prove2me | solution 1 for GridHam.hamPath_implies_colorCompatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:27:44.922946+00:00
-- url     : https://prove2.me/submissions/2fb881c9-2d64-4178-9a07-74425ee9024a

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring
public import Theorems.Thm_GridHam_hamPath_implies_diff_parity_of_even
public import Theorems.Thm_GridHam_odd_mul_iff_c
public import Theorems.Thm_GridHam_hamPath_odd_parity

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (h : HasHamPath width height s t) :
    ColorCompatible width height s t := by
  unfold ColorCompatible
  split
  case isTrue hodd =>
    exact hamPath_odd_parity width height s t ((odd_mul_iff_c width height).mp hodd) h
  case isFalse heven =>
    exact hamPath_implies_diff_parity_of_even width height s t
      (by omega) h
end GridHam
