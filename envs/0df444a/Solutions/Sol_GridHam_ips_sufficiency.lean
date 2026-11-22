-- Prove2me | solution 1 for GridHam.ips_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:56:31.123116+00:00
-- url     : https://prove2.me/submissions/8f80c3ec-4791-4b99-9e8d-02110f924a74

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
public import Theorems.Thm_GridHam_suff_all

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t)
    (hacc : IsAcceptable width height s t) :
    HasHamPath width height s t :=
  suff_all (width + height) width height s t (Nat.le_refl _) hs ht hst hacc
end GridHam
