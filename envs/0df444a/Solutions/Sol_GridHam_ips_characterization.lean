-- Prove2me | solution 1 for GridHam.ips_characterization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:59:29.603336+00:00
-- url     : https://prove2.me/submissions/e6f99cd5-2d54-46fd-8a11-5746057480d3

module
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_Reduction
public import Definitions.Def_GridHam_Necessity
public import Definitions.Def_GridHam_Main
public import Theorems.Thm_GridHam_ips_sufficiency
public import Theorems.Thm_GridHam_hamPath_implies_acceptable


set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (width height : ℕ) (s t : Coord)
    (hs : InBounds width height s) (ht : InBounds width height t)
    (hst : s ≠ t) :
    HasHamPath width height s t ↔ IsAcceptable width height s t :=
  ⟨hamPath_implies_acceptable width height s t hs ht,
   ips_sufficiency width height s t hs ht hst⟩
end GridHam
