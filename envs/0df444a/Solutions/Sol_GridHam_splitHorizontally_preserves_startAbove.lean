-- Prove2me | solution 1 for GridHam.splitHorizontally_preserves_startAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:45:01.878223+00:00
-- url     : https://prove2.me/submissions/afe5bc2b-60a2-4234-a65c-b7ac0de0cf75

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_hasHamPath_reverse
public import Theorems.Thm_GridHam_splitHorizontally_preserves_startBelow

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution
    (width height cut cutCol : ℕ) (s t : Coord)
    (hstartAbove : t.2 < s.2)
    (hcutRange : t.2 ≤ cut) (hcutRange' : cut < s.2)
    (hcutCol : cutCol < width)
    (hlower : HasHamPath width (cut + 1) t (cutCol, cut))
    (hupper : HasHamPath width (height - (cut + 1)) (cutCol, 0)
      (s.1, s.2 - (cut + 1))) :
    HasHamPath width height s t :=
  hasHamPath_reverse (splitHorizontally_preserves_startBelow width height cut cutCol t s
    hstartAbove hcutRange hcutRange' hcutCol hlower hupper)
end GridHam
