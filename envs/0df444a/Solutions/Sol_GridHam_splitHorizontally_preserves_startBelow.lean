-- Prove2me | solution 1 for GridHam.splitHorizontally_preserves_startBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:55.639735+00:00
-- url     : https://prove2.me/submissions/83878938-9a46-4aee-87c7-9b27bbf41541

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_splitVertically_preserves_startLeft
public import Theorems.Thm_GridHam_hasHamPath_transpose

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution
    (width height cut cutCol : ℕ) (s t : Coord)
    (hstartBelow : s.2 < t.2)
    (hcutRange : s.2 ≤ cut) (hcutRange' : cut < t.2)
    (hcutCol : cutCol < width)
    (hlower : HasHamPath width (cut + 1) s (cutCol, cut))
    (hupper : HasHamPath width (height - (cut + 1)) (cutCol, 0)
      (t.1, t.2 - (cut + 1))) :
    HasHamPath width height s t := by
  have hl : HasHamPath (cut + 1) width (swapXY s) (cut, cutCol) :=
    hasHamPath_transpose hlower
  have hu : HasHamPath (height - (cut + 1)) width (0, cutCol)
      ((swapXY t).1 - (cut + 1), (swapXY t).2) :=
    hasHamPath_transpose hupper
  have hT : HasHamPath height width (swapXY s) (swapXY t) :=
    splitVertically_preserves_startLeft height width cut cutCol (swapXY s) (swapXY t)
      hstartBelow hcutRange hcutRange' hcutCol hl hu
  exact hasHamPath_transpose hT
end GridHam
