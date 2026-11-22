-- Prove2me | solution 1 for GridHam.splitVertically_preserves_startRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:44:57.781835+00:00
-- url     : https://prove2.me/submissions/598cd8b6-d150-43a0-a5ad-5caf597da7a5

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_splitVertically_preserves_startLeft
public import Theorems.Thm_GridHam_hasHamPath_reverse

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution
    (width height cut cutRow : ℕ) (s t : Coord)
    (hstartRight : t.1 < s.1)
    (hcutRange : t.1 ≤ cut) (hcutRange' : cut < s.1)
    (hcutRow : cutRow < height)
    (hleft : HasHamPath (cut + 1) height (cut, cutRow) t)
    (hright : HasHamPath (width - (cut + 1)) height (0, cutRow)
      (s.1 - (cut + 1), s.2)) :
    HasHamPath width height s t :=
  hasHamPath_reverse (splitVertically_preserves_startLeft width height cut cutRow t s
    hstartRight hcutRange hcutRange' hcutRow (hasHamPath_reverse hleft) hright)
end GridHam
