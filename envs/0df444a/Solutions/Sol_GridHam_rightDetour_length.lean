-- Prove2me | solution 1 for GridHam.rightDetour_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:28:23.231805+00:00
-- url     : https://prove2.me/submissions/400adc33-ade8-4001-969d-e126df19d5ac

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
public import Theorems.Thm_GridHam_colSeg_length

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (w h y : ℕ) (hy : y + 1 < h) :
    (rightDetour w h y).length = 2 * h := by
  unfold rightDetour
  simp only [List.length_append, List.length_reverse, colSeg_length]
  omega
end GridHam
