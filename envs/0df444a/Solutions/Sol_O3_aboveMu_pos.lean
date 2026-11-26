-- Prove2me | solution 1 for O3.aboveMu_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:31.420832+00:00
-- url     : https://prove2.me/submissions/43c52cec-c172-4870-bf09-52e66a6ca3c0

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveEta_pos

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p eps D : ℝ}
    (_hp : AboveTwoRegime p) (heps : 0 < eps) (hD : 0 < D) :
    0 < aboveMu p eps D := by
  exact div_pos (mul_pos (aboveEta_pos p) heps)
    (Real.rpow_pos_of_pos hD _)
end O3
