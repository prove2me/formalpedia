-- Prove2me | solution 1 for O3.aboveTheta_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:58.496258+00:00
-- url     : https://prove2.me/submissions/57d48970-5381-4756-b522-2737cd462ec0

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveAP_pos
import Theorems.Thm_O3_aboveEta_pos

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : AboveTwoRegime p) :
    0 < aboveTheta p := by
  exact mul_pos (aboveAP_pos hp) (aboveEta_pos p)
end O3
