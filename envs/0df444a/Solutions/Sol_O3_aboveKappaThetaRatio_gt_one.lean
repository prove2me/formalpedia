-- Prove2me | solution 1 for O3.aboveKappaThetaRatio_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:02.702589+00:00
-- url     : https://prove2.me/submissions/45b0065c-c208-4b2e-9527-385d7b170bbe

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveTheta_pos
import Theorems.Thm_O3_aboveTheta_lt_one

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p kappa : ℝ}
    (hp : AboveTwoRegime p) (hkappa : 1 < kappa) :
    1 < 8 * kappa ^ 2 / (aboveTheta p) ^ 2 := by
  have htheta : 0 < aboveTheta p := aboveTheta_pos hp
  have htheta1 : aboveTheta p < 1 := aboveTheta_lt_one hp
  have htheta_sq : (aboveTheta p) ^ 2 < 1 := by nlinarith [sq_nonneg (aboveTheta p)]
  have hkappa_sq : 1 < kappa ^ 2 := by nlinarith [sq_nonneg kappa]
  rw [lt_div_iff₀ (sq_pos_of_pos htheta)]
  nlinarith
end O3
