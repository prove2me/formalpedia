-- Prove2me | solution 1 for O3.Stage2RouteD.pairing_dualityMap_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:07.984249+00:00
-- url     : https://prove2.me/submissions/2c9eabfa-4aac-40b8-8db1-e6359b351c60

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_scalar_powerDuality_self
import Theorems.Thm_O3_Stage2RouteD_lpNorm_rpow_p
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_dualityMap_of_ne
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.Stage2RouteD.dualityMap_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ} (u : Point d) :
    pairing (dualityMap p u) u = (lpNorm p u) ^ (2 : ℕ) := by
  by_cases hu : u = 0
  · subst u
    simp [dualityMap_zero (by linarith : 0 < p), lpNorm_zero (by linarith : 0 < p), pairing]
  · rw [dualityMap_of_ne (by linarith : 0 < p) hu]
    unfold pairing
    simp only
    simp only [mul_assoc]
    change (∑ i, (lpNorm p u) ^ (2 - p) *
      (|u i| ^ (p - 2) * (u i * u i))) = (lpNorm p u) ^ (2 : ℕ)
    rw [← Finset.mul_sum]
    rw [show (∑ i, |u i| ^ (p - 2) * (u i * u i)) = lpPower p u by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [mul_assoc] using scalar_powerDuality_self (p := p) (u := u i) hp]
    rw [← lpNorm_rpow_p hp u]
    have hnorm : 0 < lpNorm p u := lpNorm_pos_of_ne_zero hu
    rw [← Real.rpow_add hnorm]
    norm_num
end O3.Stage2RouteD
