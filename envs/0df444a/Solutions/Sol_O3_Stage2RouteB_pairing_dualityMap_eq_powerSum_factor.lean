-- Prove2me | solution 1 for O3.Stage2RouteB.pairing_dualityMap_eq_powerSum_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:04.590796+00:00
-- url     : https://prove2.me/submissions/47af3b32-9583-408b-8e09-581df7b7a79d

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_powerSum_factor_eq_norm_factor
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



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 0 < p) {d : ℕ}
    {z : Point d} (hz : z ≠ 0) (h : Point d) :
    pairing (dualityMap p z) h =
      (lpPower p z) ^ (2 / p - 1) * pairing (powerDualityMap p z) h := by
  have hn : 0 < lpNorm p z := lpNorm_pos_of_ne_zero hz
  rw [dualityMap, if_neg hn.ne']
  simp only [pairing, powerDualityMap]
  rw [show (∑ i, lpNorm p z ^ (2 - p) * (|z i| ^ (p - 2) * z i) * h i) =
      lpNorm p z ^ (2 - p) * (∑ i, |z i| ^ (p - 2) * z i * h i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [powerSum_factor_eq_norm_factor hp hz]
end O3.Stage2RouteB
