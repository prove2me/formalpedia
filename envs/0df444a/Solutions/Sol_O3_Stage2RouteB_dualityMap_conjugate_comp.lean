-- Prove2me | solution 1 for O3.Stage2RouteB.dualityMap_conjugate_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:41.541062+00:00
-- url     : https://prove2.me/submissions/7bbd6c33-408f-41a8-8b5c-fc782865d926

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteB_lpNorm_dualityMap
import Theorems.Thm_O3_Stage2RouteB_outer_comp_exponent
import Theorems.Thm_O3_Stage2RouteB_powerDuality_coordinate_comp
import Theorems.Thm_O3_Stage2RouteB_powerDuality_coordinate_scale
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_one_lt_conjugateExponent
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
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    dualityMap (conjugateExponent p) (dualityMap p x) = x := by
  by_cases hx : x = 0
  · subst x
    rw [dualityMap_zero (by linarith : 0 < p)]
    exact dualityMap_zero (lt_trans zero_lt_one (one_lt_conjugateExponent hp))
  · have hn : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
    have hJuNorm := lpNorm_dualityMap hp x
    have hJu : dualityMap p x ≠ 0 := by
      intro hzero
      have := congrArg (lpNorm (conjugateExponent p)) hzero
      rw [hJuNorm, lpNorm_zero (lt_trans zero_lt_one (one_lt_conjugateExponent hp))] at this
      exact hn.ne' this
    rw [dualityMap, if_neg (lpNorm_pos_of_ne_zero hJu).ne']
    funext i
    rw [hJuNorm]
    rw [dualityMap, if_neg hn.ne']
    let c : ℝ := lpNorm p x ^ (2 - p)
    let b : ℝ := |x i| ^ (p - 2) * x i
    have hc : 0 < c := Real.rpow_pos_of_pos hn _
    change lpNorm p x ^ (2 - conjugateExponent p) *
        (|c * b| ^ (conjugateExponent p - 2) * (c * b)) = x i
    rw [powerDuality_coordinate_scale hc]
    rw [powerDuality_coordinate_comp hp]
    dsimp only [c]
    rw [← mul_assoc]
    rw [← Real.rpow_mul hn.le]
    rw [← Real.rpow_add hn]
    rw [outer_comp_exponent hp, Real.rpow_zero, one_mul]
end O3.Stage2RouteB
