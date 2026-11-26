-- Prove2me | solution 1 for O3.Stage2RouteB.lpPower_dualityMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:26.442537+00:00
-- url     : https://prove2.me/submissions/abc23103-8afa-4539-a525-0759a60e52b7

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_lpNorm_rpow_eq_lpPower
import Theorems.Thm_O3_Stage2RouteB_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteB_mul_conjugateExponent_sub_one
import Theorems.Thm_O3_Stage2RouteB_conjugateExponent_ne_zero
import Theorems.Thm_O3_Stage2RouteB_exponent_balance
import Theorems.Thm_O3_Stage2RouteB_abs_dualityMap_coordinate
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
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    lpPower (conjugateExponent p) (dualityMap p x) =
      (lpNorm p x) ^ (conjugateExponent p) := by
  by_cases hx : x = 0
  · subst x
    rw [dualityMap_zero (by linarith : 0 < p)]
    rw [lpPower_zero (conjugateExponent_ne_zero hp)]
    rw [lpNorm_zero (by linarith : 0 < p)]
    exact (Real.zero_rpow (conjugateExponent_ne_zero hp)).symm
  · have hn : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
    have hnp := lpNorm_rpow_eq_lpPower (p := p) (by linarith : p ≠ 0) x
    simp only [lpPower]
    rw [show (∑ i, |dualityMap p x i| ^ conjugateExponent p) =
        lpNorm p x ^ ((2 - p) * conjugateExponent p) *
          (∑ i, |x i| ^ p) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_dualityMap_coordinate hp hx]
      rw [Real.mul_rpow (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg (abs_nonneg _) _)]
      rw [← Real.rpow_mul hn.le]
      rw [← Real.rpow_mul (abs_nonneg (x i))]
      congr 1
      rw [mul_conjugateExponent_sub_one hp]]
    change lpNorm p x ^ ((2 - p) * conjugateExponent p) * lpPower p x = _
    rw [← hnp, ← Real.rpow_add hn]
    rw [exponent_balance hp]
end O3.Stage2RouteB
