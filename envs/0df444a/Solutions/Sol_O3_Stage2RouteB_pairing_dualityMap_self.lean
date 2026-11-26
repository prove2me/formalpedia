-- Prove2me | solution 1 for O3.Stage2RouteB.pairing_dualityMap_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:55.092251+00:00
-- url     : https://prove2.me/submissions/36905595-077c-48a1-9bd6-35e5d4c8c5ce

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_lpNorm_rpow_eq_lpPower
import Theorems.Thm_O3_Stage2RouteB_pairing_powerDualityMap_self
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
    pairing (dualityMap p x) x = (lpNorm p x) ^ (2 : ℕ) := by
  by_cases hx : x = 0
  · subst x
    simp [dualityMap, lpNorm_zero (by linarith : 0 < p), pairing]
  · have hnpos : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
    have hnpow := lpNorm_rpow_eq_lpPower (p := p) (by linarith : p ≠ 0) x
    rw [dualityMap, if_neg hnpos.ne']
    simp only [pairing]
    rw [show (∑ i, lpNorm p x ^ (2 - p) * (|x i| ^ (p - 2) * x i) * x i) =
        lpNorm p x ^ (2 - p) * (∑ i, |x i| ^ (p - 2) * x i * x i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    rw [show (∑ i, |x i| ^ (p - 2) * x i * x i) = lpPower p x by
      simpa only [pairing, powerDualityMap] using pairing_powerDualityMap_self hp x]
    calc
      lpNorm p x ^ (2 - p) * lpPower p x =
          lpNorm p x ^ (2 - p) * lpNorm p x ^ p := by rw [hnpow]
      _ = lpNorm p x ^ ((2 - p) + p) := (Real.rpow_add hnpos _ _).symm
      _ = lpNorm p x ^ (2 : ℝ) := by ring_nf
      _ = lpNorm p x ^ (2 : ℕ) := by rw [Real.rpow_two]
end O3.Stage2RouteB
