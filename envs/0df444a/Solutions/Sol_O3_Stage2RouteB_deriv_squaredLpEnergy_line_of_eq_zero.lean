-- Prove2me | solution 1 for O3.Stage2RouteB.deriv_squaredLpEnergy_line_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:46.809863+00:00
-- url     : https://prove2.me/submissions/08e65d10-e745-499b-9a9a-0e6f608ee435

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteB_squaredLpEnergy_scalar_mul
import Theorems.Thm_O3_lpNorm_neg
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
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) (hxt : (fun i ↦ x i + t * h i) = 0) :
    deriv (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) t =
      pairing (dualityMap p (fun i ↦ x i + t * h i)) h := by
  have hxcoord : ∀ i, x i = -t * h i := by
    intro i
    have hi := congrFun hxt i
    simp only [Pi.zero_apply] at hi
    linarith
  have hfun : (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) =
      fun s : ℝ ↦ (s - t) ^ (2 : ℕ) * squaredLpEnergy p h := by
    funext s
    rw [show (fun i ↦ x i + s * h i) = (fun i ↦ (s - t) * h i) by
      funext i
      rw [hxcoord i]
      ring]
    exact squaredLpEnergy_scalar_mul (by linarith : 0 < p) h
  rw [hfun]
  have hd := (((hasDerivAt_id t).sub_const t).pow 2).mul_const (squaredLpEnergy p h)
  rw [hxt, dualityMap_zero (by linarith : 0 < p)]
  simp only [pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  simpa using hd.deriv
end O3.Stage2RouteB
