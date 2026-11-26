-- Prove2me | solution 1 for O3.Experimental.pUniformConvexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:58.329179+00:00
-- url     : https://prove2.me/submissions/936e83dd-bdde-412d-be8e-c7ba1a90503f

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_Experimental_scalarUniformConvexity
import Theorems.Thm_O3_Experimental_lpNorm_rpow_eq_lpPower
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
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p : ℝ} (hp : 2 < p) {d : ℕ}
    (x y c : Point d) :
    uniformRegularizer p c y ≥
      uniformRegularizer p c x + pairing (powerDualityMap p (x - c)) (y - x) +
        (2 ^ (2 - p) / p) * (lpNorm p (y - x)) ^ p := by
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦
    scalarUniformConvexity (p := p) (x := (x - c) i) (y := (y - c) i) hp
  rw [lpNorm_rpow_eq_lpPower (by linarith : p ≠ 0)]
  simpa only [uniformRegularizer, lpPower, pairing, powerDualityMap,
    scalarEnergy, scalarJ, Pi.sub_apply, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum, div_eq_mul_inv,
    sub_sub_sub_cancel_right, mul_comm, mul_left_comm, mul_assoc,
    one_mul, mul_one, add_comm, add_left_comm, add_assoc] using hsum
end O3.Experimental
