-- Prove2me | solution 1 for O3.Stage2Closure.squaredLpEnergy_smooth_above_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:30.78993+00:00
-- url     : https://prove2.me/submissions/59de929e-2cef-4fd2-bc79-56d3f2e4e1a5

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2Closure_hasDerivAt_smoothRemainder
import Theorems.Thm_O3_Stage2Closure_smoothRemainder_concave_above_two
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3
open O3.Stage2Closure
open scoped BigOperators
open Stage2RouteA Stage2RouteB
namespace O3.Stage2Closure
theorem _root_.solution {q : ℝ} (hq : 2 < q) {d : ℕ}
    (u v : Point d) :
    squaredLpEnergy q v ≤ squaredLpEnergy q u +
      pairing (dualityMap q u) (v - u) +
        ((q - 1) / 2) * (lpNorm q (v - u)) ^ (2 : ℕ) := by
  let h : Point d := v - u
  have huv : u + h = v := by
    funext i
    simp only [h, Pi.add_apply, Pi.sub_apply]
    ring
  have hconc := smoothRemainder_concave_above_two hq u h
  have htangent := hconc.slope_le_of_hasDerivAt
    (x := (0 : ℝ)) (y := (1 : ℝ)) (by simp) (by simp) (by norm_num)
    (hasDerivAt_smoothRemainder (by linarith : 1 < q) u h 0)
  norm_num [slope, smoothRemainder, smoothRemainderDeriv] at htangent
  rw [huv] at htangent
  change squaredLpEnergy q v ≤ squaredLpEnergy q u +
    pairing (dualityMap q u) h +
      ((q - 1) / 2) * (lpNorm q h) ^ (2 : ℕ)
  nlinarith
end O3.Stage2Closure
