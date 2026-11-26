-- Prove2me | solution 1 for O3.Stage2Closure.hasDerivAt_squaredLpEnergy_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:36:56.65479+00:00
-- url     : https://prove2.me/submissions/dcd498ce-f0ae-4ba6-a050-38400165a665

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_lineEnergy_of_ne_zero
import Theorems.Thm_O3_Stage2RouteB_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteB_squaredLpEnergy_scalar_mul
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
theorem _root_.solution {q : ℝ} (hq : 1 < q) {d : ℕ}
    (u h : Point d) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ squaredLpEnergy q (u + s • h))
      (pairing (dualityMap q (u + t • h)) h) t := by
  by_cases hz : u + t • h = 0
  · have hcoord : ∀ i, u i = -t * h i := by
      intro i
      have hi := congrFun hz i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      linarith
    have hfun : (fun s : ℝ ↦ squaredLpEnergy q (u + s • h)) =
        fun s : ℝ ↦ (s - t) ^ (2 : ℕ) * squaredLpEnergy q h := by
      funext s
      rw [show u + s • h = (fun i ↦ (s - t) * h i) by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hcoord i]
        ring]
      exact squaredLpEnergy_scalar_mul (by linarith : 0 < q) h
    rw [hfun]
    have hd := (((hasDerivAt_id t).sub_const t).pow 2).mul_const
      (squaredLpEnergy q h)
    rw [hz, Stage2RouteB.dualityMap_zero (by linarith : 0 < q)]
    simpa [pairing] using hd
  · change HasDerivAt (Stage2RouteA.lineEnergy q u h)
      (pairing (dualityMap q (u + t • h)) h) t
    exact Stage2RouteA.hasDerivAt_lineEnergy_of_ne_zero hq u h t hz
end O3.Stage2Closure
