-- Prove2me | solution 1 for O3.Stage2Closure.squaredLpEnergy_two_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:37:48.170846+00:00
-- url     : https://prove2.me/submissions/af378461-3da6-4131-9306-a2339abbf112

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2Closure_dualityMap_two
import Theorems.Thm_O3_Stage2RouteB_squaredLpEnergy_eq_quadraticRegularizer
import Theorems.Thm_O3_Stage2RouteC_lpNorm_two_sq
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
theorem _root_.solution {d : ℕ} (u v : Point d) :
    squaredLpEnergy 2 v ≤
      squaredLpEnergy 2 u + pairing (dualityMap 2 u) (v - u) +
        ((2 - 1) / 2) * (lpNorm 2 (v - u)) ^ (2 : ℕ) := by
  rw [dualityMap_two]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by norm_num : (0 : ℝ) < 2),
    squaredLpEnergy_eq_quadraticRegularizer (by norm_num : (0 : ℝ) < 2)]
  simp only [quadraticRegularizer, sub_zero]
  simp_rw [Stage2RouteC.lpNorm_two_sq]
  simp only [pairing, Pi.sub_apply]
  rw [show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num]
  have hsum : (∑ i : Fin d, v i ^ (2 : ℕ)) =
      (∑ i : Fin d, u i ^ (2 : ℕ)) +
        2 * (∑ i : Fin d, u i * (v i - u i)) +
        (∑ i : Fin d, (v i - u i) ^ (2 : ℕ)) := by
    calc
      (∑ i : Fin d, v i ^ (2 : ℕ)) =
          ∑ i : Fin d, ((u i ^ (2 : ℕ) + 2 * (u i * (v i - u i))) +
            (v i - u i) ^ (2 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  nlinarith
end O3.Stage2Closure
