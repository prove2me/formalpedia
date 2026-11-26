-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.lpNorm_two_sq_sub_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:45.623992+00:00
-- url     : https://prove2.me/submissions/fca87d06-9a1f-497e-88d7-762beef2ee57

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
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
open O3.Stage8EuclideanMinimizer
namespace O3.Stage8EuclideanMinimizer
theorem _root_.solution {d : ℕ} (x z x₀ : Point d) :
    (lpNorm 2 (x - x₀)) ^ (2 : ℕ) =
      (lpNorm 2 (z - x₀)) ^ (2 : ℕ) +
        2 * pairing (z - x₀) (x - z) +
        (lpNorm 2 (x - z)) ^ (2 : ℕ) := by
  simp_rw [Stage2RouteC.lpNorm_two_sq]
  simp only [pairing, Pi.sub_apply]
  calc
    (∑ i, (x i - x₀ i) ^ (2 : ℕ)) =
        ∑ i, ((z i - x₀ i) ^ (2 : ℕ) +
          2 * ((z i - x₀ i) * (x i - z i)) +
          (x i - z i) ^ (2 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (z i - x₀ i) ^ (2 : ℕ)) +
          (∑ i, 2 * ((z i - x₀ i) * (x i - z i))) +
          ∑ i, (x i - z i) ^ (2 : ℕ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by rw [Finset.mul_sum]
end O3.Stage8EuclideanMinimizer
