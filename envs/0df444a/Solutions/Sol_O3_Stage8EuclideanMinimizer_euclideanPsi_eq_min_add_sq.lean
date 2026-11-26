-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.euclideanPsi_eq_min_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:25.879623+00:00
-- url     : https://prove2.me/submissions/fb249fea-f377-49ca-a02c-5233ed7dbecf

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
import Theorems.Thm_O3_Stage8EuclideanMinimizer_lpNorm_two_sq_sub_decomposition
import Theorems.Thm_O3_Stage8EuclideanMinimizer_pairing_sub_decomposition
import Theorems.Thm_O3_Stage8EuclideanMinimizer_euclideanPsiMinimizer_pairing_cancel
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
theorem _root_.solution {M : ℝ} (hM : M ≠ 0) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c x =
      euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) +
        M / 2 *
          (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) := by
  let z := euclideanPsiMinimizer M x₀ s
  have hsq := lpNorm_two_sq_sub_decomposition x z x₀
  have hlin := pairing_sub_decomposition s x z x₀
  have hcancel := euclideanPsiMinimizer_pairing_cancel hM x₀ s x
  have hcancelz :
      M * pairing (z - x₀) (x - z) + pairing s (x - z) = 0 := by
    simpa only [z] using hcancel
  change M / 2 * lpNorm 2 (x - x₀) ^ (2 : ℕ) + c + pairing s (x - x₀) =
    (M / 2 * lpNorm 2 (z - x₀) ^ (2 : ℕ) + c + pairing s (z - x₀)) +
      M / 2 * lpNorm 2 (x - z) ^ (2 : ℕ)
  rw [hsq, hlin]
  linear_combination hcancelz
end O3.Stage8EuclideanMinimizer
