-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer_pairing_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:54.52078+00:00
-- url     : https://prove2.me/submissions/3c99705d-00a0-4286-830d-40a4b32a7157

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
import Theorems.Thm_O3_Stage8EuclideanMinimizer_euclideanPsiMinimizer_firstOrder
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_pairing_add_left
import Theorems.Thm_O3_Stage2RouteD_pairing_smul_left
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
theorem _root_.solution {M : ℝ} (hM : M ≠ 0)
    {d : ℕ} (x₀ s x : Point d) :
    M * pairing (euclideanPsiMinimizer M x₀ s - x₀)
        (x - euclideanPsiMinimizer M x₀ s) +
      pairing s (x - euclideanPsiMinimizer M x₀ s) = 0 := by
  rw [← Stage2RouteD.pairing_smul_left, ← Stage2RouteD.pairing_add_left]
  rw [euclideanPsiMinimizer_firstOrder hM]
  simp [pairing]
end O3.Stage8EuclideanMinimizer
