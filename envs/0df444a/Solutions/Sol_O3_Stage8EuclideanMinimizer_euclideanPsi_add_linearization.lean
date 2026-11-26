-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.euclideanPsi_add_linearization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:34.433313+00:00
-- url     : https://prove2.me/submissions/607f55bd-6ab0-4a72-9d36-7c6187603aab

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
import Theorems.Thm_O3_Stage8EuclideanMinimizer_pairing_sub_decomposition
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
theorem _root_.solution {M a fy : ℝ} {d : ℕ}
    (x₀ s g y : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c x + a * (fy + pairing g (x - y)) =
      euclideanPsi M x₀ (s + a • g)
        (c + a * (fy + pairing g (x₀ - y))) x := by
  unfold euclideanPsi
  simp only [Stage2RouteD.pairing_add_left, Stage2RouteD.pairing_smul_left]
  have hsplit : pairing g (x - y) =
      pairing g (x₀ - y) + pairing g (x - x₀) := by
    exact pairing_sub_decomposition g x x₀ y
  rw [hsplit]
  ring
end O3.Stage8EuclideanMinimizer
