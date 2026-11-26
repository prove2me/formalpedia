-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.pairing_sub_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:44.833792+00:00
-- url     : https://prove2.me/submissions/7486ab62-50a7-406e-a2b4-717ff08652d6

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
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
theorem _root_.solution {d : ℕ} (s x z x₀ : Point d) :
    pairing s (x - x₀) = pairing s (z - x₀) + pairing s (x - z) := by
  simp only [pairing, Pi.sub_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring
end O3.Stage8EuclideanMinimizer
