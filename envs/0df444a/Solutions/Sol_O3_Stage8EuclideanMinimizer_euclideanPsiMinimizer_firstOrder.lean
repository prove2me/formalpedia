-- Prove2me | solution 1 for O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer_firstOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:46.29909+00:00
-- url     : https://prove2.me/submissions/b513eefd-c862-4ea6-97ad-8bb0038f149c

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
theorem _root_.solution {M : ℝ} (hM : M ≠ 0) {d : ℕ}
    (x₀ s : Point d) :
    M • (euclideanPsiMinimizer M x₀ s - x₀) + s = 0 := by
  funext i
  simp only [euclideanPsiMinimizer, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply]
  field_simp [hM]
  ring
end O3.Stage8EuclideanMinimizer
