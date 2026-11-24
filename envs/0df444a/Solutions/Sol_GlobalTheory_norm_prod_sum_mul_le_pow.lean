-- Prove2me | solution 1 for GlobalTheory.norm_prod_sum_mul_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:17.516389+00:00
-- url     : https://prove2.me/submissions/3c1a3cf4-e4c1-410e-b062-ad5fa4dadadf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NormProdSumThetaLeExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {N M : ℕ} (c z : Fin N → Fin M → ℂ) {C B : ℝ}
    (hC : 0 ≤ C) (hc : ∀ k t, ‖c k t‖ ≤ C) (hz : ∀ k t, ‖z k t‖ ≤ B) :
    ‖∏ k, ∑ t, c k t * z k t‖ ≤ (M * (C * B)) ^ N := by
  rw [norm_prod]
  calc ∏ k, ‖∑ t, c k t * z k t‖ ≤ ∏ _k : Fin N, (M * (C * B) : ℝ) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
        calc ‖∑ t, c k t * z k t‖ ≤ ∑ t, ‖c k t * z k t‖ := norm_sum_le _ _
          _ ≤ ∑ _t : Fin M, C * B := Finset.sum_le_sum fun t _ => by
              rw [norm_mul]
              exact mul_le_mul (hc k t) (hz k t) (norm_nonneg _) hC
          _ = M * (C * B) := by simp
    _ = _ := by simp
end GlobalTheory
