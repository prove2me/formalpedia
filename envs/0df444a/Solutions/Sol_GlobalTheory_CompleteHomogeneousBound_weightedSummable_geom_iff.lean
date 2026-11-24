-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.weightedSummable_geom_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:56.633396+00:00
-- url     : https://prove2.me/submissions/ee6d0cf9-b168-4738-b52d-a7bee718b361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
open GlobalTheory GlobalTheory.CompleteHomogeneousBound
namespace GlobalTheory.CompleteHomogeneousBound
theorem _root_.solution (r : ℝ) (b : ℂ) :
    WeightedSummable r (mk fun m => b ^ m) ↔ ‖b * r‖ < 1 := by
  unfold WeightedSummable
  simp only [coeff_mk, ← mul_pow, norm_pow]
  rw [summable_geometric_iff_norm_lt_one, norm_norm]
end GlobalTheory.CompleteHomogeneousBound
