-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.WeightedSummable.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:31.77194+00:00
-- url     : https://prove2.me/submissions/b4a42518-3b90-4d26-a568-ee844b70fc01

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
namespace WeightedSummable
theorem _root_.solution {r : ℝ} {f g : ℂ⟦X⟧} (hf : WeightedSummable r f)
    (hg : WeightedSummable r g) : WeightedSummable r (f * g) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  refine h.congr fun m => ?_
  rw [coeff_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpm : p.1 + p.2 = m := by simpa using hp
  rw [← hpm, pow_add]
  ring
end WeightedSummable
end GlobalTheory.CompleteHomogeneousBound
