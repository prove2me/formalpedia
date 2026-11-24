-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.weightedSummable_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:12.396996+00:00
-- url     : https://prove2.me/submissions/2f1059d3-693c-4266-9446-f00a788fd852

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
theorem _root_.solution (r : ℝ) (b : ℂ) : WeightedSummable r (1 - C b * X) := by
  refine summable_of_ne_finset_zero (s := {0, 1}) fun m hm => ?_
  have h0 : m ≠ 0 := fun h => hm (by simp [h])
  have h1 : m ≠ 1 := fun h => hm (by simp [h])
  simp [coeff_one, coeff_X, h0, h1]
end GlobalTheory.CompleteHomogeneousBound
