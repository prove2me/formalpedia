-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.weightedSummable_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:13.389193+00:00
-- url     : https://prove2.me/submissions/8a989861-eef1-41aa-aed9-c7660469fc0f

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
theorem _root_.solution (r : ℝ) : WeightedSummable r 1 := by
  refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
  have : m ≠ 0 := by simpa using hm
  simp [coeff_one, this]
end GlobalTheory.CompleteHomogeneousBound
