-- Prove2me | solution 1 for GlobalTheory.CompleteHomogeneousBound.weightedSummable_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:16:55.574808+00:00
-- url     : https://prove2.me/submissions/f1f0eda6-5ee2-4a56-bbdd-9e1e754ecc7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_WeightedSummable_mul
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_weightedSummable_one

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
theorem _root_.solution {ι : Type*} (r : ℝ) (s : Finset ι) (f : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, WeightedSummable r (f i)) : WeightedSummable r (∏ i ∈ s, f i) :=
  Finset.prod_induction f (WeightedSummable r) (fun _ _ ha hb => ha.mul hb)
    (weightedSummable_one r) h
end GlobalTheory.CompleteHomogeneousBound
