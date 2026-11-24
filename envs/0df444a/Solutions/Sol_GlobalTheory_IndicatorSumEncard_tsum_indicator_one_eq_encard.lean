-- Prove2me | solution 1 for GlobalTheory.IndicatorSumEncard.tsum_indicator_one_eq_encard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:44.958328+00:00
-- url     : https://prove2.me/submissions/ae5e2f74-eae5-4808-ad63-02f7430237cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SetLIntegralLeMulOfEncardLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IndicatorSumEncard
namespace GlobalTheory.IndicatorSumEncard
theorem _root_.solution {ι : Type} (A : Set ι) :
    ∑' i : ι, A.indicator (fun _ => (1 : ENNReal)) i = (A.encard : ENNReal) := by
  rw [← tsum_subtype A (fun _ => (1 : ENNReal))]
  exact ENNReal.tsum_set_one A
end GlobalTheory.IndicatorSumEncard
