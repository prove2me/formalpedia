-- Prove2me | solution 1 for GlobalTheory.BoundedPowerSeriesDisc.tsum_coeff_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:44.033928+00:00
-- url     : https://prove2.me/submissions/64fda5c4-c90d-4aae-a8e6-b586e80feee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BoundedPowerSeriesDisc
open PowerSeries
variable {K : Type*} [NormedField K]
namespace GlobalTheory.BoundedPowerSeriesDisc
theorem _root_.solution (t : K) : ∑' n, coeff n (X : K⟦X⟧) * t ^ n = t := by
  rw [tsum_eq_single 1]
  · simp
  · intro n hn
    simp [coeff_X, hn]
end GlobalTheory.BoundedPowerSeriesDisc
