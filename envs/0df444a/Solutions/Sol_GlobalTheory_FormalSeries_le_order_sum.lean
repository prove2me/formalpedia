-- Prove2me | solution 1 for GlobalTheory.FormalSeries.le_order_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:27:00.111207+00:00
-- url     : https://prove2.me/submissions/8d8ec021-f528-4e45-b252-ce2ce8bbde01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution {ι : Type*} {k : ℕ∞} (s : Finset ι) {f : ι → MvPowerSeries σ R}
    (hf : ∀ i ∈ s, k ≤ (f i).order) : k ≤ (∑ i ∈ s, f i).order := le_order fun d hd => by
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => coeff_of_lt_order (hd.trans_le (hf i hi))
end GlobalTheory.FormalSeries
