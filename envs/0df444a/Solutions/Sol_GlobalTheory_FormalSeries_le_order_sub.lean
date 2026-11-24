-- Prove2me | solution 1 for GlobalTheory.FormalSeries.le_order_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:27:11.947796+00:00
-- url     : https://prove2.me/submissions/cf989896-f5e4-48e2-87f6-8ede7cbc8512

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
theorem _root_.solution {k : ℕ∞} {f g : MvPowerSeries σ R} (hf : k ≤ f.order) (hg : k ≤ g.order) :
    k ≤ (f - g).order := le_order fun d hd => by
  rw [map_sub, coeff_of_lt_order (hd.trans_le hf), coeff_of_lt_order (hd.trans_le hg), sub_zero]
end GlobalTheory.FormalSeries
