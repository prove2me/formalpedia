-- Prove2me | solution 1 for GlobalTheory.Conv.eventually_lsum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:17.834626+00:00
-- url     : https://prove2.me/submissions/2dd4cd70-4c7a-4058-b6e7-177f1ad627c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv
namespace GlobalTheory.Conv
theorem _root_.solution {f : ℂ⸨X⸩} (hf : f ∈ convLaurent) (h0 : f ≠ 0) :
    ∀ᶠ v in 𝓝[≠] (0 : ℂ), lsum f v ≠ 0 := by
  obtain ⟨ε, hε, hf⟩ := hf
  exact not_frequently.1 fun h => h0 (eq_zero_of_frequently_lsum_eq_zero hε hf h)
end GlobalTheory.Conv
