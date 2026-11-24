-- Prove2me | solution 1 for GlobalTheory.Conv.mem_convLaurent_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:57.754794+00:00
-- url     : https://prove2.me/submissions/94f21f4d-df6c-49b7-8dd0-db27c883cbf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Theorems.Thm_GlobalTheory_Conv_mem_convSeries_of_summable

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
theorem _root_.solution {f : ℂ⸨X⸩} {v : ℂ} (hv : v ≠ 0)
    (h : Summable fun n : ℤ => f.coeff n * v ^ n) : f ∈ convLaurent := by
  rw [← f.single_order_mul_powerSeriesPart, summable_single_mul_coe_iff hv] at h
  obtain ⟨ε, hε, hg⟩ := mem_convSeries.1 (mem_convSeries_of_summable hv h)
  exact ⟨ε, hε, mem_puncturedRing_iff_powerSeriesPart.2 hg⟩
end GlobalTheory.Conv
