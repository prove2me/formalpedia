-- Prove2me | solution 1 for GlobalTheory.Conv.mem_convSeries_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:00:09.940804+00:00
-- url     : https://prove2.me/submissions/761d7907-99c3-4676-b216-2c816d07fa1a

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
theorem _root_.solution {f : ℂ⟦X⟧} {u : ℂ} (hu : u ≠ 0)
    (h : Summable fun n => PowerSeries.coeff n f * u ^ n) : f ∈ convSeries := by
  refine mem_convSeries.2 ⟨‖u‖, norm_pos_iff.2 hu, fun v hv => ?_⟩
  refine Summable.of_norm_bounded (summable_norm_iff.2 h) fun n => ?_
  simp only [norm_mul, norm_pow]
  gcongr
end GlobalTheory.Conv
