-- Prove2me | solution 1 for GlobalTheory.RowFubini.measure_pos_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:15.76383+00:00
-- url     : https://prove2.me/submissions/d8165dc5-645c-4453-bcc2-644696991299

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
namespace GlobalTheory.RowFubini
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (hc : IsCompact (H : Set G)) : 0 < μ H ∧ μ H < ∞ :=
  ⟨hH.measure_pos μ ⟨1, H.one_mem⟩, hc.measure_lt_top⟩
end GlobalTheory.RowFubini
