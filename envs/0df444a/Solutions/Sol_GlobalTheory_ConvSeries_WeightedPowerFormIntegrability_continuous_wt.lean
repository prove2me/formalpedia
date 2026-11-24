-- Prove2me | solution 1 for GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.continuous_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:44:32.436031+00:00
-- url     : https://prove2.me/submissions/c2e4635a-3b69-4d5e-b23a-8c1660453d2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ConvSeries GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
open GlobalTheory.ConvSeries
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
theorem _root_.solution (b c : ℝ) (h : SchwartzMap E ℂ) : Continuous (wt b c h) := by
  have hc : Continuous (h : E → ℂ) := h.continuous
  unfold wt
  fun_prop
end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
