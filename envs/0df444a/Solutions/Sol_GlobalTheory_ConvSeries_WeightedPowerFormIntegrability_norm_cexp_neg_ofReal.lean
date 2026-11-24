-- Prove2me | solution 1 for GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.norm_cexp_neg_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:27.605097+00:00
-- url     : https://prove2.me/submissions/8652f49a-4bbc-4559-b342-253aa38ee809

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
theorem _root_.solution (x : ℝ) : ‖Complex.exp (-((x : ℝ) : ℂ))‖ = Real.exp (-x) := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
