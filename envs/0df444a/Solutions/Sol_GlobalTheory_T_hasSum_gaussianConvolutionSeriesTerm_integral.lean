-- Prove2me | solution 1 for GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:29.706797+00:00
-- url     : https://prove2.me/submissions/0ad66335-426a-4855-bb99-a2214b8db74e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegralStatement
import Theorems.Thm_GlobalTheory_ConvSeries_hasSum_term_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ) (y : E),
    HasSum (fun k => GlobalTheory.ConvSeries.term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.ConvSeries.hasSum_term_integral | exact GlobalTheory.ConvSeries.hasSum_term_integral | (intros; apply GlobalTheory.ConvSeries.hasSum_term_integral <;> assumption)
end _root_.GlobalTheory.T
