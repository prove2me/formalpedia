-- Prove2me | solution 1 for GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:43.687983+00:00
-- url     : https://prove2.me/submissions/84c23063-aa38-496e-8242-b4b289b1fa56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegr
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegrStatement
import Theorems.Thm_GlobalTheory_ConvSeries_norm_coef_le_integral


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
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 ≤ b → 0 ≤ c → ∀ (h : SchwartzMap E ℂ) (j : ℕ),
    ‖GlobalTheory.ConvSeries.coef b c (⇑h) j‖ ≤ ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  first | exact @GlobalTheory.ConvSeries.norm_coef_le_integral | exact GlobalTheory.ConvSeries.norm_coef_le_integral | (intros; apply GlobalTheory.ConvSeries.norm_coef_le_integral <;> assumption)
end _root_.GlobalTheory.T
