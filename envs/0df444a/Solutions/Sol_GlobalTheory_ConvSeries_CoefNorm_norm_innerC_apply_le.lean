-- Prove2me | solution 1 for GlobalTheory.ConvSeries.CoefNorm.norm_innerC_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:24.072228+00:00
-- url     : https://prove2.me/submissions/71fef9cf-ed6d-47d0-b8ef-4844f47fc85e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ConvSeries
open GlobalTheory.ConvSeries.CoefNorm
namespace GlobalTheory.ConvSeries.CoefNorm
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a y : E) :
    ‖innerC a y‖ ≤ ‖a‖ * ‖y‖ := by
  simp only [innerC, ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_real_inner_le_norm a y
end GlobalTheory.ConvSeries.CoefNorm
