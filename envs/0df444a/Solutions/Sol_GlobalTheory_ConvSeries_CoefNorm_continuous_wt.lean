-- Prove2me | solution 1 for GlobalTheory.ConvSeries.CoefNorm.continuous_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:22.714467+00:00
-- url     : https://prove2.me/submissions/c676e4c9-de14-4abc-99c2-a23f20aff4af

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
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ)
    (hh : Continuous h) : Continuous (wt b c h) := by
  unfold wt
  fun_prop
end GlobalTheory.ConvSeries.CoefNorm
