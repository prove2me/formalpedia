-- Prove2me | solution 1 for GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.continuous_powForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:26.525418+00:00
-- url     : https://prove2.me/submissions/337fbab6-00f7-423d-b97c-c99279555123

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
theorem _root_.solution (k : ℕ) : Continuous (fun a : E => powForm k a) := by
  have hi : Continuous (fun a : E => innerC a) := by
    unfold innerC
    exact continuous_const.clm_comp (innerSL ℝ (E := E)).continuous
  have hf : (fun a : E => powForm k a) = fun a =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => E) (fun _ => ℂ) ℂ (fun _ => innerC a))
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ) := by
    funext a; rfl
  rw [hf]
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => E) (fun _ => ℂ) ℂ).cont.comp (continuous_pi fun _ => hi)).clm_apply
    continuous_const
end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
