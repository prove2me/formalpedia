-- Prove2me | solution 1 for GlobalTheory.RealWeil.continuous_fourier_gau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:50:05.361797+00:00
-- url     : https://prove2.me/submissions/54490777-0104-40d7-ad39-1d7062a3a21f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
variable {J : V ≃ₗᵢ[ℝ] V}
namespace GlobalTheory.RealWeil
theorem _root_.solution (h : IsHeis om ρ) (f : B) : Continuous (𝓕 fun u => gau u • ρ u f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (h.integrable f)
end GlobalTheory.RealWeil
