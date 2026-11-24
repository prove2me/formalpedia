-- Prove2me | solution 1 for GlobalTheory.RealWeil.Good.integrable_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:07:13.490465+00:00
-- url     : https://prove2.me/submissions/6b6de022-8cca-41fd-9fe7-3f668e23fae0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Theorems.Thm_GlobalTheory_RealWeil_Good_fourier
import Theorems.Thm_GlobalTheory_RealWeil_continuous_fourier_gau

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
namespace Good
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Integrable (𝓕 fun u => gau u • ρ u f) := by
  have := hf.fourier hJ 0
  simp only [pow_zero, one_mul] at this
  exact (integrable_norm_iff (continuous_fourier_gau h f).aestronglyMeasurable).1 this
end Good
end GlobalTheory.RealWeil
