-- Prove2me | solution 1 for GlobalTheory.RealWeil.Good.sm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:34.342105+00:00
-- url     : https://prove2.me/submissions/471d112b-b111-44a7-b6e0-018844713e87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Theorems.Thm_GlobalTheory_RealWeil_gau_ne_zero
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous_gau_smul
import Theorems.Thm_GlobalTheory_RealWeil_Good_fourier
import Theorems.Thm_GlobalTheory_RealWeil_Good_integrable_fourier
import Theorems.Thm_GlobalTheory_RealWeil_contDiff_gau_inv

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
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) : Sm ρ f := by
  have h1 := (h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f) (hf.integrable_fourier hJ)
  have h2 : ContDiff ℝ ∞ (𝓕 (𝓕 fun u => gau u • ρ u f)) := Real.contDiff_fourier fun n _ => hf.fourier hJ n
  have h3 : ContDiff ℝ ∞ fun u => gau u • ρ u f := by
    rw [← h1]
    have : 𝓕⁻ (𝓕 fun u => gau u • ρ u f) = fun u => 𝓕 (𝓕 fun u => gau u • ρ u f) (-u) := by
      funext u; rw [Real.fourierInv_eq_fourier_neg]
    rw [this]
    exact h2.comp contDiff_neg
  have : ContDiff ℝ ∞ fun u => (gau u)⁻¹ • gau u • ρ u f := (contDiff_gau_inv (V := V)).smul h3
  simpa only [smul_smul, inv_mul_cancel₀ (gau_ne_zero _), one_smul, Sm] using this
end Good
end GlobalTheory.RealWeil
