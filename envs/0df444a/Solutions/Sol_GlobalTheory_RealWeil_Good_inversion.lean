-- Prove2me | solution 1 for GlobalTheory.RealWeil.Good.inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:37.219797+00:00
-- url     : https://prove2.me/submissions/7cfe4a85-1f40-45da-9fa0-90e6a0b76464

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Theorems.Thm_GlobalTheory_RealWeil_gau_zero
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous_gau_smul
import Theorems.Thm_GlobalTheory_RealWeil_omJ_skew
import Theorems.Thm_GlobalTheory_RealWeil_proj_translate
import Theorems.Thm_GlobalTheory_RealWeil_Good_integrable_fourier

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
    ∫ w, ρ w (proj h (ρ (-w) f)) = f := by
  have e : ∀ w, ρ w (proj h (ρ (-w) f)) = 𝓕 (fun u => gau u • ρ u f) (J w) := by
    intro w
    have h0 : omJ J w (-w) = 0 := by
      have := omJ_skew hJ w w
      have e : omJ J w (-w) = -omJ J w w := by simp [omJ]
      linarith
    rw [proj_translate hJ, h.2.1, h0, add_neg_cancel, h.1]
    simp
  simp only [e]
  rw [J.measurePreserving.integral_comp J.toHomeomorph.measurableEmbedding]
  have := congrFun ((h.continuous_gau_smul f).fourierInv_fourier_eq (h.integrable f)
    (hf.integrable_fourier hJ)) 0
  rw [Real.fourierInv_eq] at this
  simpa [gau_zero, h.1] using this
end Good
end GlobalTheory.RealWeil
