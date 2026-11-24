-- Prove2me | solution 1 for GlobalTheory.RealWeil.Sm.good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:26:07.706619+00:00
-- url     : https://prove2.me/submissions/b27f7fea-62bc-4fe3-bea8-c6b33ed5f45e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Theorems.Thm_GlobalTheory_RealWeil_contDiff_gau
import Theorems.Thm_GlobalTheory_RealWeil_decay_gau_smul
import Theorems.Thm_GlobalTheory_RealWeil_proj_translate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
namespace Sm
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ f : B,
    Sm ρ f → Good h f := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h f hf
  let ψ : SchwartzMap V B := ⟨fun u => gau u • ρ u f, contDiff_gau.smul hf, fun k n => decay_gau_smul h hf k n⟩
  have hψ : ((𝓕 ψ : SchwartzMap V B) : V → B) = 𝓕 (fun u => gau u • ρ u f) := SchwartzMap.fourier_coe ψ
  intro n
  have hint := (𝓕 ψ).integrable_pow_mul volume n
  refine (J.measurePreserving.integrable_comp_of_integrable hint).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, proj_translate hJ h f w, h.2.2.1, hψ]
end Sm
end GlobalTheory.RealWeil
