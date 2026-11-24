-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.inner_intw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:57:12.116697+00:00
-- url     : https://prove2.me/submissions/393df008-4c2c-48b9-a6be-5b6bfa63d565

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_integrable
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_intw
import Theorems.Thm_P2M_GlobalTheory_RealWeil_Osc_inner_heis__d75be7e68716
import Theorems.Thm_GlobalTheory_RealWeil_Osc_inner_integral
import Theorems.Thm_GlobalTheory_RealWeil_Osc_inner_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Φ : B →L[ℂ] H}
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hΦ : ∀ v f, ‖Φ (ρ' v f)‖ = ‖Φ f‖)
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) :
    inner ℂ (Φ (intw ρ' T ρ f)) (Φ (intw ρ' T ρ f)) = ∫ w, inner ℂ (Φ (T (ρ (-w) f))) (Φ (T (ρ (-w) f))) := by
  have := inner_integral (Φ := Φ) (intw ρ' T ρ f) (intw_integrable h' hT hf)
  refine this.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
  simp only
  rw [inner_heis' hJ h' hΦ, ← hT' (ρ (-w) f), ← inner_proj hJ h' hΦ, proj_heis_intw hJ h' hT hT' hf, hT']
end GlobalTheory.RealWeil.Osc
