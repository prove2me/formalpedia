-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.norm_intw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:43.56803+00:00
-- url     : https://prove2.me/submissions/bc4636c0-b232-4b8a-813b-ff601cb03fe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_inner_intw
import Theorems.Thm_GlobalTheory_RealWeil_Good_inversion


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
    (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (hΦ' : ∀ v f, ‖Φ (ρ' v f)‖ = ‖Φ f‖)
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x)
    (hn : ∀ x, inner ℂ (Φ (T x)) (Φ (T x)) = inner ℂ (Φ (proj h x)) (Φ (proj h x))) {f : B} (hf : Good h f) :
    ‖Φ (intw ρ' T ρ f)‖ = ‖Φ f‖ := by
  have e1 := inner_intw hJ h' hΦ' hT hT' hf
  have e2 := inner_intw hJ h hΦ (proj_proj hJ h) (proj_proj hJ h) hf
  have e3 : intw ρ (proj h) ρ f = f := hf.inversion hJ
  simp only [hn] at e1
  rw [e3, ← e1] at e2
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), e2]
end GlobalTheory.RealWeil.Osc
