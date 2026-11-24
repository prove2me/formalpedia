-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.inner_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:28:08.59897+00:00
-- url     : https://prove2.me/submissions/50eed39e-440e-4fb1-9bf8-b6b0b6f7f7eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_P2M_GlobalTheory_RealWeil_Osc_inner_heis__d75be7e68716
import Theorems.Thm_GlobalTheory_RealWeil_Osc_inner_integral
import Theorems.Thm_GlobalTheory_RealWeil_Osc_star_gau
import Theorems.Thm_GlobalTheory_RealWeil_gau_neg
import Theorems.Thm_GlobalTheory_RealWeil_proj_apply


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
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖)
    (x y : B) : inner ℂ (Φ (proj h x)) (Φ y) = inner ℂ (Φ x) (Φ (proj h y)) := by
  rw [← inner_conj_symm, proj_apply, proj_apply, inner_integral _ (h.integrable _), inner_integral _ (h.integrable _),
    ← integral_conj, ← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_smul, inner_smul_right, map_mul, inner_conj_symm, star_gau, gau_neg, inner_heis' hJ h hΦ u]
end GlobalTheory.RealWeil.Osc
