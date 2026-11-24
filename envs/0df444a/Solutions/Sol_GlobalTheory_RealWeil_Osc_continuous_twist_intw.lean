-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.continuous_twist_intw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:28.748485+00:00
-- url     : https://prove2.me/submissions/eaf5e4cd-e8fb-497d-96d6-861e3401d0fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_cont_neg
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_integrable
import Theorems.Thm_GlobalTheory_RealWeil_Osc_continuous_twist_proj
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_continuous


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
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution {h : IsHeis (omJ J) ρ} {f : B} (hf : Good h f) :
    Continuous fun a : V →L[ℝ] V => ∫ w, ρ (a w) (∫ u, gau u • ρ (a u) (proj h (ρ (-w) f))) := by
  have hc := continuous_twist_proj h
  refine continuous_of_dominated (bound := fun w => (∫ u : V, ‖gau u‖) * ‖proj h (ρ (-w) f)‖) ?_ ?_
    ((good_integrable hf).const_mul _) ?_
  · intro a
    exact (h.continuous a.continuous
      (hc.comp (continuous_const.prodMk ((proj h).continuous.comp (cont_neg h f))))).aestronglyMeasurable
  · intro a
    refine Filter.Eventually.of_forall fun w => ?_
    rw [h.2.2.1]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp only [norm_smul, h.2.2.1]
    rw [integral_mul_const]
  · refine Filter.Eventually.of_forall fun w => ?_
    exact h.continuous (by fun_prop) (hc.comp (continuous_id.prodMk continuous_const))
end GlobalTheory.RealWeil.Osc
