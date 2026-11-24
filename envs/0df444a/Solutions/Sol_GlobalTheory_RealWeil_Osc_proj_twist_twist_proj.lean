-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.proj_twist_twist_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:45.717542+00:00
-- url     : https://prove2.me/submissions/fe5f6ad1-251b-4aeb-a34f-c4d7b0f2860e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_heis
import Theorems.Thm_GlobalTheory_RealWeil_IsHeis_twist
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
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (a b : V →L[ℝ] V)
    (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) (hb : ∀ x y, omJ J (b x) (b y) = omJ J x y) (x : B) :
    proj h (proj (h.twist a ha) (proj (h.twist b hb) (proj h x))) = mu J a b • proj h x := by
  rw [proj_apply (h.twist a ha), ← (proj h).integral_comp_comm ((h.twist a ha).integrable _), mu,
    ← integral_smul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e1 := ((proj h).comp (ρ (a u))).integral_comp_comm ((h.twist b hb).integrable (proj h x))
  simp only [ContinuousLinearMap.comp_apply] at e1
  simp only
  rw [map_smul, proj_apply (h.twist b hb), ← e1, ← integral_smul, ← integral_smul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [map_smul]
  rw [proj_heis_heis hJ h _ _ (proj_proj hJ h _), smul_smul, smul_smul]
end GlobalTheory.RealWeil.Osc
