-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.proj_heis_intw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:42:46.999953+00:00
-- url     : https://prove2.me/submissions/9b59a71a-a859-47a3-86ea-ec6b2bde24de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_integrable
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_heis
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
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) (v : V) :
    proj h' (ρ' v (intw ρ' T ρ f)) = T (ρ v f) := by
  have e1 := ((proj h').comp (ρ' v)).integral_comp_comm (intw_integrable h' hT hf)
  have e2 := (T.comp ((proj h).comp (ρ v))).integral_comp_comm (intw_integrable h (proj_proj hJ h) hf)
  rw [hf.inversion hJ] at e2
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  rw [intw, ← e1, ← hT, ← e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [proj_heis_heis hJ h' _ _ (hT' _), proj_heis_heis hJ h _ _ (proj_proj hJ h _), map_smul, hT]
end GlobalTheory.RealWeil.Osc
