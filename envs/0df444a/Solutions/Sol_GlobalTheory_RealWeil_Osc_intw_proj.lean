-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.intw_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:42.692748+00:00
-- url     : https://prove2.me/submissions/ad03204f-174e-4a25-89ce-483fc61426f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_comp
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_ext
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_intw
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_intw
import Theorems.Thm_GlobalTheory_RealWeil_Good_sm
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
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Sm ρ f)
    (a b : V →L[ℝ] V) (hab : ∀ v, a (b v) = v) (ha : ∀ x y, omJ J (a x) (a y) = omJ J x y) :
    intw ρ' T ρ (proj (h.twist a ha) f) = proj (h'.twist a ha) (intw ρ' T ρ f) := by
  have g1 := good_of_sm hJ h hf
  have s : ∀ {ρ : V → B →L[ℂ] B} (h : IsHeis (omJ J) ρ) (x : B), Good h (proj (h.twist a ha) x) := by
    intro ρ h x
    have := sm_comp b ((good_proj hJ (h.twist a ha) x).sm hJ)
    simp only [hab] at this
    exact good_of_sm hJ h this
  refine good_ext hJ (good_intw hJ h' hT hT' (s h f)) (s h' _) fun v => ?_
  rw [proj_heis_intw hJ h' hT hT' (s h f)]
  have e1 := (T.comp (ρ v)).integral_comp_comm ((h.twist a ha).integrable f)
  have e2 := ((proj h').comp (ρ' v)).integral_comp_comm ((h'.twist a ha).integrable (intw ρ' T ρ f))
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  rw [proj_apply (h.twist a ha), proj_apply (h'.twist a ha), ← e1, ← e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [h.2.1, h'.2.1, map_smul, proj_heis_intw hJ h' hT hT' g1]
end GlobalTheory.RealWeil.Osc
