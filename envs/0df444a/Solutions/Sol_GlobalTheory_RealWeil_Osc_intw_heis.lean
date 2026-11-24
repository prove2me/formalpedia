-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.intw_heis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:41.403124+00:00
-- url     : https://prove2.me/submissions/8f7e99ef-4709-4a6b-9c1b-388f8a90765f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_of_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_heis
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_ext
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_intw
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_intw
import Theorems.Thm_GlobalTheory_RealWeil_Good_sm


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
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Sm ρ f) (a : V) :
    intw ρ' T ρ (ρ a f) = ρ' a (intw ρ' T ρ f) := by
  have g1 := good_of_sm hJ h hf
  have g2 := good_of_sm hJ h (sm_heis h a hf)
  refine good_ext hJ (good_intw hJ h' hT hT' g2)
    (good_of_sm hJ h' (sm_heis h' a ((good_intw hJ h' hT hT' g1).sm hJ))) fun v => ?_
  rw [proj_heis_intw hJ h' hT hT' g2, h.2.1, h'.2.1, map_smul, map_smul, proj_heis_intw hJ h' hT hT' g1]
end GlobalTheory.RealWeil.Osc
