-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.good_intw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:18.776876+00:00
-- url     : https://prove2.me/submissions/7caf6db2-ddeb-4390-a0ef-151cfd7f18a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_cont_neg
import Theorems.Thm_GlobalTheory_RealWeil_Osc_norm_le_of_proj
import Theorems.Thm_GlobalTheory_RealWeil_Osc_proj_heis_intw
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
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ')
    (hT : ∀ x, T (proj h x) = T x) (hT' : ∀ x, proj h' (T x) = T x) {f : B} (hf : Good h f) :
    Good h' (intw ρ' T ρ f) := by
  intro n
  simp only [proj_heis_intw hJ h' hT hT' hf]
  refine Integrable.mono' ((hf n).const_mul ‖T‖)
    ((continuous_norm.pow n).mul (T.continuous.comp (cont_neg h f)).norm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (by positivity), mul_left_comm]
  gcongr
  exact norm_le_of_proj hT _
end GlobalTheory.RealWeil.Osc
