-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.good_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:08.621294+00:00
-- url     : https://prove2.me/submissions/b8d25b88-dabb-41b5-b6da-66645a6b16b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_integrable_pow_gau
import Theorems.Thm_GlobalTheory_RealWeil_gau_neg
import Theorems.Thm_GlobalTheory_RealWeil_proj_heis_proj


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
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (x : B) : Good h (proj h x) := by
  intro n
  refine ((integrable_pow_gau (V := V) n).mul_const ‖proj h x‖).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [proj_heis_proj hJ, gau_neg, norm_smul, mul_assoc]
end GlobalTheory.RealWeil.Osc
