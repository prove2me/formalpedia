-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.intw_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:52.810941+00:00
-- url     : https://prove2.me/submissions/7b76aecd-5a6b-472b-b20a-23f418fb2f14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_cont_neg
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_integrable
import Theorems.Thm_GlobalTheory_RealWeil_Osc_norm_le_of_proj
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
theorem _root_.solution {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ') (hT : ∀ x, T (proj h x) = T x)
    {f : B} (hf : Good h f) : Integrable fun w => ρ' w (T (ρ (-w) f)) := by
  refine Integrable.mono' ((good_integrable hf).const_mul ‖T‖)
    (h'.continuous continuous_id (T.continuous.comp (cont_neg h f))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [h'.2.2.1]
  exact norm_le_of_proj hT _
end GlobalTheory.RealWeil.Osc
