-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.continuous_twist_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:59.886133+00:00
-- url     : https://prove2.me/submissions/ffb6a12f-000a-4e31-84c9-35298aa73def

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
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
theorem _root_.solution (h : IsHeis (omJ J) ρ) :
    Continuous fun p : (V →L[ℝ] V) × B => ∫ u, gau u • ρ (p.1 u) p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  refine continuousAt_of_dominated (bound := fun u => ‖gau u‖ * (‖p₀.2‖ + 1)) ?_ ?_
    ((integrable_gau (V := V)).norm.mul_const _) ?_
  · exact Filter.Eventually.of_forall fun p =>
      (continuous_gau.smul ((h.2.2.2 p.2).comp p.1.continuous)).aestronglyMeasurable
  · have : ∀ᶠ p : (V →L[ℝ] V) × B in nhds p₀, ‖p.2‖ < ‖p₀.2‖ + 1 :=
      (continuous_snd.norm.continuousAt (x := p₀)).eventually_lt_const (lt_add_one _)
    filter_upwards [this] with p hp
    refine Filter.Eventually.of_forall fun u => ?_
    rw [norm_smul, h.2.2.1]
    gcongr
  · refine Filter.Eventually.of_forall fun u => Continuous.continuousAt ?_
    exact (h.continuous (by fun_prop) continuous_snd).const_smul _
end GlobalTheory.RealWeil.Osc
