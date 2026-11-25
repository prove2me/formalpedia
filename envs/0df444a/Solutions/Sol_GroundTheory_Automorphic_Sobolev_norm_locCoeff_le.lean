-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_locCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:58.445636+00:00
-- url     : https://prove2.me/submissions/af5122fc-00cd-4a34-94fa-bcf02ec9fd00

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_bump_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_bump_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) (i : Fin n) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ y ∈ Metric.closedBall x₀ (2 * δ), ‖a i y - a i x₀‖ ≤ η) (x : E) :
    ‖locCoeff a x₀ hδ i x‖ ≤ η := by
  have e : locCoeff a x₀ hδ i x = bump x₀ hδ x * (a i x - a i x₀) := by
    simp only [locCoeff, sub_apply, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply (bump x₀ hδ).hasTemperateGrowth, smul_eq_mul]
    ring
  rw [e, norm_mul]
  by_cases hx : x ∈ Metric.closedBall x₀ (2 * δ)
  · calc ‖bump x₀ hδ x‖ * ‖a i x - a i x₀‖ ≤ 1 * η :=
          mul_le_mul (norm_bump_le x₀ hδ x) (h x hx) (norm_nonneg _) zero_le_one
      _ = η := one_mul η
  · rw [bump_eq_zero x₀ hδ hx, norm_zero, zero_mul]; exact hη
end GroundTheory.Automorphic.Sobolev
