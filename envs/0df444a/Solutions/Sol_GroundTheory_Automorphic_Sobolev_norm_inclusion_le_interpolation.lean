-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_inclusion_le_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:17.925051+00:00
-- url     : https://prove2.me/submissions/579e3a25-3588-4bf8-a9d9-ada316463c33

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_inclusion
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_inclusion_sq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_rpow_of_integrable
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_weight_mul_norm_sq_fourierFun
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_sq_eq_integral
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
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {r t s : ℝ} (hrt : r < t) (hts : t < s)
    (v : SobolevSpace E F s) :
    ‖SobolevSpace.inclusion hts.le v‖ ≤
      ‖v‖ ^ ((t - r) / (s - r)) * ‖SobolevSpace.inclusion (hrt.trans hts).le v‖ ^ ((s - t) / (s - r)) := by
  have hsr : 0 < s - r := by linarith
  set a := (t - r) / (s - r) with ha_def
  set θ := (s - t) / (s - r) with hθ_def
  have ha : 0 < a := div_pos (by linarith) hsr
  have hθ : 0 < θ := div_pos (by linarith) hsr
  have haθ : a + θ = 1 := by rw [ha_def, hθ_def, ← add_div]; field_simp; ring
  have hexp : s * a + r * θ = t := by rw [ha_def, hθ_def]; field_simp; ring
  set A : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun v ξ‖ ^ 2
  set B : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ r * ‖fourierFun v ξ‖ ^ 2
  have hA : Integrable A (volume : Measure E) := integrable_weight_mul_norm_sq_fourierFun v
  have hB : Integrable B (volume : Measure E) := by
    have := integrable_weight_mul_norm_sq_fourierFun
      (SobolevSpace.inclusion (hrt.trans hts).le v)
    refine this.congr ?_
    filter_upwards [fourierFun_inclusion (hrt.trans hts).le v] with ξ hξ
    simp only [B, hξ]
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun ξ ↦ by positivity
  have hB0 : ∀ ξ, 0 ≤ B ξ := fun ξ ↦ by positivity
  have hpq : (1 / a).HolderConjugate (1 / θ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, by simp [haθ]⟩
    rw [lt_div_iff₀ ha, one_mul]; linarith
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ fun ξ ↦ Real.rpow_nonneg (hA0 ξ) a) (ae_of_all _ fun ξ ↦ Real.rpow_nonneg (hB0 ξ) θ)
    (memLp_rpow_of_integrable hA hA0 ha) (memLp_rpow_of_integrable hB hB0 hθ)
  have e1 : ∀ ξ, A ξ ^ a * B ξ ^ θ = (1 + ‖ξ‖ ^ 2) ^ t * ‖fourierFun v ξ‖ ^ 2 := by
    intro ξ
    have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    simp only [A, B]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul h0.le, ← Real.rpow_mul h0.le]
    calc (1 + ‖ξ‖ ^ 2) ^ (s * a) * (‖fourierFun v ξ‖ ^ 2) ^ a *
          ((1 + ‖ξ‖ ^ 2) ^ (r * θ) * (‖fourierFun v ξ‖ ^ 2) ^ θ)
        = ((1 + ‖ξ‖ ^ 2) ^ (s * a) * (1 + ‖ξ‖ ^ 2) ^ (r * θ)) *
          ((‖fourierFun v ξ‖ ^ 2) ^ a * (‖fourierFun v ξ‖ ^ 2) ^ θ) := by ring
      _ = _ := by
        rw [← Real.rpow_add h0, hexp, ← Real.rpow_add_of_nonneg (by positivity) ha.le hθ.le, haθ,
          Real.rpow_one]
  have e2 : ∀ ξ, (A ξ ^ a) ^ (1 / a) = A ξ := fun ξ ↦ by
    rw [← Real.rpow_mul (hA0 ξ), mul_one_div_cancel ha.ne', Real.rpow_one]
  have e3 : ∀ ξ, (B ξ ^ θ) ^ (1 / θ) = B ξ := fun ξ ↦ by
    rw [← Real.rpow_mul (hB0 ξ), mul_one_div_cancel hθ.ne', Real.rpow_one]
  simp only [e1, e2, e3, one_div_one_div] at hH
  rw [← norm_inclusion_sq hts.le, ← norm_sq_eq_integral,
    ← norm_inclusion_sq (hrt.trans hts).le] at hH
  have hsq : ∀ (x : ℝ) (c : ℝ), 0 ≤ x → (x ^ 2) ^ c = (x ^ c) ^ 2 := fun x c hx ↦ by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]
  rw [hsq _ _ (norm_nonneg _), hsq _ _ (norm_nonneg _), ← mul_pow] at hH
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hH
end GroundTheory.Automorphic.Sobolev
