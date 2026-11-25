-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.exists_pos_le_norm_prinSymb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:18.593469+00:00
-- url     : https://prove2.me/submissions/403bef01-a676-45ed-86ab-3058646dfd98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_continuous_prinSymb
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_prinSymb_smul
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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {ι : Type*} [Fintype ι] {m : ℕ} (hm : 1 ≤ m) (c : ι → ℂ)
    (w : ι → Fin m → E) (hell : ∀ ξ : E, ξ ≠ 0 → prinSymb c w ξ ≠ 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : E, c₀ * ‖ξ‖ ^ m ≤ ‖prinSymb c w ξ‖ := by
  by_cases hE : ∃ ξ : E, ξ ≠ 0
  · obtain ⟨ξ₀, hξ₀⟩ := hE
    have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨‖ξ₀‖⁻¹ • ξ₀, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ₀)]⟩
    obtain ⟨η, hη, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
      (continuous_prinSymb c w).norm.continuousOn
    have hη0 : η ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hη; exact zero_ne_one hη
    refine ⟨‖prinSymb c w η‖, norm_pos_iff.2 (hell η hη0), fun ξ ↦ ?_⟩
    by_cases hξ : ξ = 0
    · rw [hξ, norm_zero, zero_pow (by omega), mul_zero]; exact norm_nonneg _
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hmem : ‖ξ‖⁻¹ • ξ ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hmin hmem
      simp only at h1
      have h2 : prinSymb c w ξ = ((‖ξ‖ : ℝ) : ℂ) ^ m * prinSymb c w (‖ξ‖⁻¹ • ξ) := by
        rw [← prinSymb_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, mul_comm]
      gcongr
      exact h1
  · simp only [not_exists, not_not] at hE
    refine ⟨1, one_pos, fun ξ ↦ ?_⟩
    rw [hE ξ, norm_zero, zero_pow (by omega), mul_zero]; exact norm_nonneg _
end GroundTheory.Automorphic.Sobolev
