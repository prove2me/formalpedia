-- Prove2me | solution 1 for Malliavin.cylinder_mem_domD12_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:49.507666+00:00
-- url     : https://prove2.me/submissions/d32cc7df-eac2-41f5-97a0-71a3e98e1d17

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_isSmoothBounded_comp_truncCoord
import Theorems.Thm_Malliavin_mderiv_comp_truncCoord
import Theorems.Thm_Malliavin_norm_mderiv_comp_truncCoord_le
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mderivClosure_toLp
import Theorems.Thm_Malliavin_mderiv_cylindrical
import Theorems.Thm_Malliavin_mem_domD12_of_tendsto
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_tendsto_cutoff
import Theorems.Thm_Malliavin_tendsto_deriv_cutoff
import Theorems.Thm_Malliavin_tendsto_toLp_of_dominated
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (L : Fin n → StrongDual ℝ W) {φ : (Fin n → ℝ) → ℝ} {ψ : W → ℝ}
    (hφf : ∀ y, |f y| ≤ φ y) (hφf' : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y)
    (hψ : ∀ m x, φ (truncCoord m L x) ≤ ψ x) (hψ' : ∀ x, φ (fun i ↦ L i x) ≤ ψ x)
    (hint : Integrable (fun x ↦ ψ x ^ 2) μ) :
    (memLp_cylinder_of_dominated μ hf L hφf hψ' hint).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_cylinder_of_dominated μ hf L hφf hψ' hint).toLp _) =
        (memLp_mderiv_cylinder_of_dominated μ hf L hφf' hψ' hint).toLp _ := by
  set Fm : ∀ m : ℕ, IsSmoothBounded (fun x ↦ f (truncCoord m L x)) :=
    fun m ↦ isSmoothBounded_comp_truncCoord hf m L with hFm
  have hlim : ∀ x, Tendsto (fun m ↦ truncCoord m L x) atTop (𝓝 (fun i ↦ L i x)) := fun x ↦
    tendsto_pi_nhds.mpr fun i ↦ tendsto_cutoff (L i x)
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x ↦ (abs_nonneg _).trans ((hφf _).trans (hψ' x))
  refine mem_domD12_of_tendsto μ (F := fun m ↦ (Fm m).toLp μ) (fun m ↦ (Fm m).toLp_mem_domD12 μ)
    ?_ ?_
  · refine tendsto_toLp_of_dominated (fun m ↦ (Fm m).memLp μ 2)
      (memLp_cylinder_of_dominated μ hf L hφf hψ' hint)
      (bound := fun x ↦ 2 ^ 2 * ψ x ^ 2) (hint.const_mul _)
      (fun m ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · have h1 : |f (truncCoord m L x)| ≤ ψ x := (hφf _).trans (hψ m x)
      have h2 : |f (fun i ↦ L i x)| ≤ ψ x := (hφf _).trans (hψ' x)
      rw [Real.norm_eq_abs, ← mul_pow]
      gcongr
      calc |f (truncCoord m L x) - f (fun i ↦ L i x)|
          ≤ |f (truncCoord m L x)| + |f (fun i ↦ L i x)| := abs_sub _ _
        _ ≤ ψ x + ψ x := add_le_add h1 h2
        _ = 2 * ψ x := by ring
    · exact (hf.continuous.tendsto _).comp (hlim x)
  · simp_rw [mderivClosure_toLp]
    unfold IsSmoothBounded.mderivLp
    refine tendsto_toLp_of_dominated (fun m ↦ (Fm m).memLp_mderiv μ 2)
      (memLp_mderiv_cylinder_of_dominated μ hf L hφf' hψ' hint)
      (bound := fun x ↦ (2 * ∑ i, ‖ofDual μ (L i)‖) ^ 2 * ψ x ^ 2) (hint.const_mul _)
      (fun m ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · have hK : 0 ≤ ∑ i, ‖ofDual μ (L i)‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      have h1 := (norm_mderiv_comp_truncCoord_le μ hf hφf' m L x).trans
        (mul_le_mul_of_nonneg_right (hψ m x) hK)
      have h2 := (norm_mderiv_cylinder_le μ hf hφf' L x).trans
        (mul_le_mul_of_nonneg_right (hψ' x) hK)
      rw [← mul_pow]
      gcongr
      calc ‖mderiv μ (fun y ↦ f (truncCoord m L y)) x - mderiv μ (fun y ↦ f (fun i ↦ L i y)) x‖
          ≤ ‖mderiv μ (fun y ↦ f (truncCoord m L y)) x‖ +
              ‖mderiv μ (fun y ↦ f (fun i ↦ L i y)) x‖ := norm_sub_le _ _
        _ ≤ ψ x * ∑ i, ‖ofDual μ (L i)‖ + ψ x * ∑ i, ‖ofDual μ (L i)‖ := add_le_add h1 h2
        _ = 2 * (∑ i, ‖ofDual μ (L i)‖) * ψ x := by ring
    · rw [mderiv_cylindrical μ f L x (hf.differentiable one_ne_zero _)]
      simp_rw [mderiv_comp_truncCoord μ f hf _ L x]
      refine tendsto_finsetSum _ fun i _ ↦ ?_
      refine Tendsto.smul_const ?_ _
      have hfd : Tendsto (fun m ↦ fderiv ℝ f (truncCoord m L x) (Pi.single i 1)) atTop
          (𝓝 (fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1))) := by
        have hc : Continuous fun y ↦ fderiv ℝ f y (Pi.single i (1 : ℝ)) :=
          (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
        exact (hc.tendsto _).comp (hlim x)
      simpa using hfd.mul (tendsto_deriv_cutoff (L i x))
end Malliavin
