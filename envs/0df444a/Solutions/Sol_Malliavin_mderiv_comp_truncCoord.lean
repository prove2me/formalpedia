-- Prove2me | solution 1 for Malliavin.mderiv_comp_truncCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:03.23475+00:00
-- url     : https://prove2.me/submissions/816b7c23-70ba-4567-b2ef-56b20cff229f

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_contDiff_truncCoord
import Theorems.Thm_Malliavin_fderiv_truncCoord_apply
import Theorems.Thm_Malliavin_CameronMartin_apply_inclusion
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
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
theorem _root_.solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (m : ℕ)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    mderiv μ (fun y ↦ f (truncCoord m L y)) x =
      ∑ i, (fderiv ℝ f (truncCoord m L x) (Pi.single i 1) * deriv (cutoff m) (L i x)) •
        ofDual μ (L i) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_mderiv, Submodule.coe_inner, Submodule.coe_sum, sum_inner]
  simp only [Submodule.coe_smul, real_inner_smul_left]
  simp_rw [← Submodule.coe_inner, ← apply_inclusion]
  have hcomp : (fun y ↦ f (truncCoord m L y)) = f ∘ truncCoord m L := rfl
  rw [hcomp, fderiv_comp x (hf.differentiable one_ne_zero _)
    ((contDiff_truncCoord m L).differentiable one_ne_zero _), ContinuousLinearMap.comp_apply,
    fderiv_truncCoord_apply, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring
end Malliavin
