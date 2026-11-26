-- Prove2me | solution 1 for Malliavin.fderiv_truncCoord_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:35:29.545793+00:00
-- url     : https://prove2.me/submissions/607f59d0-0dbb-4e7f-9a7d-3c34e4e852a3

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_cutoff_contDiff
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
omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ]
namespace Malliavin
theorem _root_.solution (m : ℕ) {n : ℕ} (L : Fin n → StrongDual ℝ W) (x w : W) :
    fderiv ℝ (truncCoord m L) x w =
      ∑ i, (deriv (cutoff m) (L i x) * L i w) • Pi.single i (1 : ℝ) := by
  have hd : ∀ i, DifferentiableAt ℝ (fun x ↦ cutoff m (L i x)) x := fun i ↦
    ((cutoff_contDiff m).differentiable one_ne_zero (L i x)).comp x (L i).differentiableAt
  change fderiv ℝ (fun x (i : Fin n) ↦ cutoff m (L i x)) x w = _
  rw [fderiv_pi hd]
  ext j
  rw [ContinuousLinearMap.pi_apply, Finset.sum_apply]
  have hcomp : (fun x ↦ cutoff m (L j x)) = cutoff m ∘ L j := rfl
  rw [hcomp, fderiv_comp x ((cutoff_contDiff m).differentiable one_ne_zero _)
    (L j).differentiableAt, (L j).fderiv, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
    smul_eq_mul]
  simp only [mul_comm, Pi.smul_apply, Pi.single_apply, smul_eq_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
end Malliavin
