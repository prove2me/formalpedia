-- Prove2me | solution 1 for Malliavin.CameronMartin.mgf_tilted_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:13.345726+00:00
-- url     : https://prove2.me/submissions/0bc6a82c-84af-43ae-810c-62dc2c0efec9

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_integral_exp_coe
import Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply


attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
open Malliavin Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin.CameronMartin
theorem _root_.solution (h : Space μ) (L : StrongDual ℝ W) (t : ℝ) :
    mgf L (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) t =
      Real.exp ((L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) * t +
        ((‖ofDual μ L‖₊ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
  set g : Space μ := ofDual μ L with hg
  have hnum : ∫ x, Real.exp (((fun x ↦ (h : Lp ℝ 2 μ) x) + fun x ↦ t * L x) x) ∂μ =
      Real.exp (t * L (mean μ)) * Real.exp (‖h + t • g‖ ^ 2 / 2) := by
    rw [← integral_exp_coe μ (h + t • g), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [centeredDualToLp_ae_eq μ L,
      Lp.coeFn_add (h : Lp ℝ 2 μ) ((t • g : Space μ) : Lp ℝ 2 μ),
      Lp.coeFn_smul t (g : Lp ℝ 2 μ)] with x hx hadd hsmul
    simp only [Pi.add_apply]
    rw [← Real.exp_add, Submodule.coe_add, hadd, Pi.add_apply, Submodule.coe_smul, hsmul,
      Pi.smul_apply, hg, coe_ofDual, hx, smul_eq_mul]
    ring_nf
  have hsq : ‖h + t • g‖ ^ 2 = ‖h‖ ^ 2 + 2 * t * @inner ℝ _ _ g h + t ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_add_sq_real, Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_right,
      ← Submodule.coe_inner, real_inner_comm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  unfold mgf
  rw [integral_exp_tilted, hnum, integral_exp_coe μ h, hsq]
  simp only [coe_nnnorm, NNReal.coe_pow]
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring
end Malliavin.CameronMartin
