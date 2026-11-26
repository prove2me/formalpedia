-- Prove2me | solution 1 for Malliavin.norm_mderivClosure_comp_pi_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:04.446006+00:00
-- url     : https://prove2.me/submissions/19457f85-702a-499e-9570-778d27feedc7

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
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
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 μ} (hF : ∀ i, F i ∈ domD12 μ) :
    ‖mderivClosure μ ((memLp_comp_pi μ hf hK F).toLp _)‖ ≤
      K * ∑ i, ‖mderivClosure μ (F i)‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  rw [(comp_pi_mem_domD12 μ hf hK hF).2, Lp.norm_toLp]
  have hmeas : ∀ i, AEStronglyMeasurable
      (fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i (1 : ℝ)) • (mderivClosure μ (F i)) x) μ :=
    fun i ↦ by
      have hpi : AEStronglyMeasurable (fun x i ↦ F i x) μ :=
        (aemeasurable_pi_iff.mpr fun i ↦
          (Lp.aestronglyMeasurable (F i)).aemeasurable).aestronglyMeasurable
      exact (((hf.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hpi)
        |>.apply_continuousLinearMap _).smul (Lp.aestronglyMeasurable _)
  have hbound : eLpNorm (fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
      (mderivClosure μ (F i)) x) 2 μ ≤ ∑ i, ‖K‖ₑ * eLpNorm (⇑(mderivClosure μ (F i))) 2 μ := by
    calc eLpNorm (fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
          (mderivClosure μ (F i)) x) 2 μ
        = eLpNorm (∑ i, fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
            (mderivClosure μ (F i)) x) 2 μ := by
          congr 1
          funext x
          simp only [Finset.sum_apply]
      _ ≤ ∑ i, eLpNorm (fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
            (mderivClosure μ (F i)) x) 2 μ := eLpNorm_sum_le (fun i _ ↦ hmeas i) one_le_two
      _ ≤ ∑ i, eLpNorm (K • ⇑(mderivClosure μ (F i))) 2 μ := by
          refine Finset.sum_le_sum fun i _ ↦ eLpNorm_mono fun x ↦ ?_
          rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hK0]
          exact mul_le_mul_of_nonneg_right (abs_fderiv_pi_single_le hK _ i) (norm_nonneg _)
      _ ≤ ∑ i, ‖K‖ₑ * eLpNorm (⇑(mderivClosure μ (F i))) 2 μ :=
          Finset.sum_le_sum fun i _ ↦ eLpNorm_const_smul_le
  have hfin : ∀ i, ‖K‖ₑ * eLpNorm (⇑(mderivClosure μ (F i))) 2 μ ≠ ∞ := fun i ↦
    ENNReal.mul_ne_top enorm_ne_top (Lp.eLpNorm_ne_top _)
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ ↦ hfin i) hbound).trans
    (le_of_eq ?_)
  rw [ENNReal.toReal_sum (fun i _ ↦ hfin i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs, abs_of_nonneg hK0, Lp.norm_def]
end Malliavin
