-- Prove2me | solution 1 for Malliavin.dualLp_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:54.349342+00:00
-- url     : https://prove2.me/submissions/d66efd24-9bc4-4e1f-97f2-1fa03102036c

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_cutoff_contDiff
import Theorems.Thm_Malliavin_abs_cutoff_le
import Theorems.Thm_Malliavin_abs_cutoff_le_const
import Theorems.Thm_Malliavin_deriv_cutoff_nonneg
import Theorems.Thm_Malliavin_deriv_cutoff_le_one
import Theorems.Thm_Malliavin_abs_deriv_cutoff_le
import Theorems.Thm_Malliavin_tendsto_deriv_cutoff
import Theorems.Thm_Malliavin_tendsto_cutoff
import Theorems.Thm_Malliavin_tendsto_toLp_of_dominated
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mderivClosure_toLp
import Theorems.Thm_Malliavin_mderiv_comp
import Theorems.Thm_Malliavin_mderiv_dual
import Theorems.Thm_Malliavin_mem_domD12_of_tendsto
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
universe u_1 u_2
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution (L : StrongDual ℝ W) :
    dualLp μ L ∈ domD12 μ ∧ mderivClosure μ (dualLp μ L) = constOfDual μ L := by
  have hn : ∀ n, IsSmoothBounded fun x ↦ cutoff n (L x) := fun n ↦
    IsSmoothBounded.comp_dual (cutoff_contDiff n) ⟨_, abs_cutoff_le_const n⟩
      ⟨1, abs_deriv_cutoff_le n⟩ L
  refine mem_domD12_of_tendsto μ (F := fun n ↦ (hn n).toLp μ)
    (fun n ↦ (hn n).toLp_mem_domD12 μ) ?_ ?_
  · -- `cutoff n ∘ L → L` in `L²(μ)`
    refine tendsto_toLp_of_dominated (hf := fun n ↦ (hn n).memLp μ 2)
      (hg := IsGaussian.memLp_dual μ L 2 (by simp)) (bound := fun x ↦ 4 * (L x) ^ 2)
      ((IsGaussian.memLp_dual μ L 2 (by simp)).integrable_sq.const_mul 4)
      (fun n ↦ Filter.Eventually.of_forall fun x ↦ ?_)
      (Filter.Eventually.of_forall fun x ↦ tendsto_cutoff (L x))
    have h1 : |cutoff n (L x) - L x| ≤ 2 * |L x| := by
      calc |cutoff n (L x) - L x| ≤ |cutoff n (L x)| + |L x| := abs_sub _ _
        _ ≤ |L x| + |L x| := add_le_add_left (abs_cutoff_le n _) _
        _ = 2 * |L x| := by ring
    calc ‖cutoff n (L x) - L x‖ ^ 2 = |cutoff n (L x) - L x| ^ 2 := by rw [Real.norm_eq_abs]
      _ ≤ (2 * |L x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = 4 * (L x) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  · -- `D (cutoff n ∘ L) = cutoff n' (L) • ofDual L → ofDual L` in `L²(μ; H)`
    simp_rw [mderivClosure_toLp]
    unfold IsSmoothBounded.mderivLp constOfDual
    have hm : ∀ n x,
        mderiv μ (fun y ↦ cutoff n (L y)) x = deriv (cutoff n) (L x) • ofDual μ L := by
      intro n x
      rw [mderiv_comp μ ((cutoff_contDiff n).differentiable one_ne_zero _) L.differentiableAt,
        mderiv_dual]
    refine tendsto_toLp_of_dominated (hf := fun n ↦ (hn n).memLp_mderiv μ 2)
      (hg := memLp_const _) (bound := fun _ ↦ 4 * ‖ofDual μ L‖ ^ 2) (integrable_const _)
      (fun n ↦ Filter.Eventually.of_forall fun x ↦ ?_)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    · rw [hm]
      have h1 : deriv (cutoff n) (L x) • ofDual μ L - ofDual μ L =
          (deriv (cutoff n) (L x) - 1) • ofDual μ L := by
        rw [sub_smul, one_smul]
      rw [h1, norm_smul, Real.norm_eq_abs, mul_pow]
      have h2 : |deriv (cutoff n) (L x) - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [deriv_cutoff_nonneg n (L x), deriv_cutoff_le_one n (L x)]
      calc |deriv (cutoff n) (L x) - 1| ^ 2 * ‖ofDual μ L‖ ^ 2
          ≤ 1 ^ 2 * ‖ofDual μ L‖ ^ 2 := by gcongr
        _ ≤ 4 * ‖ofDual μ L‖ ^ 2 := by linarith [sq_nonneg ‖ofDual μ L‖]
    · rw [show (fun n ↦ mderiv μ (fun y ↦ cutoff n (L y)) x) =
          fun n ↦ deriv (cutoff n) (L x) • ofDual μ L from funext fun n ↦ hm n x]
      have := (tendsto_deriv_cutoff (L x)).smul_const (ofDual μ L)
      simpa using this
end Malliavin
