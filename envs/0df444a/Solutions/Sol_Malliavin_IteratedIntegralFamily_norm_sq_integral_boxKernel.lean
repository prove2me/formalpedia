-- Prove2me | solution 1 for Malliavin.IteratedIntegralFamily.norm_sq_integral_boxKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:35.471005+00:00
-- url     : https://prove2.me/submissions/5b78c53f-eb56-48b4-822c-7957b0482671

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_measurableSet_simplex
import Theorems.Thm_Malliavin_mem_simplex
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
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
namespace IteratedIntegralFamily
theorem _root_.solution (J : IteratedIntegralFamily P)
    {n : ℕ} (u v : Fin n → ℝ≥0) (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    ‖J.integral n (boxKernel u v)‖ ^ 2 = ∏ i, ((v i : ℝ) - u i) := by
  rw [← real_inner_self_eq_norm_sq, J.sameOrder]
  have hsubset : orderedBox u v ⊆ simplex ℝ≥0 n := by
    intro t ht
    rw [mem_simplex]
    intro i j hij
    have hit : t i ∈ Set.Ioc (u i) (v i) := ht i (Set.mem_univ i)
    have hjt : t j ∈ Set.Ioc (u j) (v j) := ht j (Set.mem_univ j)
    exact lt_of_le_of_lt (hit.2.trans (hord i j hij)) hjt.1
  have hcoe :
      (boxKernel u v : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
        (orderedBox u v).indicator (fun _ ↦ (1 : ℝ)) :=
    indicatorConstLp_coeFn
  calc
    (∫ t in simplex ℝ≥0 n,
        inner ℝ (boxKernel u v t) (boxKernel u v t) ∂iteratedKernelMeasure n) =
        ∫ t in simplex ℝ≥0 n, boxKernel u v t ∂iteratedKernelMeasure n := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hcoe] with t ht
      rw [ht]
      by_cases hmem : t ∈ orderedBox u v
      · simp only [Set.indicator_of_mem hmem, RCLike.inner_apply, conj_trivial, one_mul]
      · simp only [Set.indicator_of_notMem hmem, RCLike.inner_apply, conj_trivial, zero_mul]
    _ = (iteratedKernelMeasure n).real (orderedBox u v ∩ simplex ℝ≥0 n) := by
      unfold boxKernel
      rw [setIntegral_indicatorConstLp (measurableSet_simplex n)]
      simp only [smul_eq_mul, mul_one]
    _ = (iteratedKernelMeasure n).real (orderedBox u v) := by
      rw [Set.inter_eq_left.mpr hsubset]
    _ = ∏ i, ((v i : ℝ) - u i) := by
      rw [measureReal_def, orderedBox, iteratedKernelMeasure, Measure.pi_pi,
        ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [nonnegativeLebesgueMeasure_Ioc, ENNReal.toReal_ofReal]
      exact sub_nonneg.mpr (by exact_mod_cast huv i)
end IteratedIntegralFamily
end Malliavin
