-- Prove2me | solution 1 for Malliavin.coe_space_mem_domD12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:51.785949+00:00
-- url     : https://prove2.me/submissions/7ff54bfd-5d1a-400b-97f8-928fc28ee6ed

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
import Theorems.Thm_Malliavin_coeFn_dualLp
import Theorems.Thm_Malliavin_dualLp_mem_domD12
import Theorems.Thm_Malliavin_constOfDual_eq_constLp
import Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_denseRange_ofDual
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mderivClosure_toLp
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
theorem _root_.solution (h : Space μ) :
    (h : Lp ℝ 2 μ) ∈ domD12 μ ∧ mderivClosure μ (h : Lp ℝ 2 μ) = constLp μ h := by
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp (denseRange_ofDual μ h)
  choose L hL using hx
  -- `dualLp μ (L n)` differs from `ofDual μ (L n)` by the centering constant `L n (mean μ)`
  have hcenter : ∀ n, dualLp μ (L n) =
      (ofDual μ (L n) : Lp ℝ 2 μ) + Lp.const 2 μ (L n (mean μ)) := by
    intro n
    apply Lp.ext
    filter_upwards [coeFn_dualLp μ (L n), centeredDualToLp_ae_eq μ (L n),
      Lp.coeFn_add (ofDual μ (L n) : Lp ℝ 2 μ) (Lp.const 2 μ (L n (mean μ))),
      Lp.coeFn_const 2 μ (L n (mean μ))] with x h1 h2 h3 h4
    rw [h1, h3, Pi.add_apply, coe_ofDual, h2, h4]
    simp only [Function.const_apply, sub_add_cancel]
  -- the functional `dualLp μ (L n) - const` has the same derivative as `dualLp μ (L n)`
  have hmem : ∀ n, (ofDual μ (L n) : Lp ℝ 2 μ) ∈ domD12 μ ∧
      mderivClosure μ (ofDual μ (L n) : Lp ℝ 2 μ) = constLp μ (ofDual μ (L n)) := by
    intro n
    have hc : (Lp.const 2 μ (L n (mean μ)) : Lp ℝ 2 μ) ∈ domD12 μ ∧
        mderivClosure μ (Lp.const 2 μ (L n (mean μ))) = 0 := by
      have hsb := IsSmoothBounded.const (W := W) (L n (mean μ))
      have heq : hsb.toLp μ = Lp.const 2 μ (L n (mean μ)) := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hsb.memLp μ 2), Lp.coeFn_const 2 μ (L n (mean μ))]
          with x h1 h2
        rw [IsSmoothBounded.toLp, h1, h2]
        rfl
      refine ⟨heq ▸ hsb.toLp_mem_domD12 μ, ?_⟩
      rw [← heq, mderivClosure_toLp]
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (hsb.memLp_mderiv μ 2), Lp.coeFn_zero (Space μ) 2 μ]
        with x h1 h2
      rw [IsSmoothBounded.mderivLp, h1, h2, mderiv_const]
      rfl
    have hsub : (ofDual μ (L n) : Lp ℝ 2 μ) =
        dualLp μ (L n) + (-1 : ℝ) • Lp.const 2 μ (L n (mean μ)) := by
      rw [hcenter n, neg_one_smul, add_neg_cancel_right]
    have hc' : ((-1 : ℝ) • Lp.const 2 μ (L n (mean μ)) : Lp ℝ 2 μ) ∈ domD12 μ :=
      Submodule.smul_mem (D12 μ) _ hc.1
    rw [hsub]
    refine ⟨Submodule.add_mem (D12 μ) (dualLp_mem_domD12 μ (L n)).1 hc', ?_⟩
    rw [mderivClosure_add μ (dualLp_mem_domD12 μ (L n)).1 hc', mderivClosure_smul μ hc.1,
      (dualLp_mem_domD12 μ (L n)).2, hc.2, smul_zero, add_zero, constOfDual_eq_constLp]
  refine mem_domD12_of_tendsto μ (F := fun n ↦ (ofDual μ (L n) : Lp ℝ 2 μ))
    (fun n ↦ (hmem n).1) ?_ ?_
  · have : Tendsto (fun n ↦ ((x n : Space μ) : Lp ℝ 2 μ)) atTop (𝓝 (h : Lp ℝ 2 μ)) :=
      (continuous_subtype_val.tendsto h).comp hlim
    refine this.congr fun n ↦ ?_
    rw [← hL n]
  · simp_rw [(hmem _).2]
    have := ((constLp μ).continuous.tendsto h).comp hlim
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, ← hL n]
end Malliavin
