-- Prove2me | solution 1 for Malliavin.brownianLp_half_notMem_closure_span_unitIncrementLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:02.739161+00:00
-- url     : https://prove2.me/submissions/ed323655-002c-448f-ba1f-555d1748124e

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
import Theorems.Thm_Malliavin_inner_brownianLp_unitIncrementLp
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
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) :
    brownianLp hB (1 / 2) ∉
      (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure := by
  intro hmem
  set x := brownianLp hB (1 / 2) with hx
  set e₀ := unitIncrementLp hB 0 with he₀
  -- inner products of `x` with the unit increments
  have hx0 : ⟪x, e₀⟫_ℝ = 1 / 2 := by
    rw [hx, he₀, inner_brownianLp_unitIncrementLp]
    norm_num
  have hxk : ∀ k : ℕ, 1 ≤ k → ⟪x, unitIncrementLp hB k⟫_ℝ = 0 := by
    intro k hk
    rw [hx, inner_brownianLp_unitIncrementLp]
    have h1 : ((1 / 2 : ℝ≥0) : ℝ) ≤ k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      norm_num
      linarith
    rw [min_eq_left (h1.trans (by linarith)), min_eq_left h1, sub_self]
  -- the unit increments are orthonormal
  have hee : ∀ k : ℕ, ⟪e₀, unitIncrementLp hB k⟫_ℝ = if k = 0 then 1 else 0 := by
    intro k
    have h0 : e₀ = brownianLp hB ((0 : ℕ) + 1) - brownianLp hB (0 : ℕ) := rfl
    rw [h0, inner_sub_left, inner_brownianLp_unitIncrementLp, inner_brownianLp_unitIncrementLp]
    push_cast
    simp only [zero_add]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [if_neg hk.ne', min_eq_left (by linarith), min_eq_left h1, min_eq_left (by linarith),
        min_eq_left (by linarith)]
      ring
  -- `y := x - (1/2) e₀` lies in the closed span and is orthogonal to every generator
  set y := x - (1 / 2 : ℝ) • e₀ with hy
  have hymem : y ∈ (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure :=
    Submodule.sub_mem _ hmem (Submodule.smul_mem _ _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨0, rfl⟩)))
  have hyk : ∀ k : ℕ, ⟪y, unitIncrementLp hB k⟫_ℝ = 0 := by
    intro k
    rw [hy, inner_sub_left, real_inner_smul_left, hee]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [if_pos rfl, ← he₀, hx0]
      ring
    · rw [if_neg hk.ne', hxk k hk]
      ring
  have hyorth : y ∈ (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal']
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨k, rfl⟩ := hu
      exact hyk k
    | zero => simp only [inner_zero_right]
    | add u v _ _ hu hv => rw [inner_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [real_inner_smul_right, hu, mul_zero]
  -- hence `y = 0`, so `x = (1/2) e₀`, contradicting `‖x‖² = 1/2`
  have hy0 : y = 0 := by
    rw [Submodule.mem_orthogonal] at hyorth
    exact inner_self_eq_zero.mp (hyorth y hymem)
  have hxx : ⟪x, x⟫_ℝ = 1 / 2 := by
    rw [hx, inner_brownianLp]
    norm_num
  have hx' : x = (1 / 2 : ℝ) • e₀ := by
    rw [hy] at hy0
    exact sub_eq_zero.mp hy0
  have he₀e₀ : ⟪e₀, e₀⟫_ℝ = 1 := by
    have := hee 0
    rwa [if_pos rfl, ← he₀] at this
  rw [hx', real_inner_smul_left, real_inner_smul_right, he₀e₀] at hxx
  norm_num at hxx
end Malliavin
