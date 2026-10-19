-- Prove2me | solution 1 for OAI.BackwardIntertwiners.bilateralWeight_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:06:38.554226+00:00
-- url     : https://prove2.me/submissions/10c99f17-ebbe-4123-8bfa-f2e174946d18

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean:L272-L285
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.bilateralWeight_quadratic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Theorems.Thm_OAI_BackwardIntertwiners_bilateralWeight_ratio
import Theorems.Thm_OAI_BackwardIntertwiners_halfSum_bounds

-- ---- from OAI.Analysis.BackwardIntertwiners.ExplicitWeights ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma residueCorrection_mono {t : ℕ → ℕ} (ht : ResidueBounds t) :
    Monotone (residueCorrection t) := by
  intro k l hkl
  by_cases hk : k = 0
  · simpa [hk, residueCorrection] using residueCorrection_nonneg t l
  have hl : l ≠ 0 := by omega
  have hq : weightBlock k ≤ weightBlock l := Nat.add_le_add_right (Nat.log_mono_right hkl) 1
  dsimp only [residueCorrection]
  rw [ite_eq_right hk, ite_eq_right hl]
  rcases hq.eq_or_lt with hq | hq
  · simp [hq, residueScale]
  · have hNN : 2 * residueScale k ≤ residueScale l := by
      dsimp [residueScale]
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hNk : (2 * residueScale k : ℝ) ≤ residueScale l := by exact_mod_cast hNN
    have htk : (t (weightBlock k) : ℝ) < residueScale k := by exact_mod_cast ht _
    have htl : (0:ℝ) ≤ t (weightBlock l) := Nat.cast_nonneg _
    linarith

lemma halfExponent_mono {t : ℕ → ℕ} (ht : ResidueBounds t) : Monotone (halfExponent t) := by
  intro k l hkl
  have hc := residueCorrection_mono ht hkl
  have hkl' : (k:ℝ) ≤ l := by exact_mod_cast hkl
  dsimp [halfExponent]
  linarith

lemma halfSum_quadratic {t : ℕ → ℕ} (ht : ResidueBounds t) :
    Tendsto (fun n : ℕ => halfSum t n / (n:ℝ)^2) atTop (𝓝 5) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hs : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have hz : Tendsto (fun n : ℕ => halfSum t n / (n:ℝ)^2 - 5) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => 5*(n:ℝ)⁻¹ + 400*(Real.sqrt (n:ℝ))⁻¹) ?_ ?_
      (by simpa using (hi.const_mul 5).add (hs.const_mul 400))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hh := (halfSum_bounds ht n).1
      have hdiv := (le_div_iff₀ (sq_pos_of_pos hn0)).mpr (show 5*(n:ℝ)^2 ≤ halfSum t n by nlinarith)
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hr0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn0
      have hr := Real.sq_sqrt hn0.le
      have hh := (halfSum_bounds ht n).2
      have he : (5*(n:ℝ)*((n:ℝ)+1) + 400*(n:ℝ)*Real.sqrt n) / (n:ℝ)^2 - 5 =
          5*(n:ℝ)⁻¹ + 400*(Real.sqrt (n:ℝ))⁻¹ := by
        field_simp
        nlinarith
      rw [← he]
      exact sub_le_sub_right (div_le_div_of_nonneg_right hh (sq_nonneg _)) 5
  simpa only [sub_add_cancel, zero_add] using hz.add_const 5

lemma bilateralWeight_antitone (t u : ℕ → ℕ) : Antitone (bilateralWeight t u) := by
  apply antitone_int_of_succ_le
  intro j
  have hr := bilateralWeight_ratio t u j
  have he : bilateralBeta t u j ≤ 1 := by
    rw [bilateralBeta, Real.exp_le_one_iff]
    have hh := bilateralExponent_nonneg t u j
    linarith
  exact (div_le_one (bilateralWeight_pos t u j)).mp (hr.le.trans he)

lemma halfSum_discreteConvex {t : ℕ → ℕ} (ht : ResidueBounds t) : DiscreteConvex (halfSum t) := by
  unfold DiscreteConvex
  simpa only [halfSum_succ, add_sub_cancel_left] using halfExponent_mono ht

lemma halfSum_root_bound {t : ℕ → ℕ} (ht : ResidueBounds t) {n : ℕ} (hn : 0 < n) :
    -halfSum t n / (n:ℝ) ≤ -5*(n:ℝ) := by
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  apply (div_le_iff₀ hn').mpr
  have hh := (halfSum_bounds ht n).1
  nlinarith

lemma bilateralWeight_roots_summable {t u : ℕ → ℕ} (ht : ResidueBounds t) (hu : ResidueBounds u) :
    Summable (fun j : ℤ => if j = 0 then (0:ℝ) else bilateralWeight t u j ^ (1/(j:ℝ))) := by
  have hs : Summable (fun n : ℕ => Real.exp (-5*(n:ℝ))) := by
    simpa only [mul_comm (-5:ℝ)] using Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-5:ℝ) < 0)
  apply Summable.of_nat_of_neg_add_one
  · apply hs.of_nonneg_of_le
    · intro n
      split_ifs
      · rfl
      · exact Real.rpow_nonneg (bilateralWeight_pos t u _).le _
    · intro n
      by_cases hn : n = 0
      · simp [hn]
      · rw [ite_eq_right (by exact_mod_cast hn), bilateralWeight_nat, ← Real.exp_mul]
        apply Real.exp_le_exp.mpr
        simpa only [mul_one_div, Int.cast_natCast] using halfSum_root_bound ht (Nat.pos_of_ne_zero hn)
  · have hs' : Summable (fun n : ℕ => Real.exp (-5*((n:ℝ)+1))) := by
      simpa only [mul_add, mul_one, Real.exp_add] using hs.mul_right (Real.exp (-5))
    apply hs'.of_nonneg_of_le
    · intro n
      split_ifs
      · rfl
      · exact Real.rpow_nonneg (bilateralWeight_pos t u _).le _
    · intro n
      have hj : -((n:ℤ)+1) = -((n+1:ℕ):ℤ) := by omega
      rw [hj, ite_eq_right (by omega), bilateralWeight_neg_nat, ← Real.exp_mul]
      apply Real.exp_le_exp.mpr
      have hb := halfSum_root_bound hu (Nat.zero_lt_succ n)
      convert hb using 1 <;>
        simp only [Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.succ_eq_add_one, inv_neg,
          div_eq_mul_inv, Nat.cast_add, Nat.cast_one] ; ring

lemma bilateralWeight_quadratic {t u : ℕ → ℕ} (ht : ResidueBounds t) (hu : ResidueBounds u) :
    QuadraticWeights (bilateralWeight t u) where
  positive := bilateralWeight_pos t u
  decreasing := bilateralWeight_antitone t u
  convex_negative := by
    simpa only [bilateralWeight_neg_nat, Real.log_exp] using halfSum_discreteConvex hu
  concave_positive := by
    simpa only [bilateralWeight_nat, Real.log_exp, neg_neg] using halfSum_discreteConvex ht
  root_sum := bilateralWeight_roots_summable ht hu
  quadratic := by
    refine ⟨5, ?_, ?_, ?_⟩
    · exact (Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num : (3:ℝ) ≠ 1)).trans (by norm_num)
    · simpa only [bilateralWeight_nat, Real.log_exp, neg_div] using (halfSum_quadratic ht).neg
    · simpa only [bilateralWeight_neg_nat, Real.log_exp] using halfSum_quadratic hu

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.bilateralWeight_quadratic := @_root_.OAI.BackwardIntertwiners.bilateralWeight_quadratic
