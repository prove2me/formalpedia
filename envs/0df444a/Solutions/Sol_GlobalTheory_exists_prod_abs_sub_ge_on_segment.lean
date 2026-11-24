-- Prove2me | solution 1 for GlobalTheory.exists_prod_abs_sub_ge_on_segment
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:55.758072+00:00
-- url     : https://prove2.me/submissions/948ddd0d-caae-4b45-93e4-050557f68799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsProdAbsSubGeOnSegment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution : ∀ (N : ℕ) (x : Fin N → ℝ) (a δ : ℝ), 0 < δ →
    ∃ r : ℝ, a ≤ r ∧ r ≤ a + δ ∧ (δ / (2 * Real.exp 1)) ^ N ≤ ∏ i, |r - x i| := by
  intro N x a δ hδ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨a, le_rfl, by linarith, by simp⟩
  by_contra hcon
  push Not at hcon
  have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  set m : ℝ := δ / (2 * Real.exp 1) with hm
  have hm0 : 0 < m := by positivity
  let P : ℝ[X] := ∏ i : Fin N, (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
  have hlc : P.leadingCoeff = Real.exp 1 ^ N := by
    simp only [P, leadingCoeff_prod, leadingCoeff_linear he0.ne']
    simp
  have hdeg : P.degree ≤ N := by
    have : P.degree = ∑ _i : Fin N, (1 : WithBot ℕ) := by
      simp only [P, degree_prod, degree_linear he0.ne']
    rw [this]; simp
  have hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1 := by
    intro t ht
    have h1 := hcon (a + δ / 2 + δ / 2 * t) (by nlinarith [ht.1]) (by nlinarith [ht.2])
    have h2 : |P.eval t| = (∏ i, |a + δ / 2 + δ / 2 * t - x i|) / m ^ N := by
      simp only [P, eval_prod, Finset.abs_prod]
      have : ∀ i : Fin N, |eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))|
          = |a + δ / 2 + δ / 2 * t - x i| / m := by
        intro i
        have : eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
            = (a + δ / 2 + δ / 2 * t - x i) / m := by
          simp only [eval_add, eval_mul, eval_C, eval_X, hm]
          field_simp
          ring
        rw [this, abs_div, abs_of_pos hm0]
      simp only [this, Finset.prod_div_distrib]
      simp
    rw [h2, div_le_one (by positivity)]
    exact h1.le
  have h3 := Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdeg hb
  rw [hlc] at h3
  have h4 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h5 : (2 : ℝ) ^ N < Real.exp 1 ^ N := pow_lt_pow_left₀ he (by norm_num) hN.ne'
  linarith
end GlobalTheory
