-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_coeff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:44:55.531431+00:00
-- url     : https://prove2.me/submissions/073a0a3c-6ff3-4df5-b8ea-1a605cd5d7fe

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_bound_explicit_degree_weights
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_product_pow_coeff_ne_zero_degree_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i))
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1)
    (hτs : ∀ i n, n < T i → PowerSeries.coeff n (τ i) = 0) :
    ‖RowTranslation.rowScalar ε τ β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  by_cases hz : PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ)) = 0
  · simp [RowTranslation.rowScalar, hz, Real.exp_nonneg]
  have hdegree : ∑ i, T i * (e i : ℕ) ≤ k :=
    OAI.PiExponent.LiteralAnalytic.product_pow_coeff_ne_zero_degree_bound
      τ T (fun i => (e i : ℕ)) k hτs hz
  have hdegreeR : (∑ i, (T i : ℝ) * (e i : ℕ)) ≤ (k : ℝ) := by
    exact_mod_cast hdegree
  have hsize : (∑ i, (a i : ℝ)) ≤ H / ws := by
    apply (le_div_iff₀ hws).2
    calc
      (∑ i, (a i : ℝ)) * ws = ∑ i, ws * (a i : ℝ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ MatrixTranslationBounds.weight w (fun i => a i) := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
      _ ≤ H := ha
  have hweighted :
      F * MatrixTranslationBounds.weight w (fun i => (e i : ℕ)) ≤
        v * (∑ i, (T i : ℝ) * (e i : ℕ)) := by
    unfold MatrixTranslationBounds.weight
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hm := mul_le_mul_of_nonneg_right (hTw i)
      (Nat.cast_nonneg (e i : ℕ) : (0 : ℝ) ≤ (e i : ℕ))
    simpa only [mul_assoc] using hm
  have hkv : v * (k : ℝ) ≤ H := by
    have hh := (le_div_iff₀ hv).mp hk
    nlinarith
  have hbudget : MatrixTranslationBounds.weight w (fun i => (e i : ℕ)) ≤ H / F := by
    apply (le_div_iff₀ hF).2
    have hh := hweighted.trans (mul_le_mul_of_nonneg_left hdegreeR hv.le)
    nlinarith [hh.trans hkv]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4C : 0 ≤ Real.log 4 + C :=
    add_nonneg (Real.log_nonneg (by norm_num)) hC
  have heterm := mul_le_mul_of_nonneg_left hbudget hν
  have haterm := mul_le_mul_of_nonneg_left hsize hlog4C
  have hkterm := mul_le_mul_of_nonneg_left hk hlog2
  apply (OAI.PiExponent.LiteralAnalytic.rowScalar_exp_bound_explicit_degree_weights
    ε τ β a e k w C ν hC hε hτc).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ -ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * (H / F) + (Real.log 4 + C) * (H / ws) + Real.log 2 * (H / v) := by
      linarith [heterm, haterm, hkterm]
    _ = _ := by ring
