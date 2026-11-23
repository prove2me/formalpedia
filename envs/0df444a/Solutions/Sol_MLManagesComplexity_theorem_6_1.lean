-- Prove2me | solution 1 for MLManagesComplexity.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:50:55.27168+00:00
-- url     : https://prove2.me/submissions/06f9ccc1-3501-4294-8cd0-f89f1b0fd39d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MLManagesComplexity_PPolyComputable
import Definitions.Def_MLManagesComplexity_PolyMaxEntropy
import Definitions.Def_MLManagesComplexity_CompIndist
import Theorems.Thm_MLManagesComplexity_logLoss_range_and_distinguisher
import Theorems.Thm_MLManagesComplexity_acceptance_gap

set_option autoImplicit false

open AutoregressiveCompression.Main MLManagesComplexity

private lemma negligible_poly_mul {ν₀ : ℕ → ℝ} (hν₀ : Negligible ν₀) (c : ℕ) :
    Negligible (fun n : ℕ => ((n : ℝ) + 2) ^ c * (ν₀ n + 2 * (2 : ℝ) ^ (-(n : ℝ)))) := by
  intro k
  have h_add2 : ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ) + 2) ^ c ≤ (2 : ℝ) ^ c * (n : ℝ) ^ c := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hn_real : (2 : ℝ) ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
    have hle : (n : ℝ) + 2 ≤ 2 * (n : ℝ) := by linarith
    calc
      ((n : ℝ) + 2) ^ c ≤ (2 * (n : ℝ)) ^ c := pow_le_pow_left₀ (by positivity) hle c
      _ = (2 : ℝ) ^ c * (n : ℝ) ^ c := mul_pow 2 (n : ℝ) c
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ k * (((n : ℝ) + 2) ^ c * ν₀ n))
      Filter.atTop (nhds 0) := by
    have h_upper : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ c * |(n : ℝ) ^ (k + c) * ν₀ n|)
        Filter.atTop (nhds 0) := by
      simpa using (hν₀ (k + c)).abs.const_mul ((2 : ℝ) ^ c)
    refine squeeze_zero_norm' ?_ h_upper
    filter_upwards [h_add2] with n hn
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ k),
        abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) + 2) ^ c)]
    calc
      (n : ℝ) ^ k * (((n : ℝ) + 2) ^ c * |ν₀ n|)
          ≤ (n : ℝ) ^ k * (((2 : ℝ) ^ c * (n : ℝ) ^ c) * |ν₀ n|) := by
            gcongr
      _ = (2 : ℝ) ^ c * ((n : ℝ) ^ (k + c) * |ν₀ n|) := by
            rw [pow_add]
            ring
      _ = (2 : ℝ) ^ c * |(n : ℝ) ^ (k + c) * ν₀ n| := by
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ (k + c))]
  have h2 : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ k * (((n : ℝ) + 2) ^ c * (2 * (2 : ℝ) ^ (-(n : ℝ)))))
      Filter.atTop (nhds 0) := by
    have hexp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (k + c) / (2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_const_div_const_pow_of_one_lt (k + c) (by norm_num : (1 : ℝ) < 2)
    have h_upper : Filter.Tendsto
        (fun n : ℕ => (2 * (2 : ℝ) ^ c) * ((n : ℝ) ^ (k + c) / (2 : ℝ) ^ n))
        Filter.atTop (nhds 0) := by
      simpa using hexp.const_mul (2 * (2 : ℝ) ^ c)
    refine squeeze_zero_norm' ?_ h_upper
    filter_upwards [h_add2] with n hn
    have hrpow : (2 : ℝ) ^ (-(n : ℝ)) = ((2 : ℝ) ^ n)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    rw [hrpow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      (n : ℝ) ^ k * (((n : ℝ) + 2) ^ c * (2 * ((2 : ℝ) ^ n)⁻¹))
          ≤ (n : ℝ) ^ k * (((2 : ℝ) ^ c * (n : ℝ) ^ c) * (2 * ((2 : ℝ) ^ n)⁻¹)) := by
            gcongr
      _ = (2 * (2 : ℝ) ^ c) * ((n : ℝ) ^ (k + c) / (2 : ℝ) ^ n) := by
            rw [pow_add, div_eq_mul_inv]
            ring
  have hsum := h1.add h2
  simpa [mul_add] using hsum

theorem solution (D D' : DistFamily) (hDD' : CompIndist D D') (μ : DistFamily)
    (hμ : PPolyComputable μ) (hmax : PolyMaxEntropy μ) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ n : ℕ, |expectation (D n) (logLoss μ n) - expectation (D' n) (logLoss μ n)| ≤ ν n := by
  obtain ⟨c, _, A, hApoly, hAapprox⟩ := logLoss_range_and_distinguisher μ hμ hmax
  obtain ⟨ν₀, hν₀_negl, hν₀_bound⟩ := hDD' A hApoly
  refine ⟨fun n : ℕ => ((n : ℝ) + 2) ^ c * (ν₀ n + 2 * (2 : ℝ) ^ (-(n : ℝ))),
    negligible_poly_mul hν₀_negl c, fun n => ?_⟩
  let K : ℝ := ((n : ℝ) + 2) ^ c
  let ε : ℝ := (2 : ℝ) ^ (-(n : ℝ))
  have hK : 0 < K := by positivity
  have hε : 0 ≤ ε := by positivity
  have hgap := acceptance_gap (A n) K ε hK hε (logLoss μ n) (D n) (D' n) (hAapprox n)
  have h_invK : (1 / K) * |expectation (D n) (logLoss μ n) - expectation (D' n) (logLoss μ n)|
      ≤ ν₀ n + 2 * ε := by
    have h1 := (abs_le.mp hgap).1
    have h2 := hν₀_bound n
    linarith
  have h_mul := mul_le_mul_of_nonneg_left h_invK (le_of_lt hK)
  have h_lhs : K * ((1 / K) * |expectation (D n) (logLoss μ n) - expectation (D' n) (logLoss μ n)|)
      = |expectation (D n) (logLoss μ n) - expectation (D' n) (logLoss μ n)| := by
    field_simp [ne_of_gt hK]
  rw [h_lhs] at h_mul
  exact h_mul
