-- Prove2me | solution 1 for LL_Decomp1528c.theta_ge_half_mid
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:39:27.425955+00:00
-- url     : https://prove2.me/submissions/c212e528-4f64-4224-86c2-4fc95140ff08

import Mathlib
open Real Finset Chebyshev

set_option maxHeartbeats 2000000

/-!
# `θ n ≥ (n+1)/2` for `1000 ≤ n < 10^4`

The Chebyshev function `θ` is compared with `ψ` through Mathlib's three-term
Costa–Pereira bound `ψ x - θ x ≤ ψ (√x) + ψ (x^{1/3}) + ψ (x^{1/5})`.
Each of the three `ψ` values is bounded by `ψ` at an integer (monotonicity of `ψ`)
and then by the explicit bound `ψ y ≤ y log 4 + 2√y log y`.
The remaining terms are controlled by explicit numerical bounds on `log`.
-/

/-! ## Numeric bounds on logs -/

lemma ll_log_four_le : Real.log 4 ≤ 1.386295 := by
  rw [Real.log_four_eq]
  linarith [Real.log_two_lt_d9]

lemma ll_log_five_le : Real.log 5 ≤ 1.609438 := by
  linarith [Real.log_five_lt_d9]

lemma ll_log_45_le : Real.log 45 ≤ 3.8067 := by
  have h : Real.log 45 = 2 * Real.log 3 + Real.log 5 := by
    rw [show (45 : ℝ) = 3 ^ 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  linarith [Real.log_three_lt_d9, Real.log_five_lt_d9]

lemma ll_log_13_le : Real.log 13 ≤ 2.7726 := by
  have h : Real.log 13 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_lt_d9]

lemma ll_log_22_le : Real.log 22 ≤ 3.4658 := by
  have h : Real.log 22 ≤ Real.log 32 := Real.log_le_log (by norm_num) (by norm_num)
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_lt_d9]

lemma ll_log_7_le : Real.log 7 ≤ 2.0795 := by
  have h : Real.log 7 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_lt_d9]

/-! ## Numeric upper bounds on `ψ` at small arguments -/

lemma ll_psi_45_le : ψ 45 ≤ 113.5 := by
  have h := Chebyshev.psi_le (x := 45) (by norm_num)
  have hs : Real.sqrt 45 ≤ 6.71 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 45), Real.sqrt_nonneg (45 : ℝ)]
  have hs0 : (0 : ℝ) ≤ Real.sqrt 45 := Real.sqrt_nonneg _
  have hl0 : (0 : ℝ) ≤ Real.log 45 := Real.log_nonneg (by norm_num)
  have hp : Real.sqrt 45 * Real.log 45 ≤ 6.71 * 3.8067 :=
    mul_le_mul hs ll_log_45_le hl0 (by norm_num)
  nlinarith [ll_log_four_le]

lemma ll_psi_13_le : ψ 13 ≤ 38.1 := by
  have h := Chebyshev.psi_le (x := 13) (by norm_num)
  have hs : Real.sqrt 13 ≤ 3.61 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13), Real.sqrt_nonneg (13 : ℝ)]
  have hl0 : (0 : ℝ) ≤ Real.log 13 := Real.log_nonneg (by norm_num)
  have hp : Real.sqrt 13 * Real.log 13 ≤ 3.61 * 2.7726 :=
    mul_le_mul hs ll_log_13_le hl0 (by norm_num)
  nlinarith [ll_log_four_le]

lemma ll_psi_5_le : ψ 5 ≤ 14.2 := by
  have h := Chebyshev.psi_le (x := 5) (by norm_num)
  have hs : Real.sqrt 5 ≤ 2.24 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg (5 : ℝ)]
  have hl0 : (0 : ℝ) ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hp : Real.sqrt 5 * Real.log 5 ≤ 2.24 * 1.609438 :=
    mul_le_mul hs ll_log_five_le hl0 (by norm_num)
  nlinarith [ll_log_four_le]

lemma ll_psi_100_le : ψ 100 ≤ 230.8 := by
  have h := Chebyshev.psi_le (x := 100) (by norm_num)
  have hs : Real.sqrt 100 = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs] at h
  have hl : Real.log 100 ≤ 4.6052 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
    linarith [Real.log_ten_eq, ll_log_five_le, Real.log_two_lt_d9]
  nlinarith [ll_log_four_le]

lemma ll_psi_22_le : ψ 22 ≤ 63.1 := by
  have h := Chebyshev.psi_le (x := 22) (by norm_num)
  have hs : Real.sqrt 22 ≤ 4.70 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22), Real.sqrt_nonneg (22 : ℝ)]
  have hl0 : (0 : ℝ) ≤ Real.log 22 := Real.log_nonneg (by norm_num)
  have hp : Real.sqrt 22 * Real.log 22 ≤ 4.70 * 3.4658 :=
    mul_le_mul hs ll_log_22_le hl0 (by norm_num)
  nlinarith [ll_log_four_le]

lemma ll_psi_7_le : ψ 7 ≤ 20.75 := by
  have h := Chebyshev.psi_le (x := 7) (by norm_num)
  have hs : Real.sqrt 7 ≤ 2.65 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7), Real.sqrt_nonneg (7 : ℝ)]
  have hl0 : (0 : ℝ) ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hp : Real.sqrt 7 * Real.log 7 ≤ 2.65 * 2.0795 :=
    mul_le_mul hs ll_log_7_le hl0 (by norm_num)
  nlinarith [ll_log_four_le]

/-! ## Fractional-power bounds -/

lemma ll_rpow_half_le {x : ℝ} (_hx : 0 ≤ x) : x ^ ((2 : ℝ))⁻¹ ≤ Real.sqrt x := by
  have h : ((2 : ℝ))⁻¹ = 1 / 2 := by norm_num
  rw [h, ← Real.sqrt_eq_rpow]

lemma ll_rpow_third_le {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hc0 : 0 ≤ c) (hc : x ≤ c ^ 3) :
    x ^ ((3 : ℝ))⁻¹ ≤ c := by
  calc x ^ ((3 : ℝ))⁻¹ ≤ (c ^ 3) ^ ((3 : ℝ))⁻¹ :=
        Real.rpow_le_rpow hx hc (by norm_num)
    _ = c := Real.pow_rpow_inv_natCast hc0 (by norm_num)

lemma ll_rpow_fifth_le {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hc0 : 0 ≤ c) (hc : x ≤ c ^ 5) :
    x ^ ((5 : ℝ))⁻¹ ≤ c := by
  calc x ^ ((5 : ℝ))⁻¹ ≤ (c ^ 5) ^ ((5 : ℝ))⁻¹ :=
        Real.rpow_le_rpow hx hc (by norm_num)
    _ = c := Real.pow_rpow_inv_natCast hc0 (by norm_num)

/-! ## The analytic bound on `[1000, 10^4)` -/

lemma ll_theta_ge_half_mid_nat (n : ℕ) (h1 : 1000 ≤ n) (h2 : n < 10 ^ 4) :
    ((n : ℝ) + 1) / 2 ≤ θ n := by
  have hn : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
  have hn4 : (n : ℝ) < 10 ^ 4 := by exact_mod_cast h2
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hpsi : (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) ≤ ψ (n : ℝ) :=
    Chebyshev.psi_ge n
  have hgap := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (x := (n : ℝ))
  have hlog2 := Real.log_two_gt_d9
  rcases lt_or_ge (n : ℝ) 2000 with hcase | hcase
  · -- range `[1000, 2000)`
    have hsq : Real.sqrt (n : ℝ) ≤ 45 := by
      have h : Real.sqrt (n : ℝ) ≤ Real.sqrt 2000 := Real.sqrt_le_sqrt (by linarith)
      have h2000 : Real.sqrt (2000 : ℝ) ≤ 45 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2000),
          Real.sqrt_nonneg (2000 : ℝ)]
      linarith
    have hhalf : (n : ℝ) ^ ((2 : ℝ))⁻¹ ≤ 45 :=
      le_trans (ll_rpow_half_le hn0) hsq
    have hthird : (n : ℝ) ^ ((3 : ℝ))⁻¹ ≤ 13 := by
      apply ll_rpow_third_le hn0 (by norm_num)
      nlinarith
    have hfifth : (n : ℝ) ^ ((5 : ℝ))⁻¹ ≤ 5 := by
      apply ll_rpow_fifth_le hn0 (by norm_num)
      nlinarith
    have hgapA : ψ (n : ℝ) - θ (n : ℝ) ≤ 165.8 := by
      have a : ψ ((n : ℝ) ^ ((2 : ℝ))⁻¹) ≤ ψ 45 := Chebyshev.psi_mono hhalf
      have b : ψ ((n : ℝ) ^ ((3 : ℝ))⁻¹) ≤ ψ 13 := Chebyshev.psi_mono hthird
      have c : ψ ((n : ℝ) ^ ((5 : ℝ))⁻¹) ≤ ψ 5 := Chebyshev.psi_mono hfifth
      linarith [ll_psi_45_le, ll_psi_13_le, ll_psi_5_le]
    have hlog : Real.log ((n : ℝ) + 1) ≤ 7.625 := by
      have ha : Real.log ((n : ℝ) + 1) ≤ Real.log 2001 := Real.log_le_log (by linarith) (by linarith)
      have hb : Real.log 2001 ≤ Real.log 2048 := Real.log_le_log (by norm_num) (by norm_num)
      have hc : Real.log 2048 = 11 * Real.log 2 := by
        rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
        norm_num
      linarith [Real.log_two_lt_d9]
    nlinarith
  · -- range `[2000, 10^4)`
    have hsq : Real.sqrt (n : ℝ) ≤ 100 := by
      have h : Real.sqrt (n : ℝ) ≤ Real.sqrt (10 ^ 4 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h100 : Real.sqrt (10 ^ 4 : ℝ) = 100 := by
        rw [show (10 ^ 4 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have hhalf : (n : ℝ) ^ ((2 : ℝ))⁻¹ ≤ 100 :=
      le_trans (ll_rpow_half_le hn0) hsq
    have hthird : (n : ℝ) ^ ((3 : ℝ))⁻¹ ≤ 22 := by
      apply ll_rpow_third_le hn0 (by norm_num)
      nlinarith
    have hfifth : (n : ℝ) ^ ((5 : ℝ))⁻¹ ≤ 7 := by
      apply ll_rpow_fifth_le hn0 (by norm_num)
      nlinarith
    have hgapB : ψ (n : ℝ) - θ (n : ℝ) ≤ 314.7 := by
      have a : ψ ((n : ℝ) ^ ((2 : ℝ))⁻¹) ≤ ψ 100 := Chebyshev.psi_mono hhalf
      have b : ψ ((n : ℝ) ^ ((3 : ℝ))⁻¹) ≤ ψ 22 := Chebyshev.psi_mono hthird
      have c : ψ ((n : ℝ) ^ ((5 : ℝ))⁻¹) ≤ ψ 7 := Chebyshev.psi_mono hfifth
      linarith [ll_psi_100_le, ll_psi_22_le, ll_psi_7_le]
    have hlog : Real.log ((n : ℝ) + 1) ≤ 9.705 := by
      have ha : Real.log ((n : ℝ) + 1) ≤ Real.log 10001 := Real.log_le_log (by linarith) (by linarith)
      have hb : Real.log 10001 ≤ Real.log 16384 := Real.log_le_log (by norm_num) (by norm_num)
      have hc : Real.log 16384 = 14 * Real.log 2 := by
        rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]
        norm_num
      linarith [Real.log_two_lt_d9]
    nlinarith

theorem solution (n : ℕ) (h1 : 1000 ≤ n) (h2 : n < 10 ^ 4) : ((n : ℝ) + 1) / 2 ≤ θ n :=
  ll_theta_ge_half_mid_nat n h1 h2
