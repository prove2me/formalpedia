-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_scale_below_close
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:00:06.279165+00:00
-- url     : https://prove2.me/submissions/d22d4408-dd3c-45a2-af1e-512ed25f356a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

private theorem bernoulli_lower (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hfactor : 0 ≤ 1 - x := by linarith
      have hmul := mul_le_mul_of_nonneg_right ih hfactor
      have hquad : 0 ≤ (n : ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)
      rw [Nat.cast_succ]
      nlinarith [hmul, hquad]

theorem solution (n : ℕ) (hn : 0 < n) (S : ℝ) (hS : 0 < S) :
    ∃ R : ℝ, 0 < R ∧ R < S ∧ 2 * R ^ n > S ^ n := by
  let x : ℝ := 1 / (4 * (n : ℝ))
  let R : ℝ := S * (1 - x)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have hden : 0 < 4 * (n : ℝ) := by positivity
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hxlt : x < 1 := by
    dsimp [x]
    rw [div_lt_iff₀ hden]
    nlinarith [hnOne]
  have hx1 : x ≤ 1 := le_of_lt hxlt
  have hnx : (n : ℝ) * x = 1 / 4 := by
    dsimp [x]
    field_simp [ne_of_gt hnR]
  have hfac : 0 < 1 - x := by linarith
  have hRpos : 0 < R := by
    dsimp [R]
    exact mul_pos hS hfac
  have hRlt : R < S := by
    dsimp [R]
    nlinarith [mul_pos hS hx0]
  have hpower : (3 : ℝ) / 4 ≤ (1 - x) ^ n := by
    have h := bernoulli_lower n x (le_of_lt hx0) hx1
    rw [hnx] at h
    norm_num at h
    exact h
  have hRpow : R ^ n = S ^ n * (1 - x) ^ n := by
    dsimp [R]
    rw [mul_pow]
  have hSnp : 0 < S ^ n := pow_pos hS n
  have hscaled := mul_le_mul_of_nonneg_left hpower (le_of_lt hSnp)
  refine ⟨R, hRpos, hRlt, ?_⟩
  rw [hRpow]
  nlinarith [hscaled, hSnp]