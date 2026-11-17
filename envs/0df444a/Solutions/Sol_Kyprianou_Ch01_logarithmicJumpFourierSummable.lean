-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpFourierSummable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:27:16.839207+00:00
-- url     : https://prove2.me/submissions/56fbd669-febc-409f-8a22-cf59ada7e0be

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpWeightsHasSumOne
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

/-! Logarithmic jump series converges absolutely at every real frequency. -/
theorem solution
    (q xi : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun n : ℕ =>
      (((q ^ (n + 1) / ((n : ℝ) + 1)) /
        (-Real.log (1 - q))) : ℂ) *
        Complex.exp ((xi : ℂ) *
          (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I)) := by
  let w : ℕ → ℝ := fun n =>
    (q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))
  have hsum : Summable w :=
    (Kyprianou.Ch01.logarithmicJumpWeightsHasSumOne q hq0 hq1).summable
  have hlog : 0 < -Real.log (1 - q) := by
    have hp : 0 < 1 - q := sub_pos.mpr hq1
    have hl : 1 - q < 1 := sub_lt_self 1 hq0
    exact neg_pos.mpr (Real.log_neg hp hl)
  have hnonneg : ∀ n, 0 ≤ w n := by
    intro n
    dsimp [w]
    exact div_nonneg
      (div_nonneg (pow_nonneg (le_of_lt hq0) _) (by positivity))
      (le_of_lt hlog)
  have hs : Summable (fun n : ℕ =>
      (w n : ℂ) * Complex.exp
        ((xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I)) := by
    apply Summable.of_norm_bounded hsum
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg n)]
    have hnorm :
        ‖Complex.exp ((xi : ℂ) *
          (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    rw [hnorm]
    simp
  simpa only [w, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one] using hs
