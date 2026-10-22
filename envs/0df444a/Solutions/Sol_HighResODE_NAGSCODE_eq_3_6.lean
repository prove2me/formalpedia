-- Prove2me | solution 1 for HighResODE.NAGSCODE.eq_3_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:49:03.682871+00:00
-- url     : https://prove2.me/submissions/8b9720d6-f1a6-41e3-b88b-b936d1ef0892

import Mathlib
import Definitions.Def_HighResODE_NAGSCODE_Setting

set_option autoImplicit false

open HighResODE.NAGSCODE
open scoped InnerProductSpace

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ s : ℝ) (hμ : 0 ≤ μ) (hs : 0 ≤ s)
    (xs : EuclideanSpace ℝ (Fin n)) (X V : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    lyap f μ s xs X V t ≤ (1 + Real.sqrt (μ * s)) * (f (X t) - f xs) + ‖V t‖ ^ 2
      + 3 * μ * ‖X t - xs‖ ^ 2 + 3 * s / 4 * ‖gradient f (X t)‖ ^ 2 := by
  unfold lyap
  set a := ‖V t‖ with ha
  set b := ‖(2 * Real.sqrt μ) • (X t - xs)‖ with hb
  set c := ‖Real.sqrt s • gradient f (X t)‖ with hc
  have hb2 : b ^ 2 = 4 * μ * ‖X t - xs‖ ^ 2 := by
    rw [hb, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, mul_pow,
      Real.sq_sqrt hμ]
    ring
  have hc2 : c ^ 2 = s * ‖gradient f (X t)‖ ^ 2 := by
    rw [hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hs]
  have htri : ‖V t + (2 * Real.sqrt μ) • (X t - xs) + Real.sqrt s • gradient f (X t)‖ ≤ a + b + c := by
    calc _ ≤ ‖V t + (2 * Real.sqrt μ) • (X t - xs)‖ + ‖Real.sqrt s • gradient f (X t)‖ :=
          norm_add_le _ _
      _ ≤ (‖V t‖ + ‖(2 * Real.sqrt μ) • (X t - xs)‖) + ‖Real.sqrt s • gradient f (X t)‖ :=
          by linarith [norm_add_le (V t) ((2 * Real.sqrt μ) • (X t - xs))]
  have hnn : 0 ≤ ‖V t + (2 * Real.sqrt μ) • (X t - xs) + Real.sqrt s • gradient f (X t)‖ :=
    norm_nonneg _
  have hsq : ‖V t + (2 * Real.sqrt μ) • (X t - xs) + Real.sqrt s • gradient f (X t)‖ ^ 2
      ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h1 := pow_le_pow_left₀ hnn htri 2
    nlinarith [h1, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  nlinarith [hsq, hb2, hc2, Real.sqrt_nonneg (μ * s)]
