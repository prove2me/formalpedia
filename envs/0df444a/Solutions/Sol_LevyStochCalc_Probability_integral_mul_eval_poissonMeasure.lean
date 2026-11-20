-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_mul_eval_poissonMeasure
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:11:01.474198+00:00
-- url     : https://prove2.me/submissions/c4bc6a4a-6f44-45a7-b92a-d4926392ebc0

import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a Poisson law and Poisson integration by parts

The law `poissonMeasure r` on `ℕ` gives the atom `n` the mass `exp (-r) * r ^ n / n !`, so it is
the Poisson law of mean `r`. Every polynomial function is integrable for it, and the Stein
identity `E[N p(N)] = r E[p(N + 1)]` holds for every real polynomial `p`, with the forward shift
in place of the derivative of the Gaussian identity. Mean and variance are both `r`, the
factorial moments are `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`, the third central moment is `r` and
the fourth central moment is `3 r ^ 2 + r`. The identity has moments of every finite order.

## Main statements

* `LevyStochCalc.Probability.integrable_eval_poissonMeasure` — `p(N)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_poissonMeasure` — `E[N p(N)] = r E[p(N + 1)]`.
* `LevyStochCalc.Probability.integral_id_poissonMeasure` — `E[N] = r`.
* `LevyStochCalc.Probability.integral_id_sq_poissonMeasure` — `E[N ^ 2] = r ^ 2 + r`.
* `LevyStochCalc.Probability.integral_sub_sq_poissonMeasure` — `E[(N - r) ^ 2] = r`.
* `LevyStochCalc.Probability.integral_descPochhammer_eval_poissonMeasure` — the factorial
  moments `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`.
* `LevyStochCalc.Probability.integral_sub_pow_three_poissonMeasure` — `E[(N - r) ^ 3] = r`.
* `LevyStochCalc.Probability.integral_sub_pow_four_poissonMeasure` —
  `E[(N - r) ^ 4] = 3 r ^ 2 + r`.
* `LevyStochCalc.Probability.memLp_natCast_poissonMeasure` — `N ∈ Lᵖ` for every finite `p`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat



theorem _root_.solution (r : ℝ≥0) (p : ℝ[X]) :
    ∫ n : ℕ, (n : ℝ) * p.eval (n : ℝ) ∂poissonMeasure r
      = (r : ℝ) * ∫ n : ℕ, p.eval ((n : ℝ) + 1) ∂poissonMeasure r := by
  have hint : Integrable (fun n : ℕ => (n : ℝ) * p.eval (n : ℝ)) (poissonMeasure r) := by
    refine (integrable_eval_poissonMeasure r (Polynomial.X * p)).congr (ae_of_all _ fun n => ?_)
    show Polynomial.eval (n : ℝ) (Polynomial.X * p) = (n : ℝ) * Polynomial.eval (n : ℝ) p
    rw [Polynomial.eval_mul, Polynomial.eval_X]
  have hs := (hasSum_integral_poissonMeasure hint).summable
  rw [integral_poissonMeasure, integral_poissonMeasure, hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [smul_eq_mul, Nat.cast_zero, zero_mul, mul_zero, zero_add]
  refine tsum_congr fun n => ?_
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
