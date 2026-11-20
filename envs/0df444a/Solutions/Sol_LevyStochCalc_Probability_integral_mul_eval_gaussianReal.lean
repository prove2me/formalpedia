-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_mul_eval_gaussianReal
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:45:31.293699+00:00
-- url     : https://prove2.me/submissions/cb3acdd8-cc3a-4012-8614-4eba24c11fcc

import Definitions.Def_LevyStochCalc_Probability_GaussianMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of a centred real Gaussian and Gaussian integration by parts

For the law `gaussianReal 0 v` on `ℝ` the even moments are `E[X^(2n)] = v^n (2n-1)!!`, the odd
moments vanish, and the two are tied together by the recursion `E[X^(k+2)] = (k+1) v E[X^k]`.
Every polynomial function is integrable for this law, and the Stein identity
`E[X p(X)] = v E[p'(X)]` holds for every real polynomial `p`.

## Main statements

* `LevyStochCalc.Probability.integral_pow_even_gaussianReal` — `E[X^(2n)] = v^n (2n-1)!!`.
* `LevyStochCalc.Probability.integral_pow_odd_gaussianReal` — `E[X^(2n+1)] = 0`.
* `LevyStochCalc.Probability.integral_pow_add_two_gaussianReal` — `E[X^(k+2)] = (k+1) v E[X^k]`.
* `LevyStochCalc.Probability.integrable_eval_gaussianReal` — `p(X)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_gaussianReal` — `E[X p(X)] = v E[p'(X)]`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

variable (v : ℝ≥0)

theorem _root_.solution (p : ℝ[X]) :
    ∫ x, x * p.eval x ∂gaussianReal 0 v
      = (v : ℝ) * ∫ x, (derivative p).eval x ∂gaussianReal 0 v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, derivative_add, mul_add]
    have hI : ∀ r : ℝ[X], Integrable (fun x : ℝ => x * r.eval x) (gaussianReal 0 v) := fun r => by
      have h := integrable_eval_gaussianReal v (X * r)
      simp only [eval_mul, eval_X] at h
      exact h
    rw [integral_add (hI p) (hI q),
      integral_add (integrable_eval_gaussianReal v _) (integrable_eval_gaussianReal v _), hp, hq,
      mul_add]
  | monomial k c =>
    simp only [eval_monomial, derivative_monomial]
    have e1 : (fun x : ℝ => x * (c * x ^ k)) = fun x => c * x ^ (k + 1) := by
      funext x; ring
    rw [e1, integral_const_mul]
    rcases k with _ | k
    · simp only [zero_add, pow_one, Nat.cast_zero, mul_zero, zero_mul, Nat.sub_zero, pow_zero]
      have := integral_pow_odd_gaussianReal v 0
      simp only [mul_zero, zero_add, pow_one] at this
      simp [this]
    · rw [show k + 1 + 1 = k + 2 by ring, integral_pow_add_two_gaussianReal]
      simp only [Nat.add_sub_cancel]
      rw [integral_const_mul]
      push_cast
      ring

end LevyStochCalc.Probability
