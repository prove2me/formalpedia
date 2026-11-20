-- Prove2me | solution 1 for LevyStochCalc.Probability.sum_antidiagonal_div_factorial
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:25:17.267897+00:00
-- url     : https://prove2.me/submissions/79c4a355-fc80-4c67-af26-51e0b52ba9d3

import Definitions.Def_LevyStochCalc_Probability_HermiteGenerating_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generating function of the Hermite polynomials of variance `τ`

The Hermite polynomials of variance `τ` are generated over `ℂ` by
`e^(t x - t ^ 2 τ / 2) = ∑_r (t ^ r / r!) H_r(x; τ)`, which follows from the Appell binomial
decomposition `H_n(x; τ) / n! = ∑_(a + m = n) (x ^ a / a!) (H_m(0; τ) / m!)` by an antidiagonal
Cauchy product of the exponential series with the series of the values at the origin, the latter
summing to `e^(-t ^ 2 τ / 2)` because `H_(2b)(0; τ) = (-τ / 2) ^ b (2b)! / b!` and
`H_(2b+1)(0; τ) = 0`. A complex scalar covers the purely imaginary frequencies `t = i a`, where
the identity reads `e^(i a x + a ^ 2 τ / 2) = ∑_r ((i a) ^ r / r!) H_r(x; τ)`. Both factors of
the Cauchy product are absolutely summable, hence so is the scaled Hermite series itself, at
every argument and every complex scalar.

## Main statements

* `LevyStochCalc.Probability.hermiteScaled_two_mul_zero` —
  `H_(2b)(0; τ) = (-τ / 2) ^ b (2b)! / b!`.
* `LevyStochCalc.Probability.hermiteScaled_two_mul_add_one_zero` — `H_(2b+1)(0; τ) = 0`.
* `LevyStochCalc.Probability.sum_antidiagonal_hermiteScaled` — the Appell binomial identity
  `H_n(x; τ) / n! = ∑_(a + m = n) (x ^ a / a!) (H_m(0; τ) / m!)`.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_zero` —
  `e^(-t ^ 2 τ / 2) = ∑_m (t ^ m / m!) H_m(0; τ)`.
* `LevyStochCalc.Probability.hasSum_hermiteScaled` —
  `e^(t x - t ^ 2 τ / 2) = ∑_r (t ^ r / r!) H_r(x; τ)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_expTerm` — absolute summability of `z ^ a / a!`.
* `LevyStochCalc.Probability.summable_norm_hermiteScaled_zero` — absolute summability of
  `t ^ m / m! · H_m(0; τ)`.
* `LevyStochCalc.Probability.summable_norm_hermiteScaled` — absolute summability of
  `t ^ r / r! · H_r(x; τ)` at every argument.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_real` — the same identity for a real scalar.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_I` —
  `e^(i a x + a ^ 2 τ / 2) = ∑_r ((i a) ^ r / r!) H_r(x; τ)`.
* `LevyStochCalc.Probability.sum_antidiagonal_div_factorial` —
  `∑_(r + s = d) A ^ r B ^ s / (r! s!) = (A + B) ^ d / d!`.
-/

namespace LevyStochCalc.Probability

open Finset

theorem _root_.solution {K : Type*} [Field K] [CharZero K] (A B : K) (d : ℕ) :
    ∑ p ∈ antidiagonal d, A ^ p.1 * B ^ p.2 / ((p.1.factorial : K) * (p.2.factorial : K))
      = (A + B) ^ d / (d.factorial : K) := by
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)), Finset.sum_mul, add_pow,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => A ^ i * B ^ j / ((i.factorial : K) * (j.factorial : K)) * (d.factorial : K))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.cast_choose K hi']
  have h1 : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((d - i).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

end LevyStochCalc.Probability
