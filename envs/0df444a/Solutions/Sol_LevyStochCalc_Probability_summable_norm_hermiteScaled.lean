-- Prove2me | solution 1 for LevyStochCalc.Probability.summable_norm_hermiteScaled
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:26:03.769682+00:00
-- url     : https://prove2.me/submissions/94d09e70-71c1-4067-8618-554dceb17964

import Definitions.Def_LevyStochCalc_Probability_HermiteGenerating_F000

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

theorem _root_.solution (τ x : ℝ) (t : ℂ) :
    Summable fun r : ℕ => ‖t ^ r / (r.factorial : ℂ) * (hermiteScaled r τ x : ℂ)‖ := by
  set f : ℕ → ℂ := fun a => (t * (x : ℂ)) ^ a / (a.factorial : ℂ) with hf_def
  set g : ℕ → ℂ := fun m => t ^ m / (m.factorial : ℂ) * (hermiteScaled m τ 0 : ℂ) with hg_def
  have hfn : Summable fun a => ‖f a‖ := summable_norm_expTerm (t * (x : ℂ))
  have hgn : Summable fun m => ‖g m‖ := summable_norm_hermiteScaled_zero τ t
  have hS := summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn
  refine hS.congr fun n => ?_
  congr 1
  have hterm : ∀ p : ℕ × ℕ, p ∈ antidiagonal n →
      f p.1 * g p.2
        = t ^ n * ((x : ℂ) ^ p.1 / (p.1.factorial : ℂ)
            * ((hermiteScaled p.2 τ 0 : ℂ) / (p.2.factorial : ℂ))) := by
    intro p hp
    have hn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    simp only [hf_def, hg_def]
    rw [← hn, pow_add, mul_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hreal := sum_antidiagonal_hermiteScaled τ x n
  have hcast : ∑ p ∈ antidiagonal n, ((x : ℂ) ^ p.1 / (p.1.factorial : ℂ)
      * ((hermiteScaled p.2 τ 0 : ℂ) / (p.2.factorial : ℂ)))
      = ((hermiteScaled n τ x / (n.factorial : ℝ) : ℝ) : ℂ) := by
    rw [← hreal]
    push_cast
    rfl
  rw [hcast]
  push_cast
  ring

end LevyStochCalc.Probability
