-- Prove2me | solution 1 for LevyStochCalc.Probability.summable_norm_charlierScaled
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:27:37.237966+00:00
-- url     : https://prove2.me/submissions/294761b6-74ba-4cbc-9d69-63e65b3fa2e7

import Definitions.Def_LevyStochCalc_Probability_Charlier_F001
import Definitions.Def_LevyStochCalc_Probability_Charlier_F002
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generating function of the Charlier polynomials

At a natural argument `n` the Charlier polynomials with parameter `lam` (the mean of the Poisson
law that makes them orthogonal) are generated over `ℂ` by
`e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)`, obtained by induction on `n`: the value
`C_s(0; lam) = (-lam) ^ s` matches the exponential series at `n = 0`, and the forward difference
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)` turns the step into an index shift, which on the
generating side multiplies by `1 + t`. The same induction, run on the bound
`|T_(s+1)(n + 1)| ≤ |T_(s+1)(n)| + |t| |T_s(n)|` for the terms `T_s(n) = (t ^ s / s!) C_s(n; lam)`
and started from the exponential series at `n = 0`, shows that the series is absolutely summable
at every natural argument.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_zero_arg` — `C_s(0; lam) = (-lam) ^ s`.
* `LevyStochCalc.Probability.hasSum_charlierScaled` —
  `e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_charlierScaled` — absolute summability of
  `t ^ s / s! · C_s(n; lam)` at every natural argument.
-/

namespace LevyStochCalc.Probability

open Finset

theorem AuxC_diff (lam : ℝ) : ∀ (s : ℕ) (x : ℝ),
    charlierScaled (s + 1) lam (x + 1) - charlierScaled (s + 1) lam x =
      ((s : ℝ) + 1) * charlierScaled s lam x := by
  intro s
  induction s with
  | zero => intro x; simp
  | succ s ih =>
    intro x
    have h1 := ih x
    have h2 := ih (x - 1)
    rw [sub_add_cancel] at h2
    have h3 := charlierScaled_succ s lam x
    have e1 := charlierScaled_succ (s + 1) lam (x + 1)
    have e2 := charlierScaled_succ (s + 1) lam x
    rw [add_sub_cancel_right] at e1
    push_cast
    linear_combination e1 - e2 - lam * h1 + x * h2 - ((s : ℝ) + 1) * h3

theorem _root_.solution (lam : ℝ) (n : ℕ) (t : ℂ) :
    Summable fun s : ℕ => ‖t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ)‖ := by
  induction n with
  | zero =>
    have h0 : ∀ s : ℕ, charlierScaled s lam 0 = (-lam) ^ s := by
      intro s
      induction s with
      | zero => simp
      | succ s ih => rw [charlierScaled_succ, ih]; ring
    simp only [Nat.cast_zero, h0]
    refine (Real.summable_pow_div_factorial (‖t‖ * |lam|)).congr fun s => ?_
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    push_cast
    rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    ring
  | succ n ih =>
    rw [← summable_nat_add_iff 1]
    have ih1 := (summable_nat_add_iff 1).mpr ih
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun s => ?_) (ih1.add (ih.mul_left ‖t‖))
    have hd := AuxC_diff lam s n
    have hf : ((s + 1).factorial : ℂ) = ((s : ℂ) + 1) * (s.factorial : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hs0 : ((s : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
    have hfs : (s.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero s)
    have heq : t ^ (s + 1) / ((s + 1).factorial : ℂ) *
        (charlierScaled (s + 1) lam ((n + 1 : ℕ) : ℝ) : ℂ) =
        t ^ (s + 1) / ((s + 1).factorial : ℂ) * (charlierScaled (s + 1) lam (n : ℝ) : ℂ) +
          t * (t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ)) := by
      have hc : charlierScaled (s + 1) lam ((n + 1 : ℕ) : ℝ) =
          charlierScaled (s + 1) lam (n : ℝ) + ((s : ℝ) + 1) * charlierScaled s lam (n : ℝ) := by
        push_cast; linarith
      rw [hc, hf]
      push_cast
      field_simp
      ring
    show ‖t ^ (s + 1) / ((s + 1).factorial : ℂ) *
        (charlierScaled (s + 1) lam ((n + 1 : ℕ) : ℝ) : ℂ)‖ ≤ _
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul t]

end LevyStochCalc.Probability
