-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_hermitePoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:29:27.433979+00:00
-- url     : https://prove2.me/submissions/812e3f70-f64c-46aa-a769-708abdc24026

import Definitions.Def_LevyStochCalc_Probability_Hermite_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Hermite polynomials of variance `v` and their Gaussian orthogonality

The probabilists' Hermite polynomials of variance `v` are given by the Appell recursion
`H_(n+1) = (x - v d/dx) H_n`, which makes the derivative `H_(n+1)' = (n+1) H_n` and the three-term
recursion `H_(n+2) = x H_(n+1) - (n+1) v H_n` immediate. For `v > 0` they rescale Mathlib's
family `Polynomial.hermite` by `H_n(x; v) = √v ^ n * He_n(x / √v)`, and `H_2(x; v) = x ^ 2 - v`.
Under the law `gaussianReal 0 v` they are orthogonal, with `E[H_n H_m] = δ_(n m) n! v ^ n`.

The opening section adds the derivative and the three-term recursion of Mathlib's
`Polynomial.hermite`, both of which belong with `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`.

## Main statements

* `Polynomial.derivative_hermite` — `He_(n+1)' = (n+1) He_n`.
* `Polynomial.hermite_succ_succ` — `He_(n+2) = X He_(n+1) - (n+1) He_n`.
* `LevyStochCalc.Probability.derivative_hermitePoly` — `H_(n+1)' = (n+1) H_n`.
* `LevyStochCalc.Probability.hermitePoly_succ_succ` — `H_(n+2) = X H_(n+1) - (n+1) v H_n`.
* `LevyStochCalc.Probability.hermiteScaled_two` — `H_2(x; v) = x ^ 2 - v`.
* `LevyStochCalc.Probability.hermiteScaled_eq` — `H_n(x; v) = √v ^ n * He_n(x / √v)` for `v > 0`.
* `LevyStochCalc.Probability.integral_hermitePoly_mul` — `E[H_n H_m] = δ_(n m) n! v ^ n`.
-/

namespace Polynomial

end Polynomial

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

theorem AuxH_L (v : ℝ≥0) : ∀ (n : ℕ) (q : ℝ[X]),
    ∫ x, (hermitePoly (v : ℝ) n).eval x * q.eval x ∂gaussianReal 0 v
      = (v : ℝ) ^ n * ∫ x, (derivative^[n] q).eval x ∂gaussianReal 0 v
  | 0, q => by simp
  | n + 1, q => by
    have h := integral_hermite_step v (hermitePoly (v : ℝ) n) q
    have e : ∀ x : ℝ, (hermitePoly (v : ℝ) (n + 1)).eval x * q.eval x
        = (x * (hermitePoly (v : ℝ) n).eval x
            - (v : ℝ) * (derivative (hermitePoly (v : ℝ) n)).eval x) * q.eval x := by
      intro x; rw [hermitePoly_succ]; simp [eval_sub, eval_mul]
    simp_rw [e]
    rw [h, AuxH_L v n (derivative q), Function.iterate_succ_apply]
    ring

theorem AuxH_D (v : ℝ) : ∀ j : ℕ, derivative^[j] (hermitePoly v j) = C (j.factorial : ℝ)
  | 0 => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply, derivative_hermitePoly, iterate_derivative_C_mul,
      AuxH_D v j, ← C_mul, Nat.factorial_succ]
    push_cast
    ring_nf

theorem AuxH_Z (v : ℝ) (j k : ℕ) (hk : j < k) : derivative^[k] (hermitePoly v j) = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = r + (j + 1) := ⟨k - (j + 1), by omega⟩
  rw [Function.iterate_add_apply, Function.iterate_succ_apply', AuxH_D, derivative_C,
    iterate_derivative_zero]

theorem _root_.solution (v : ℝ≥0) (n m : ℕ) :
    ∫ x, (hermitePoly (v : ℝ) n).eval x * (hermitePoly (v : ℝ) m).eval x ∂gaussianReal 0 v
      = if n = m then (n.factorial : ℝ) * (v : ℝ) ^ n else 0 := by
  by_cases h : n = m
  · subst h
    rw [if_pos rfl, AuxH_L, AuxH_D]
    simp only [eval_C, integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · simp_rw [mul_comm ((hermitePoly (v : ℝ) n).eval _)]
      rw [AuxH_L, AuxH_Z _ _ _ hlt]
      simp
    · rw [AuxH_L, AuxH_Z _ _ _ hgt]
      simp

end LevyStochCalc.Probability
