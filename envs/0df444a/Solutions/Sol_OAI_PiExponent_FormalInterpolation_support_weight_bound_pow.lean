-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_weight_bound_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:12:24.984164+00:00
-- url     : https://prove2.me/submissions/15ccf9ac-acec-42fb-a878-35c4e439e680

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_bound_mul

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] (w : σ → Rat) (A : Real)
    (f : MvPolynomial σ Complex)
    (hbound : ∀ b ∈ f.support, ∑ k, (w k : Real) * (b k : Real) ≤ A)
    (n : Nat) (a : σ →₀ Nat) (ha : a ∈ (f ^ n).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤ (n : Real) * A := by
  induction n generalizing a with
  | zero =>
      have ha0 : a = 0 := by simpa using ha
      subst a
      simp
  | succ n ih =>
      have hpow : ∀ b ∈ (f ^ n).support,
          ∑ k, (w k : Real) * (b k : Real) ≤ (n : Real) * A := by
        intro b hb
        exact ih b hb
      have hm := OAI.PiExponent.FormalInterpolation.weighted_support_bound_mul
        w ((n : Real) * A) A (f ^ n) f hpow hbound a (by simpa [pow_succ] using ha)
      simpa [Nat.cast_succ, add_mul, add_comm, add_left_comm, add_assoc] using hm