-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_support_bound_mul
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:20:49.353755+00:00
-- url     : https://prove2.me/submissions/94841d10-2148-463f-ab37-ab9fce764006

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators Pointwise

theorem solution
    {σ : Type*} [Fintype σ] (w : σ → Rat) (A B : Real)
    (p q : MvPolynomial σ Complex)
    (hp : ∀ b ∈ p.support, ∑ k, (w k : Real) * (b k : Real) ≤ A)
    (hq : ∀ c ∈ q.support, ∑ k, (w k : Real) * (c k : Real) ≤ B)
    (a : σ →₀ Nat) (ha : a ∈ (p * q).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤ A + B := by
  classical
  have hmem : a ∈ p.support + q.support := MvPolynomial.support_mul p q ha
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.mem_add.mp hmem
  have hsum :
      (∑ k, (w k : Real) * (a k : Real)) =
        (∑ k, (w k : Real) * (b k : Real)) +
          (∑ k, (w k : Real) * (c k : Real)) := by
    rw [← hbc]
    simp [Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  calc
    ∑ k, (w k : Real) * (a k : Real) =
        (∑ k, (w k : Real) * (b k : Real)) +
          (∑ k, (w k : Real) * (c k : Real)) := hsum
    _ ≤ A + B := add_le_add (hp b hb) (hq c hc)
