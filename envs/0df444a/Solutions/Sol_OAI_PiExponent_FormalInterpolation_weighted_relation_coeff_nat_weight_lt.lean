-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_relation_coeff_nat_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:14:07.842257+00:00
-- url     : https://prove2.me/submissions/c692547f-4f2d-48f8-a02d-643e64ed7f23

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat} (W : Fin d → Nat) (delta : Nat) (hdelta : 0 < delta) (n : Nat) (i : Fin d) (q : MvPolynomial (Fin d) ℂ) (hq : ∀ a : Fin d →₀ Nat, a ∈ q.support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - (delta : ℤ)) : ∀ a : Fin d →₀ Nat, a ∈ q.support → (∑ k : Fin d, a k * W k) < n * W i := by
  intro a ha
  have h := hq a ha
  have hcast : ((∑ k : Fin d, a k * W k : Nat) : Int) =
      ((n * W i : Nat) : Int) - (delta : Int) := by
    simpa only [Nat.cast_sum, Nat.cast_mul] using h
  omega