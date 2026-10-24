-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_finsupp_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:08:51.666204+00:00
-- url     : https://prove2.me/submissions/9b67ecbe-6864-4039-b387-80e9f7dde961

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (w : σ → Rat) (f : ι → MvPolynomial σ Complex) (B : ι → Real)
    (b : ι → σ →₀ Nat) (hb : ∀ i, b i ∈ (f i).support)
    (hbound : ∀ i, ∀ c ∈ (f i).support,
      ∑ k, (w k : Real) * (c k : Real) ≤ B i) :
    ∑ k, (w k : Real) * ((∑ i, b i) k : Real) ≤ ∑ i, B i := by
  calc
    ∑ k, (w k : Real) * ((∑ i, b i) k : Real)
        = ∑ k, ∑ i, (w k : Real) * ((b i k : Nat) : Real) := by
          congr 1
          funext k
          simp [Finset.mul_sum]
    _ = ∑ i, ∑ k, (w k : Real) * ((b i k : Nat) : Real) := Finset.sum_comm
    _ ≤ ∑ i, B i := by
          apply Finset.sum_le_sum
          intro i hi
          exact hbound i (b i) (hb i)