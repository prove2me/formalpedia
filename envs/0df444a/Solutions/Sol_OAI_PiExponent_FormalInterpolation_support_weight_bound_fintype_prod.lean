-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_weight_bound_fintype_prod
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:03:43.697995+00:00
-- url     : https://prove2.me/submissions/c32d4aab-8d93-4bad-9e21-ee8f17cc0bca

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_product_has_factor_decomposition
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_finsupp_sum_le

open scoped BigOperators

theorem solution
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (w : σ → Rat) (f : ι → MvPolynomial σ Complex) (B : ι → Real)
    (hbound : ∀ i, ∀ b ∈ (f i).support,
      ∑ k, (w k : Real) * (b k : Real) ≤ B i)
    (a : σ →₀ Nat) (ha : a ∈ (∏ i, f i).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤ ∑ i, B i := by
  obtain ⟨b, hb, hdecomp⟩ :=
    OAI.PiExponent.FormalInterpolation.support_product_has_factor_decomposition
      f a ha
  have hsum :=
    OAI.PiExponent.FormalInterpolation.weighted_finsupp_sum_le
      w f B b hb hbound
  simpa [hdecomp] using hsum
