-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_product_has_factor_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:13:55.46982+00:00
-- url     : https://prove2.me/submissions/7ac92565-130c-4f88-9482-c36c4eeb21fb

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_product_decomposition_finset

open scoped BigOperators

 theorem solution
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (f : ι → MvPolynomial σ Complex) (a : σ →₀ Nat)
    (ha : a ∈ (∏ i, f i).support) :
    ∃ b : ι → σ →₀ Nat, (∀ i, b i ∈ (f i).support) ∧ a = ∑ i, b i := by
  classical
  obtain ⟨b, hb, hsum⟩ :=
    OAI.PiExponent.FormalInterpolation.support_product_decomposition_finset
      (s := Finset.univ) f a (by simpa using ha)
  refine ⟨b, ?_, hsum⟩
  intro i
  exact hb i (Finset.mem_univ i)
