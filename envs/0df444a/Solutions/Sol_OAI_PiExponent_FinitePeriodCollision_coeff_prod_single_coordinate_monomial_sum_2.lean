-- Prove2me | solution 2 for OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:09:18.420336+00:00
-- url     : https://prove2.me/submissions/af68831f-211c-4ec5-b3b0-6838d0a9ee19

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finsupp.Fintype

open scoped BigOperators

theorem solution
    {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommSemiring R]
    (S : σ → Finset ℕ) (c : σ → ℕ → R) (A : σ → ℕ) :
    (∏ i, ∑ n ∈ S i,
      MvPolynomial.monomial (Finsupp.single i n) (c i n)).coeff
        (Finsupp.equivFunOnFinite.symm A) =
      ∏ i, if A i ∈ S i then c i (A i) else 0 := by
  classical
  -- The finite support `Finsupp.equivFunOnFinite.symm x` is the sum of the
  -- single-coordinate finsupps.
  have hsum : ∀ x : σ → ℕ,
      (Finsupp.equivFunOnFinite.symm x : σ →₀ ℕ) = ∑ i, Finsupp.single i (x i) := by
    intro x
    ext j
    simp [Finsupp.single_apply]
  -- A product of single-coordinate monomials is the monomial at the summed finsupp.
  have hprod : ∀ x : σ → ℕ,
      (∏ i, MvPolynomial.monomial (Finsupp.single i (x i)) (c i (x i)) :
          MvPolynomial σ R) =
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm x) (∏ i, c i (x i)) := by
    intro x
    rw [hsum x]
    exact (MvPolynomial.monomial_sum_prod Finset.univ
      (fun i => Finsupp.single i (x i)) (fun i => c i (x i))).symm
  -- Expand the product of finite sums into a sum over choice functions.
  rw [Finset.prod_univ_sum]
  rw [MvPolynomial.coeff_sum]
  simp only [hprod, MvPolynomial.coeff_monomial]
  -- Only the choice function `x = A` can contribute.
  have hiff : ∀ x : σ → ℕ,
      Finsupp.equivFunOnFinite.symm x = Finsupp.equivFunOnFinite.symm A ↔ x = A := by
    intro x
    exact Finsupp.equivFunOnFinite.symm.injective.eq_iff
  simp only [hiff]
  rw [Finset.sum_ite_eq']
  simp only [Fintype.mem_piFinset]
  by_cases h : ∀ i, A i ∈ S i
  · simp only [if_pos h]
    exact Finset.prod_congr rfl fun i _ => (if_pos (h i)).symm
  · simp only [if_neg h]
    simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
