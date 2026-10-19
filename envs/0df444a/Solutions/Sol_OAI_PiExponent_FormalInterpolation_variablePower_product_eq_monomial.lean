-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.variablePower_product_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:21:15.90812+00:00
-- url     : https://prove2.me/submissions/f090643a-dd0f-43a4-8f6f-763e352ac77e

import Mathlib.RingTheory.MvPolynomial.Ideal

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (e b : σ → Nat) :
    (∏ i, ((MvPolynomial.X i : MvPolynomial σ k) ^ e i) ^ b i) =
      MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b i)) (1 : k) := by
  classical
  have hsum : (∑ i : σ, Finsupp.single i (e i * b i)) =
      Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b i) := by
    ext j
    simp [Finsupp.single_apply]
  calc
    (∏ i : σ, ((MvPolynomial.X i : MvPolynomial σ k) ^ e i) ^ b i) =
        ∏ i : σ, (MvPolynomial.X i : MvPolynomial σ k) ^ (e i * b i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [pow_mul]
    _ = ∏ i : σ, MvPolynomial.monomial
        (Finsupp.single i (e i * b i)) (1 : k) := by
          simp_rw [MvPolynomial.X_pow_eq_monomial]
    _ = MvPolynomial.monomial
        (∑ i : σ, Finsupp.single i (e i * b i)) (1 : k) := by
          exact (MvPolynomial.monomial_sum_one Finset.univ
            (fun i : σ => Finsupp.single i (e i * b i))).symm
    _ = MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm (fun i : σ => e i * b i)) (1 : k) := by
          rw [hsum]
