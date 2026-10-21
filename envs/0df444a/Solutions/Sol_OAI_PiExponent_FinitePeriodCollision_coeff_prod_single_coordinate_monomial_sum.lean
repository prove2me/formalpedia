-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.coeff_prod_single_coordinate_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:56:37.263989+00:00
-- url     : https://prove2.me/submissions/50782dbd-ef15-42e2-9cbe-bfe3348d5af8

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
open scoped BigOperators

theorem solution
    {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommSemiring R]
    (S : σ → Finset ℕ) (c : σ → ℕ → R) (A : σ → ℕ) :
    (∏ i, ∑ n ∈ S i,
      MvPolynomial.monomial (Finsupp.single i n) (c i n)).coeff
        (Finsupp.equivFunOnFinite.symm A) =
      ∏ i, if A i ∈ S i then c i (A i) else 0 := by
  classical
  have hmon (B : σ → ℕ) :
      (∏ i, MvPolynomial.monomial (Finsupp.single i (B i)) (c i (B i))) =
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm B)
          (∏ i, c i (B i)) := by
    rw [Finsupp.equivFunOnFinite_symm_eq_sum]
    exact (MvPolynomial.monomial_sum_prod Finset.univ
      (fun i => Finsupp.single i (B i)) (fun i => c i (B i))).symm
  have hexp (B : σ → ℕ) :
      Finsupp.equivFunOnFinite.symm B = Finsupp.equivFunOnFinite.symm A ↔ B = A :=
    Finsupp.equivFunOnFinite.symm.injective.eq_iff
  rw [Finset.prod_univ_sum, MvPolynomial.coeff_sum]
  simp_rw [hmon, MvPolynomial.coeff_monomial, hexp]
  rw [Finset.sum_ite_eq']
  simp only [Fintype.mem_piFinset, Fintype.prod_ite_zero]