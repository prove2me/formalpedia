-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bad_monomial_mem_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:33:48.178022+00:00
-- url     : https://prove2.me/submissions/069bb694-7906-4d91-9e43-72d046dec700

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d m : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (s n : Nat) (g : Fin m -> MvPolynomial (Fin d) Complex)
    (hg : forall j, g j ∈ I ^ s) (u : Fin m →₀ Nat)
    (hu : n ≤ s * (∑ j : Fin m, u j)) (a : Complex) :
    MvPolynomial.aeval g (MvPolynomial.monomial u a) ∈ I ^ n := by
  classical
  let S := u.support
  have hprod : (∏ j ∈ S, g j ^ u j) ∈ ∏ j ∈ S, (I ^ s) ^ u j := by
    apply Ideal.prod_mem_prod
    intro j hj
    exact Ideal.pow_mem_pow (hg j) (u j)
  have hprod' : (∏ j ∈ S, g j ^ u j) ∈ I ^ (s * (∑ j ∈ S, u j)) := by
    simpa only [Finset.prod_pow_eq_pow_sum, pow_mul] using hprod
  have hsum : (∑ j ∈ S, u j) = ∑ j : Fin m, u j := by
    dsimp [S]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hjS
    simpa [Finsupp.mem_support_iff] using hjS
  have heval :
      MvPolynomial.aeval g (MvPolynomial.monomial u a) ∈
        I ^ (s * (∑ j : Fin m, u j)) := by
    rw [MvPolynomial.aeval_monomial]
    simpa only [Finsupp.prod] using
      (I ^ (s * (∑ j : Fin m, u j))).mul_mem_left
        (algebraMap Complex (MvPolynomial (Fin d) Complex) a)
        (by simpa only [← hsum] using hprod')
  exact Ideal.pow_le_pow_right hu heval
