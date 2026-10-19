-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mem_ideal_span_as_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:14:55.42515+00:00
-- url     : https://prove2.me/submissions/29c2c266-edef-490d-b84c-da5390e729d5

import Mathlib.RingTheory.MvPolynomial.Ideal

open scoped BigOperators

theorem solution
    {R : Type*} [CommSemiring R] (S : Set R) (p : R)
    (hp : p ∈ Ideal.span S) :
    ∃ (m : Nat) (x : Fin m → R) (q : Fin m → R),
      (∀ j, x j ∈ S) ∧ p = ∑ j, x j * q j := by
  classical
  change p ∈ Submodule.span R S at hp
  obtain ⟨m, q, x, hsum⟩ := Submodule.mem_span_set'.mp hp
  refine ⟨m, fun j => (x j : R), q, ?_, ?_⟩
  · intro j
    exact (x j).property
  · simpa [smul_eq_mul, mul_comm] using hsum.symm