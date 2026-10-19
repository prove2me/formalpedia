-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coeff_nonzero_of_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:26:01.974131+00:00
-- url     : https://prove2.me/submissions/2f248c1f-b513-43d6-8254-3a07165c9621

import Mathlib.RingTheory.MvPolynomial.Ideal

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]
    (m : Nat) (f : Fin m → MvPolynomial σ k) (p : MvPolynomial σ k)
    (d : σ →₀ Nat) (hp : p = ∑ j, f j) (hd : p.coeff d ≠ 0) :
    ∃ j, (f j).coeff d ≠ 0 := by
  by_contra h
  push_neg at h
  apply hd
  rw [hp, MvPolynomial.coeff_sum]
  exact Finset.sum_eq_zero fun j hj => h j