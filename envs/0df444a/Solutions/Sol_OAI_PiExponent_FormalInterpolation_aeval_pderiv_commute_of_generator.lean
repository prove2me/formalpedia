-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.aeval_pderiv_commute_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:17:27.616457+00:00
-- url     : https://prove2.me/submissions/58750d12-d1bf-4759-8d4e-5a8db8b30606

import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators

theorem solution {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq σ] (D : Derivation R S S) (g : σ → S) (p : MvPolynomial σ R)
    (i : σ) (hg : ∀ j, D (g j) = if j = i then 1 else 0) :
    MvPolynomial.aeval g (MvPolynomial.pderiv i p) = D (MvPolynomial.aeval g p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.pderiv_X,
        MvPolynomial.aeval_X]
      rw [D.leibniz]
      simp [hp, hg j, Pi.single_apply, mul_comm, mul_left_comm, mul_assoc] <;> ac_rfl