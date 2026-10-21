-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.singleCoordinatePolynomialCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:51:02.549281+00:00
-- url     : https://prove2.me/submissions/b1ca47ac-e68e-434b-b9f0-1ca547ec825c

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Algebra.Polynomial.Coeff

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (i : Fin m) (p : Polynomial (PowerSeries ℂ)) (k : ℕ) :
    (Polynomial.eval₂
        (MvPolynomial.C : PowerSeries ℂ →+* MvPolynomial (Fin m) (PowerSeries ℂ))
        (MvPolynomial.X i) p).coeff (Finsupp.single i k) = p.coeff k := by
  classical
  have hsingle (n : ℕ) :
      (Finsupp.single i n : Fin m →₀ ℕ) = Finsupp.single i k ↔ n = k := by
    constructor
    · intro h
      exact Finsupp.single_injective i h
    · intro h
      exact congrArg (Finsupp.single i) h
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow,
    hsingle, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro n hn hnk
    simp only [hnk, if_false]
  · intro hk
    simp [Polynomial.notMem_support_iff.mp hk]
