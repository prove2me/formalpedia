-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.coeff_single_coordinate_binomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:38:40.920975+00:00
-- url     : https://prove2.me/submissions/55ec2757-4c75-4d7e-b8a4-43cd44bbc38c

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Algebra.Polynomial.Coeff
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_singleCoordinatePolynomialCoeff

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (i : Fin m) (n k : ℕ) (b : Fin m → PowerSeries ℂ) :
    ((MvPolynomial.C (b i) + MvPolynomial.X i) ^ n).coeff
        (Finsupp.single i k) =
      PowerSeries.C (((n.choose k : ℕ) : ℂ)) * b i ^ (n - k) := by
  have hp :
      Polynomial.eval₂ (MvPolynomial.C : PowerSeries ℂ →+* MvPolynomial (Fin m) (PowerSeries ℂ))
        (MvPolynomial.X i)
        ((Polynomial.X + Polynomial.C (b i)) ^ n) =
      (MvPolynomial.C (b i) + MvPolynomial.X i) ^ n := by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact congrArg (fun z => z ^ n) (add_comm (MvPolynomial.X i) (MvPolynomial.C (b i)))
  rw [← hp, OAI.PiExponent.FinitePeriodCollision.singleCoordinatePolynomialCoeff]
  rw [Polynomial.coeff_X_add_C_pow]
  simp [PowerSeries.C, mul_comm]