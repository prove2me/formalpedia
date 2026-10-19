-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T13:12:53.367216+00:00
-- url     : https://prove2.me/submissions/cf6a2633-b526-4a93-b458-67e7202e00ee

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_diagonal_finsupp

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (OAI.PiExponent.InterpolationMatrix.exponentVector a)
      (formalShear delta
        (MvPolynomial.monomial (OAI.PiExponent.InterpolationMatrix.exponentVector a) 1)) = 1 := by
  exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal_finsupp
    delta (OAI.PiExponent.InterpolationMatrix.exponentVector a)