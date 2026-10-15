-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_identity_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:07:43.86214+00:00
-- url     : https://prove2.me/submissions/ea02ee79-7667-4c9b-b1a1-f77303bbf27a

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPolynomial.aeval MvPowerSeries.X Q) =
    MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q := by
  have hQ :
      MvPolynomial.aeval MvPowerSeries.X Q =
        (Q : MvPowerSeries (Fin (m + 1)) ℂ) := by
    induction Q using MvPolynomial.induction_on with
    | C r => simp [← MvPowerSeries.c_eq_algebraMap]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  rw [hQ, MvPolynomial.coeff_coe]
