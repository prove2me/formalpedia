-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formalJet_pderiv_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:10:13.159183+00:00
-- url     : https://prove2.me/submissions/2c23ae07-f716-4864-a33f-9e882ae2e08f

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_aeval_pderiv_commute_of_generator
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_generator_pderiv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution {m : Nat} (c : Fin m → Complex) (i : Fin m)
    (F : MvPolynomial (Fin (m + 1)) Complex) :
    formalJet c (MvPolynomial.pderiv i.succ F) =
      MvPowerSeries.pderiv Complex i.succ (formalJet c F) := by
  simpa [formalJet] using
    OAI.PiExponent.FormalInterpolation.aeval_pderiv_commute_of_generator
      (R := Complex) (S := MvPowerSeries (Fin (m + 1)) Complex)
      (g := Fin.cases (1 + MvPowerSeries.X 0)
        (fun k => MvPowerSeries.C (c k) + MvPowerSeries.X k.succ + liftSeries m (PowerSeries.log Complex)))
      (D := MvPowerSeries.pderiv Complex i.succ) F i.succ
      (OAI.PiExponent.FormalInterpolation.formalJet_generator_pderiv c i)