-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_eq_truncatedFormalJet_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:56:20.981018+00:00
-- url     : https://prove2.me/submissions/c7c43f31-a2ce-4cb9-aca7-85b3561980a1

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
    (hgen : ∀ s : Fin (m + 1),
      MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X i.succ +
                liftLogSeries m
                  ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                    PowerSeries.log ℂ)))
          (formalJet c (MvPolynomial.X s)) =
        truncatedFormalJet T c (MvPolynomial.X s))
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
          (fun i : Fin m =>
            MvPowerSeries.X i.succ +
              liftLogSeries m
                ((InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
                  PowerSeries.log ℂ)))
        (formalJet c P) =
      truncatedFormalJet T c P := by
  exact OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet T c P
