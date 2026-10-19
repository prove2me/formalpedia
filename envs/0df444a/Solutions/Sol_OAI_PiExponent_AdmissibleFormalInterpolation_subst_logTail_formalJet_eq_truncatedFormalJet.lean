-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_eq_truncatedFormalJet
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:01:40.888543+00:00
-- url     : https://prove2.me/submissions/531d3f38-c05d-4f55-9871-031158565099
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet_generator
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet_eq_truncatedFormalJet_of_generators

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (T : Fin m → ℕ) (c : Fin m → ℂ)
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
  apply OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_eq_truncatedFormalJet_of_generators
    (T := T) (c := c)
  intro s
  exact OAI.PiExponent.AdmissibleFormalInterpolation.subst_logTail_formalJet_generator
    (T := T) (c := c) s