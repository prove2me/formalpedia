-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.diagonal_coeff_succ_shear_product
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:38:16.706002+00:00
-- url     : https://prove2.me/submissions/7ac71ed8-87c8-4eb5-927f-6428f627df97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_diagonal_coeff

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (e.prod fun j k =>
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (delta i)) j) ^ k) = 1 := by
  simpa [formalShear, MvPolynomial.aeval_monomial] using
    (formalShear_monomial_diagonal_coeff (m := m) delta e)