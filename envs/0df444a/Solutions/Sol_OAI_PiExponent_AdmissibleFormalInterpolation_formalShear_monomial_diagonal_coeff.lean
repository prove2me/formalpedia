-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_diagonal_coeff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:43:55.110561+00:00
-- url     : https://prove2.me/submissions/0cb5a1b4-bb9a-46e9-a74a-341de188cfb6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_reduce_to_zero_coordinate
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial e 1)) = 1 := by
  simpa only [PowerSeries.coeff_X_pow_self] using
    OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_reduce_to_zero_coordinate
      delta e