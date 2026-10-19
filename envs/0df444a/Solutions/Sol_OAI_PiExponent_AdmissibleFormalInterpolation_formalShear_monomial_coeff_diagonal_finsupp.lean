-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_diagonal_finsupp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:32:47.503177+00:00
-- url     : https://prove2.me/submissions/b685c6d4-07cd-48a8-8c36-723d8c3d234f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_diagonal_coeff_succ_shear_product

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial e 1)) = 1 := by
  simpa [formalShear, MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial] using
    OAI.PiExponent.AdmissibleFormalInterpolation.diagonal_coeff_succ_shear_product
      delta e