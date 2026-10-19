-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:49:49.355036+00:00
-- url     : https://prove2.me/submissions/77969e95-fa64-4b5a-9137-d79f6923a968

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (a : Fin (m + 1) →₀ ℕ) :
    formalShear delta (MvPolynomial.monomial a 1) =
      MvPowerSeries.X 0 ^ a 0 *
        ∏ i : Fin m, (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ a i.succ := by
  classical
  rw [formalShear, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_succ]
    simp only [map_one, one_mul]
    rfl
  · intro i
    simp