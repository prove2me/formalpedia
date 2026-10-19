-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_successor_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:33:34.385304+00:00
-- url     : https://prove2.me/submissions/8cd5d7da-6b97-4f6f-b418-b261a24915e9

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a : Fin (m + 1) →₀ ℕ) :
    formalShear delta (MvPolynomial.monomial a 1) =
      (MvPowerSeries.X 0) ^ (a 0) *
        ∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ) := by
  simp [formalShear, MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial,
    Fin.prod_univ_succ]