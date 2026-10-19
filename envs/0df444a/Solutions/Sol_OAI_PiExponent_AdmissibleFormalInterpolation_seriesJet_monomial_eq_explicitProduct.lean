-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet_monomial_eq_explicitProduct
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:44:19.490504+00:00
-- url     : https://prove2.me/submissions/e2b78bbc-7614-429f-8fff-7df03bf6754a

import Definitions.Def_OAI_PiExponent_ColumnCombination

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (j : ℕ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : ℕ) (a : Fin m → ℕ) :
  seriesJet (fun i => (j : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector (Fin.cases h a)) 1) =
    (1 + MvPowerSeries.X 0) ^ h *
      ∏ i, (MvPowerSeries.C ((j : ℂ) * r i) + MvPowerSeries.X i.succ +
        liftLogSeries m (G i : PowerSeries ℂ)) ^ a i := by
  classical
  simp [seriesJet, InterpolationMatrix.exponentVector,
    MvPolynomial.aeval_monomial, Fin.prod_univ_succ]