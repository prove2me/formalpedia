-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_at_succ_eq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:28:52.625984+00:00
-- url     : https://prove2.me/submissions/ee28e4d4-e453-444a-a810-6c8b83c98e7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_eq_successor_product
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_coeff_eq

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, a i.succ = e i.succ) :
    MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) =
      PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0)) := by
  rw [OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_successor_product]
  exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_coeff_eq
    delta e a htop