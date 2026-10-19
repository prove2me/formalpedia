-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_ne_zero_imp_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:37:36.119728+00:00
-- url     : https://prove2.me/submissions/45d89013-3ba8-4e68-967a-d1b4af275592

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_eq_product
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_product_support
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_succ_support

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (hne : MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial a 1)) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ a i.succ := by
  rw [OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_eq_product
    (delta := delta) (a := a)] at hne
  apply OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_product_support
    (a := a) (e := e) (g := fun i => liftLogSeries m (delta i))
  · intro i d j hcoord
    exact OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_succ_support
      (delta := delta) i d j hcoord
  · exact hne