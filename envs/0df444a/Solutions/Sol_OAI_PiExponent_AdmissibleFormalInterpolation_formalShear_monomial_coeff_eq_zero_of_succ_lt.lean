-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_zero_of_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:28:17.270693+00:00
-- url     : https://prove2.me/submissions/02227a3a-5d1d-46b3-9b2b-c63adfe5a61d

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_ne_zero_imp_succ_le

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (hstrict : ∃ i : Fin m, a i.succ < e i.succ) :
    MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := hstrict
  have hbound :=
    OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_ne_zero_imp_succ_le
      delta e a hne i
  omega