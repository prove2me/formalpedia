-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_if_top
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:23:17.032161+00:00
-- url     : https://prove2.me/submissions/6f5c2dc9-8c25-4b20-8323-5a83f438ce27

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_eq_zero_of_succ_lt
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_eq_at_succ_eq

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e a : Fin (m + 1) →₀ ℕ)
    (hbound : ∀ i : Fin m, a i.succ ≤ e i.succ) :
    MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) =
      if ∀ i : Fin m, a i.succ = e i.succ then
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0))
      else 0 := by
  by_cases htop : ∀ i : Fin m, a i.succ = e i.succ
  · rw [if_pos htop]
    exact formalShear_monomial_coeff_eq_at_succ_eq delta e a htop
  · rw [if_neg htop]
    apply formalShear_monomial_coeff_eq_zero_of_succ_lt
    by_contra h
    push_neg at h
    have hall : ∀ i : Fin m, a i.succ = e i.succ := by
      intro i
      have hle := hbound i
      have hnot := h i
      omega
    exact htop hall
