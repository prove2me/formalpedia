-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_eq_top_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:09:51.530992+00:00
-- url     : https://prove2.me/submissions/fa28fcae-da5e-4a6e-8d53-2980d9df84e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_coeff_sum_support_monomials
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_eq_if_top

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hbound : ∀ a ∈ P.support, ∀ i : Fin m, a i.succ ≤ e i.succ) :
    MvPowerSeries.coeff e (formalShear delta P) =
      ∑ a ∈ P.support.filter (fun a => ∀ i : Fin m, a i.succ = e i.succ),
        MvPolynomial.coeff a P *
          PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0)) := by
  classical
  rw [OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_sum_support_monomials]
  calc
    (∑ a ∈ P.support,
        MvPolynomial.coeff a P *
          MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1))) =
      ∑ a ∈ P.support,
        MvPolynomial.coeff a P *
          (if ∀ i : Fin m, a i.succ = e i.succ then
            PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0))
          else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_eq_if_top
          delta e a (fun i => hbound a ha i)]
    _ = ∑ a ∈ P.support,
        if ∀ i : Fin m, a i.succ = e i.succ then
          MvPolynomial.coeff a P *
            PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0))
        else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : ∀ i : Fin m, a i.succ = e i.succ <;> simp [h]
    _ = ∑ a ∈ P.support.filter (fun a => ∀ i : Fin m, a i.succ = e i.succ),
        MvPolynomial.coeff a P *
          PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0)) := by
        rw [← Finset.sum_filter]