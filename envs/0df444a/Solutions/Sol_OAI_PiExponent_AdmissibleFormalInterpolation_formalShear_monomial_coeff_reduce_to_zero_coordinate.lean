-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_reduce_to_zero_coordinate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:55:56.843614+00:00
-- url     : https://prove2.me/submissions/33c27a8c-2f6b-4cdf-96e5-0306ef80b0ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_coeff_of_successor_top_support

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial e 1)) =
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (e 0)) := by
  classical
  have hbound : ∀ a ∈ (MvPolynomial.monomial e 1 : MvPolynomial (Fin (m + 1)) ℂ).support,
      ∀ i : Fin m, a i.succ ≤ e i.succ := by
    intro a ha i
    have hae : a = e := by
      by_contra hne
      simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, hne] at ha
      exact hne ha.symm
    simpa [hae]
  have htop : ∀ a ∈ (MvPolynomial.monomial e 1 : MvPolynomial (Fin (m + 1)) ℂ).support,
      (∀ i : Fin m, a i.succ = e i.succ) → a = e := by
    intro a ha hall
    have hae : a = e := by
      by_contra hne
      simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, hne] at ha
      exact hne ha.symm
    exact hae
  have h := formalShear_coeff_of_successor_top_support
    (delta := delta) (e := e) (P := MvPolynomial.monomial e 1) hbound htop
  simpa using h