-- Prove2me | solution 2 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_ne_zero_imp_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T09:29:46.709983+00:00
-- url     : https://prove2.me/submissions/58e7ba1e-9f6f-4465-8ce6-4469796392bb

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_support
import Mathlib.RingTheory.PowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

/-!
On a finite index type, a finitely supported exponent is determined by
its underlying function. Apply the formal-shear support theorem through
this identification.
-/
theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (e a : Fin (m + 1) →₀ ℕ)
    (hne : MvPowerSeries.coeff e
      (formalShear delta (MvPolynomial.monomial a 1)) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ a i.succ := by
  classical
  let ef : Fin (m + 1) → ℕ := fun i => e i
  let af : Fin (m + 1) → ℕ := fun i => a i
  have he : InterpolationMatrix.exponentVector ef = e := by
    ext i
    simp [ef, InterpolationMatrix.exponentVector]
  have ha : InterpolationMatrix.exponentVector af = a := by
    ext i
    simp [af, InterpolationMatrix.exponentVector]
  by_cases hsame : e = a
  · intro i
    rw [hsame]
  · have hdiff : InterpolationMatrix.exponentVector ef ≠
        InterpolationMatrix.exponentVector af := by
      simpa only [he, ha] using hsame
    have hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector ef)
        (formalShear delta
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector af) 1)) ≠ 0 := by
      simpa only [he, ha] using hne
    have hsupport :=
      OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_support
        delta ef af hdiff hcoeff
    intro i
    simpa only [he, ha] using hsupport.1 i
