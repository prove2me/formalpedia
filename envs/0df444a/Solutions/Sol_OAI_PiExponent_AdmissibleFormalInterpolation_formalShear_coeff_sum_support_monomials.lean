-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_sum_support_monomials
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:33:24.579157+00:00
-- url     : https://prove2.me/submissions/dd588f22-f963-4872-8d9c-3dea82aa3b48

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.coeff e (formalShear delta P) =
      ∑ a ∈ P.support,
        MvPolynomial.coeff a P *
          MvPowerSeries.coeff e (formalShear delta (MvPolynomial.monomial a 1)) := by
  have hP : P = ∑ a ∈ P.support, MvPolynomial.monomial a (MvPolynomial.coeff a P) :=
    MvPolynomial.as_sum P
  conv_lhs => rw [hP]
  simp only [map_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hterm :
      MvPolynomial.monomial a (MvPolynomial.coeff a P) =
        MvPolynomial.C (MvPolynomial.coeff a P) * MvPolynomial.monomial a 1 := by
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hterm, map_mul]
  have hC : formalShear delta (MvPolynomial.C (MvPolynomial.coeff a P)) =
      MvPowerSeries.C (MvPolynomial.coeff a P) := by
    simp [formalShear, MvPowerSeries.c_eq_algebraMap]
  rw [hC, MvPowerSeries.coeff_C_mul]