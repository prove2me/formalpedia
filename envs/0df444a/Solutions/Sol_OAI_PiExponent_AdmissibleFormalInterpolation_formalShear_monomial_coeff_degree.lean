-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_degree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T08:52:58.394627+00:00
-- url     : https://prove2.me/submissions/d2fd2940-a184-4da4-b622-24831b104297

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_monomial_coeff_support
import Mathlib.RingTheory.PowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

/-!
A nonzero off-diagonal shear coefficient has pointwise bounded successor
exponents, with a strict inequality in some coordinate. Summation yields
the strict total-degree comparison.
-/
theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a b : Fin (m + 1) → ℕ)
    (hne : InterpolationMatrix.exponentVector a ≠ InterpolationMatrix.exponentVector b)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (formalShear delta (MvPolynomial.monomial (InterpolationMatrix.exponentVector b) 1)) ≠ 0) :
    (∑ k : Fin m, (InterpolationMatrix.exponentVector a) k.succ) <
      (∑ k : Fin m, (InterpolationMatrix.exponentVector b) k.succ) := by
  obtain ⟨hle, j, hj⟩ :=
    OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_monomial_coeff_support
      delta a b hne hcoeff
  apply Finset.sum_lt_sum
  · intro i hi
    exact hle i
  · exact ⟨j, Finset.mem_univ j, hj⟩
