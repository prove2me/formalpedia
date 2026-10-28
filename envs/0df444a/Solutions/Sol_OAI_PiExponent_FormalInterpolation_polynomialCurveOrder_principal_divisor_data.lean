-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_principal_divisor_data
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:29:32.440771+00:00
-- url     : https://prove2.me/submissions/5b3ea4db-cc99-4012-b892-9b3d97ad90c8

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_finite_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_sum_eq_norm
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_rationalAdjoin_principal_divisor
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (E : Type) [Field E] [Algebra Complex E]
    (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin Complex {t}) E)
    (ht : Transcendental Complex t) (f : E) :
    (Set.Finite {nu : PolynomialCurvePlace E |
      polynomialCurveOrder nu f ≠ 0}) ∧
      (∑ᶠ nu : PolynomialCurvePlace E,
        (polynomialCurveOrder nu f : Real)) = 0 := by
  constructor
  · exact OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_finite_support
      E t hfinite ht f
  · rw [OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_sum_eq_norm
      E t hfinite ht f]
    exact OAI.PiExponent.FormalInterpolation.rationalAdjoin_principal_divisor
      E t ht (Algebra.norm (IntermediateField.adjoin Complex {t}) f)