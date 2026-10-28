-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_finite_parameter_degree
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:22:33.464977+00:00
-- url     : https://prove2.me/submissions/88cebdde-d75d-4156-bc96-7be3bc814e66

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_principal_divisor_data
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_positive_negative_balance

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (E : Type) [Field E] [Algebra Complex E]
    (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin Complex {t}) E)
    (ht : Transcendental Complex t) (f : E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (polynomialCurveOrder nu f : Real)) =
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (-(polynomialCurveOrder nu f : Real))) := by
  obtain ⟨hfiniteSupport, hdegreeZero⟩ :=
    OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_principal_divisor_data
      E t hfinite ht f
  exact OAI.PiExponent.FormalInterpolation.finsum_positive_negative_balance
    (fun nu : PolynomialCurvePlace E => polynomialCurveOrder nu f)
    hfiniteSupport hdegreeZero