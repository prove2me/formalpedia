-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T09:14:25.875718+00:00
-- url     : https://prove2.me/submissions/10975f22-acc3-4a9f-b23b-3a21540e1019

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_principal_divisor_balance_finite_parameter_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_principal_divisor_balance_finite_parameter_degree
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurve_principal_divisor_balance_no_transcendental_parameter

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (E : Type) [Field E] [Algebra Complex E]
    (hfinite : ∀ g : E, Transcendental Complex g →
      FiniteDimensional (IntermediateField.adjoin Complex {g}) E)
    (f : E) :
    (fun nu : PolynomialCurvePlace E =>
      (polynomialCurveOrder nu f : Real)).HasFiniteSupport ∧
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (polynomialCurveOrder nu f : Real)) =
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (-(polynomialCurveOrder nu f : Real))) := by
  classical
  by_cases hparam : ∃ t : E, Transcendental Complex t
  · obtain ⟨t, ht⟩ := hparam
    have hfinite_t : FiniteDimensional (IntermediateField.adjoin Complex {t}) E :=
      hfinite t ht
    exact ⟨
      OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_finite_parameter_support
        E t hfinite_t ht f,
      OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_finite_parameter_degree
        E t hfinite_t ht f⟩
  · exact
      OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_no_transcendental_parameter
        E hfinite f hparam