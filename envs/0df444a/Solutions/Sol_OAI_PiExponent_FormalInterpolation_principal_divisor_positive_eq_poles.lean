-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.principal_divisor_positive_eq_poles
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:20:03.733766+00:00
-- url     : https://prove2.me/submissions/d2a6dd7a-9c07-4960-9b84-dc07f4bc9d96

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_max_neg_polynomialCurveOrder_eq_finrank
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_max_polynomialCurveOrder_eq_finrank
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_algebraMap
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_eq_algebraMap_of_not_transcendental
import Mathlib.Tactic

open scoped BigOperators
open IntermediateField
open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (f : E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu f : Real) 0) =
      ∑ᶠ nu : PolynomialCurvePlace E,
        max (-(polynomialCurveOrder nu f : Real)) 0 := by
  classical
  by_cases hf0 : f = 0
  · subst hf0
    have h0 : ∀ nu : PolynomialCurvePlace E,
        polynomialCurveOrder nu 0 = 0 := by
      intro nu; simp [polynomialCurveOrder, AddValuation.map_zero]
    simp [h0]
  · by_cases htr : Transcendental Complex f
    · obtain ⟨t, ht, hfin⟩ :=
        exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one htrdeg
      haveI : FiniteDimensional (adjoin Complex ({t} : Set E)) E := hfin
      have hfinf : FiniteDimensional (adjoin Complex ({f} : Set E)) E :=
        finiteDimensional_adjoin_of_transcendental (K := Complex) (F := E) t htr
      rw [finsum_max_polynomialCurveOrder_eq_finrank f htr hfinf,
        finsum_max_neg_polynomialCurveOrder_eq_finrank f htr hfinf]
    · obtain ⟨b, rfl⟩ := exists_eq_algebraMap_of_not_transcendental f htr
      have hb : b ≠ 0 := by
        intro hb; apply hf0; simp [hb]
      have hord : ∀ nu : PolynomialCurvePlace E,
          polynomialCurveOrder nu (algebraMap Complex E b) = 0 :=
        fun nu => polynomialCurveOrder_algebraMap nu hb
      simp [hord]
