-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveOrder_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:00:10.298408+00:00
-- url     : https://prove2.me/submissions/0b496a00-7c15-4106-b952-de3c4d6f123d

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurveOrder_support_finite_of_hasPrincipalDivisors
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Mathlib.Tactic

open IntermediateField
open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (f : E) :
    Set.Finite {nu : PolynomialCurvePlace E | polynomialCurveOrder nu f ≠ 0} := by
  obtain ⟨t, ht, hfin⟩ :=
    exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one htrdeg
  letI : FiniteDimensional (adjoin Complex ({t} : Set E)) E := hfin
  haveI : HasPrincipalDivisors Complex E :=
    hasPrincipalDivisors_of_transcendental Complex t ht
  exact polynomialCurveOrder_support_finite_of_hasPrincipalDivisors f
