-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_no_transcendental_parameter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:20:48.524276+00:00
-- url     : https://prove2.me/submissions/c1edd76c-fce2-4833-b059-c15aca36f145

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open OAI.PiExponent.FormalInterpolation

theorem solution
    (E : Type) [Field E] [Algebra Complex E]
    (hfinite : ∀ g : E, Transcendental Complex g →
      FiniteDimensional (IntermediateField.adjoin Complex {g}) E)
    (f : E)
    (hparam : ¬ ∃ t : E, Transcendental Complex t) :
    (fun nu : PolynomialCurvePlace E =>
      (polynomialCurveOrder nu f : Real)).HasFiniteSupport ∧
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (polynomialCurveOrder nu f : Real)) =
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (-(polynomialCurveOrder nu f : Real))) := by
  have halg : Algebra.IsAlgebraic Complex E :=
    ⟨fun x => by by_contra h; exact hparam ⟨x, h⟩⟩
  have hsurj : Function.Surjective (algebraMap Complex E) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Complex) (K := E)).2
  have hempty : IsEmpty (PolynomialCurvePlace E) := by
    refine ⟨fun nu => ?_⟩
    obtain ⟨g, hg⟩ := nu.2.2 1
    obtain ⟨b, rfl⟩ := hsurj g
    by_cases hb : b = 0
    · subst hb
      rw [map_zero, AddValuation.map_zero] at hg
      exact WithTop.top_ne_coe hg
    · rw [nu.2.1 b hb] at hg
      have : ((0 : Int) : WithTop Int) = ((1 : Int) : WithTop Int) := hg
      exact absurd (WithTop.coe_injective this) (by decide)
  refine ⟨?_, ?_⟩
  · exact Set.toFinite _
  · simp [finsum_of_isEmpty]
