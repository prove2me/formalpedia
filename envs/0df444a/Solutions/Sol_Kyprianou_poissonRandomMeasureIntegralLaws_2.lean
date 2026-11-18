-- Prove2me | solution 2 for Kyprianou.poissonRandomMeasureIntegralLaws
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:05:49.087377+00:00
-- url     : https://prove2.me/submissions/e07251d9-13c0-4610-815c-f91664af4bf4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Theorems.Thm_Kyprianou_ch02PoissonIntegralIntegrabilityCriterion
import Theorems.Thm_Kyprianou_ch02PoissonIntegralCharacteristicExponent
import Theorems.Thm_Kyprianou_ch02PoissonIntegralFirstMoment
import Theorems.Thm_Kyprianou_ch02PoissonIntegralSecondMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source-exact conjunction of the four existing Poisson integral obligations. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
    ((∀ᵐ ω ∂P,
      Integrable f (ProbabilityTheory.poissonRandomMeasure K Y ω)) ↔
      Integrable (fun x => min (1 : ℝ) |f x|) m) ∧
    (Integrable (fun x => min (1 : ℝ) |f x|) m →
      ∀ ξ : ℝ,
        charFun (P.map (fun ω =>
          ∫ x, f x ∂(ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
        Complex.exp
          (∫ x, (Complex.exp (Complex.I *
            (((ξ * f x : ℝ) : ℂ))) - 1) ∂m)) ∧
    (Integrable f m →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
        ∫ x, f x ∂m) ∧
    ((Integrable f m ∧ MemLp f 2 m) →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
          (∫ x, f x ^ 2 ∂m) + (∫ x, f x ∂m) ^ 2) := by
  exact ⟨
    Kyprianou.ch02PoissonIntegralIntegrabilityCriterion P m K Y hd f hf,
    Kyprianou.ch02PoissonIntegralCharacteristicExponent P m K Y hd f hf,
    Kyprianou.ch02PoissonIntegralFirstMoment P m K Y hd f hf,
    Kyprianou.ch02PoissonIntegralSecondMoment P m K Y hd f hf
  ⟩
