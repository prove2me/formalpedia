-- Prove2me | solution 1 for Kyprianou.poissonRandomMeasureIntegralLaws
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:45:30.85996+00:00
-- url     : https://prove2.me/submissions/98c461b0-6542-4df1-b1e8-281baaf3d679
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_ch02PoissonIntegralIntegrabilityCriterion
import Theorems.Thm_Kyprianou_ch02PoissonIntegralCharacteristicExponent
import Theorems.Thm_Kyprianou_ch02PoissonIntegralFirstMoment
import Theorems.Thm_Kyprianou_ch02PoissonIntegralSecondMoment
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false


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
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Kyprianou.ch02PoissonIntegralIntegrabilityCriterion P m K Y hd f hf
  · exact Kyprianou.ch02PoissonIntegralCharacteristicExponent P m K Y hd f hf
  · exact Kyprianou.ch02PoissonIntegralFirstMoment P m K Y hd f hf
  · exact Kyprianou.ch02PoissonIntegralSecondMoment P m K Y hd f hf

