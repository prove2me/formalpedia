-- Prove2me | solution 1 for Kyprianou.ch02PoissonRestrictionLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:50:49.106586+00:00
-- url     : https://prove2.me/submissions/e1c9ed72-b57d-4cdd-b82d-77a368d1f910

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A → MeasurableSet B →
       LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B) < ⊤ →
       P.map (fun ω => N.N ω (A ∩ B)) =
         LevyStochCalc.Poisson.poissonMeasureENN
           (LevyStochCalc.Poisson.referenceIntensity ν (A ∩ B)).toNNReal) := by
  intro A B hA hB hfinite
  exact N.poisson_law (hA.inter hB) (ne_of_lt hfinite)

