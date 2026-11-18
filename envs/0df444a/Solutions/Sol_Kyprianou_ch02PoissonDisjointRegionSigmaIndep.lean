-- Prove2me | solution 1 for Kyprianou.ch02PoissonDisjointRegionSigmaIndep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:59:38.342672+00:00
-- url     : https://prove2.me/submissions/fb9b2f6d-b713-4d46-93c2-dae576f71ff3

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_ch02PoissonDisjointRegionsIndependentSigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A →
      MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set (ℝ × ℝ) |
             C ⊆ A ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)
        (⨆ D ∈ {D : Set (ℝ × ℝ) |
             D ⊆ B ∧ MeasurableSet D},
          MeasurableSpace.comap (fun ω => N.N ω D) inferInstance)
        P) := by
  exact Kyprianou.ch02PoissonDisjointRegionsIndependentSigma P ν N
