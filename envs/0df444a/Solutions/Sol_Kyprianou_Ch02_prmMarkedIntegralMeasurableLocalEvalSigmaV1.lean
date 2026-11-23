-- Prove2me | solution 1 for Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:39:39.136827+00:00
-- url     : https://prove2.me/submissions/c2157075-60c5-4c92-a4e3-4feb3bc3096d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmNonnegativeIntegralMeasurableLocalEvalSigmaV1
import Theorems.Thm_Kyprianou_Ch02_prmSignedMarkIntegralMeasurableFromPosNegV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R) :
    Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)]
      (fun ω => ∫ z in R, z.2 ∂(N.N ω)) := by
  have hp :=
    Kyprianou.Ch02.prmNonnegativeIntegralMeasurableLocalEvalSigmaV1
      P ν N R hRm
      (R.indicator (fun z : ℝ × ℝ => ENNReal.ofReal z.2))
      ((measurable_snd.ennreal_ofReal).indicator hRm)
      (fun z hz => Set.indicator_of_notMem hz _)
  have hn :=
    Kyprianou.Ch02.prmNonnegativeIntegralMeasurableLocalEvalSigmaV1
      P ν N R hRm
      (R.indicator (fun z : ℝ × ℝ => ENNReal.ofReal (-z.2)))
      ((measurable_snd.neg.ennreal_ofReal).indicator hRm)
      (fun z hz => Set.indicator_of_notMem hz _)
  exact
    Kyprianou.Ch02.prmSignedMarkIntegralMeasurableFromPosNegV1
      P ν N R hRm hp hn
