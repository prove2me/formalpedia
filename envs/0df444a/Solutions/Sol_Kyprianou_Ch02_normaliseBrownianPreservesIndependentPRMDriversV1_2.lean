-- Prove2me | solution 2 for Kyprianou.Ch02.normaliseBrownianPreservesIndependentPRMDriversV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:51:24.748373+00:00
-- url     : https://prove2.me/submissions/158bb210-a610-4df2-a816-ee0aaf50a732

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Theorems.Thm_Kyprianou_Ch02_normaliseBrownianMotionZeroAtOriginV1
import Theorems.Thm_Kyprianou_Ch02_normalisedBrownianPathIndependentOfPRMV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P) :
    ∃ B' : LevyStochCalc.Brownian.BrownianMotion P,
      (∀ (t : ℝ) (ω : Ω), B'.W t ω = B.W t ω - B.W 0 ω) ∧
      (∀ ω : Ω, B'.W 0 ω = 0) ∧
      ProbabilityTheory.IndepFun
        (fun ω => fun (t : ℝ) => B'.W t ω)
        (fun ω => N.N ω) P := by
  rcases Kyprianou.Ch02.normaliseBrownianMotionZeroAtOriginV1 P B with
    ⟨B', hB'⟩
  refine ⟨B', hB', ?_, ?_⟩
  · intro ω
    simpa only [sub_self] using hB' 0 ω
  · have hIndep :=
      Kyprianou.Ch02.normalisedBrownianPathIndependentOfPRMV1
        P levyMeasure B N hDrivers
    have hEq :
        (fun ω => fun (t : ℝ) => B'.W t ω) =
        (fun ω => fun (t : ℝ) => B.W t ω - B.W 0 ω) := by
      funext ω t
      exact hB' t ω
    rw [hEq]
    exact hIndep
