-- Prove2me | solution 1 for Kyprianou.Ch02.normaliseBrownianPreservesIndependentPRMDriversV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:38:38.307807+00:00
-- url     : https://prove2.me/submissions/6768e437-f173-4c33-9e49-5a029cbe9107
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
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

open Kyprianou Kyprianou.Ch02

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
  obtain ⟨B', hW⟩ :=
    Kyprianou.Ch02.normaliseBrownianMotionZeroAtOriginV1 P B
  have hInd :=
    Kyprianou.Ch02.normalisedBrownianPathIndependentOfPRMV1
      P levyMeasure B N hDrivers
  refine ⟨B', hW, ?_, ?_⟩
  · intro ω
    rw [hW 0 ω]
    ring
  · have heq :
        (fun ω => fun (t : ℝ) => B'.W t ω) =
        (fun ω => fun (t : ℝ) => B.W t ω - B.W 0 ω) := by
      funext ω t
      exact hW t ω
    rwa [heq]
