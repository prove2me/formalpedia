-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversZeroStartV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:35:12.854048+00:00
-- url     : https://prove2.me/submissions/37ad1be4-55d0-4c00-925b-a37248be0650
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoIndependentDriversV1
import Theorems.Thm_Kyprianou_Ch02_normaliseBrownianPreservesIndependentPRMDriversV1
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
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure),
          (∀ ω : Ω, B.W 0 ω = 0) ∧
          ProbabilityTheory.IndepFun
            (fun ω => fun (t : ℝ) => B.W t ω)
            (fun ω => N.N ω) P := by
  classical
  obtain ⟨Ω, measΩ, hExist⟩ :=
    Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversV1 levyMeasure
  letI : MeasurableSpace Ω := measΩ
  obtain ⟨P, probP, hExist'⟩ := hExist
  letI : IsProbabilityMeasure P := probP
  obtain ⟨B, N, hind⟩ := hExist'
  obtain ⟨B', hW, hZero, hind'⟩ :=
    Kyprianou.Ch02.normaliseBrownianPreservesIndependentPRMDriversV1
      P levyMeasure B N hind
  exact ⟨Ω, measΩ, P, probP, B', N, hZero, hind'⟩
