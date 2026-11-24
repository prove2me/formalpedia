-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyItoIndependentDriversNormalisedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:36:34.651981+00:00
-- url     : https://prove2.me/submissions/5a451219-774b-47ef-b328-5e984f243961

import Theorems.Thm_Kyprianou_Ch02_normalisedBrownianDriverExistsV1
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists
import Theorems.Thm_Kyprianou_Ch02_productNormalisedBrownianPoissonIndependentV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
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
          ProbabilityTheory.IndepFun
            (fun ω => fun (t : ℝ) => B.W t ω)
            (fun ω => N.N ω) P ∧
          (∀ ω : Ω, B.W 0 ω = 0) := by
  obtain ⟨Ω₁, m₁, P₁, hP₁, B₁, hB₁zero⟩ :=
    Kyprianou.Ch02.normalisedBrownianDriverExistsV1
  obtain ⟨Ω₂, m₂, P₂, hP₂, ⟨N₂⟩⟩ :=
    Kyprianou.poissonRandomMeasureExists levyMeasure
  letI : MeasurableSpace Ω₁ := m₁
  letI : MeasurableSpace Ω₂ := m₂
  letI : IsProbabilityMeasure P₁ := hP₁
  letI : IsProbabilityMeasure P₂ := hP₂
  obtain ⟨B, N, hDrivers, hzero⟩ :=
    Kyprianou.Ch02.productNormalisedBrownianPoissonIndependentV1
      P₁ P₂ levyMeasure B₁ N₂ hB₁zero
  let P : Measure (Ω₁ × Ω₂) := P₁.prod P₂
  have hP : IsProbabilityMeasure P := inferInstance
  exact ⟨Ω₁ × Ω₂, inferInstance, P, hP, B, N, hDrivers, hzero⟩

