-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulGaussianDriftLevyZeroStartV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:08:11.157849+00:00
-- url     : https://prove2.me/submissions/5c653bf3-b666-4a5c-b1c7-065e74efef4c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftStationaryIncrementsV1

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0) :
    IsLevyProcess (fun (t : ℝ≥0) (ω : Ω) =>
      (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext ω
    simp [hB0 ω]
  · exact Kyprianou.Ch02.sourceFaithfulGaussianDriftIndependentIncrementsV1 P a σ B hB0
  · exact Kyprianou.Ch02.sourceFaithfulGaussianDriftStationaryIncrementsV1 P a σ B hB0
  · filter_upwards [B.continuous_paths] with ω hω
    have hc : Continuous (fun t : ℝ≥0 =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) :=
      (continuous_const.mul (hω.comp continuous_subtype_val)).sub
        (continuous_const.mul continuous_subtype_val)
    intro t
    exact ⟨hc.continuousAt.continuousWithinAt, _, hc.continuousAt.continuousWithinAt⟩
