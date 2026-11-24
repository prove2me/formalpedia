-- Prove2me | solution 1 for Kyprianou.Ch02.levyCoordinateAEMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:23:46.204307+00:00
-- url     : https://prove2.me/submissions/59943750-6776-4306-bcb8-5274a305587d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    ∀ t : ℝ≥0, AEMeasurable (X t) P := by
  intro t
  have hd := (hX.stationary_increments 0 t).aemeasurable_fst
  have heq : ProbabilityTheory.increment X 0 t = X t := by
    funext ω
    simp [ProbabilityTheory.increment, hX.start_zero]
  simpa only [zero_add, heq] using hd
