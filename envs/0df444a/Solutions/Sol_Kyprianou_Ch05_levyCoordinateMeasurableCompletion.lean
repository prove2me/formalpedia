-- Prove2me | solution 1 for Kyprianou.Ch05.levyCoordinateMeasurableCompletion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:08:50.757328+00:00
-- url     : https://prove2.me/submissions/65b16c9e-4819-4b20-b3c6-0abf0394f730

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (Y : NNReal → Omega → Real)
    (hY : ProbabilityTheory.IsLevyProcess Y P) :
    ∀ t : NNReal, Measurable (fun w : NullMeasurableSpace Omega P => Y t w) := by
  intro t
  have h := (hY.stationary_increments 0 t).aemeasurable_snd
  have hc : AEMeasurable (Y t) P := by
    have he : ProbabilityTheory.increment Y 0 t = Y t := by
      funext w
      change Y t w - Y 0 w = Y t w
      rw [hY.start_zero]
      simp
    rwa [he] at h
  exact hc.nullMeasurable.measurable'
