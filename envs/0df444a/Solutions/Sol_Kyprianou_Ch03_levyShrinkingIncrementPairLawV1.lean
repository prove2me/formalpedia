-- Prove2me | solution 1 for Kyprianou.Ch03.levyShrinkingIncrementPairLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:19:13.536321+00:00
-- url     : https://prove2.me/submissions/92647d09-577b-4e70-8001-df9897acdfa7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (u s : NNReal) :
    IdentDistrib
      (fun ω : Omega => (X u ω - X (min s u) ω, (0 : Real)))
      (fun ω : Omega => (X (u - min s u) ω, (0 : Real))) P P := by
  have h := hX.stationary_increments (min s u) (u - min s u)
  have he : min s u + (u - min s u) = u := by
    rw [add_comm, tsub_add_cancel_of_le (min_le_right s u)]
  rw [he] at h
  simpa [Function.comp_def, ProbabilityTheory.increment, hX.start_zero] using
    h.comp (measurable_id.prodMk measurable_const :
      Measurable (fun x : ℝ => (x, (0 : ℝ))))
