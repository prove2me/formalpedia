-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagJumpOfAddContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:04:24.787167+00:00
-- url     : https://prove2.me/submissions/224b8c62-ade8-4b4c-b8db-c120ac66a40a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (f g : ℝ≥0 → ℝ) (hf : IsCadlag f) (hg : Continuous g)
    (u : ℝ≥0) (hu : 0 < u) :
    (f u + g u) - Function.leftLim (fun t => f t + g t) u =
      f u - Function.leftLim f u := by
  haveI : (𝓝[<] u).NeBot :=
    nhdsWithin_Iio_neBot' ⟨0, hu⟩ le_rfl
  have hfl := tendsto_leftLim_of_tendsto (hf u).2
  have hgl : Tendsto g (𝓝[<] u) (𝓝 (g u)) :=
    hg.continuousAt.continuousWithinAt
  rw [leftLim_eq_of_tendsto (hfl.add hgl)]
  ring
