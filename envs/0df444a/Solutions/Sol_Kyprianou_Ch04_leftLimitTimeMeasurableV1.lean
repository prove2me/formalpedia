-- Prove2me | solution 1 for Kyprianou.Ch04.leftLimitTimeMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:58:26.529195+00:00
-- url     : https://prove2.me/submissions/5af8ce6a-6571-42ae-bd6e-c7c3d1e53387

import Theorems.Thm_Kyprianou_Ch04_clippedReciprocalLeftApproachV1
import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A positive-time left-limit version of a measurable path is measurable in time. -/
theorem solution (U L : NNReal → ℝ) (hU : Measurable U)
    (hL : ∀ t : NNReal, 0 < t → Tendsto U (𝓝[<] t) (𝓝 (L t))) :
    Measurable L := by
  let r (n : ℕ) (t : NNReal) := Real.toNNReal ((t : ℝ) - 1 / ((n : ℝ) + 1))
  let g (n : ℕ) (t : NNReal) := if t = 0 then L 0 else U (r n t)
  apply measurable_of_tendsto_metrizable (f := g)
  · intro n
    apply Measurable.ite (measurableSet_singleton 0) measurable_const
    exact hU.comp (measurable_real_toNNReal.comp (NNReal.continuous_coe.measurable.sub_const _))
  apply tendsto_pi_nhds.mpr
  intro t
  by_cases hz : t = 0
  · simpa [g,hz] using (tendsto_const_nhds (x := L 0))
  have ht : 0 < t := pos_iff_ne_zero.mpr hz
  have hwithin := Kyprianou.Ch04.clippedReciprocalLeftApproachV1 t ht
  simpa [g,hz,Function.comp_def,r] using (hL t ht).comp hwithin
