-- Prove2me | solution 1 for Maldacena2003.shapeF_equilateral_and_squeezed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:05:09.32869+00:00
-- url     : https://prove2.me/submissions/642874ef-906a-49e0-bedf-e96e921c66a6

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

theorem solution (k : ℝ) (hk : 0 < k) :
    shapeF k k k = 5 / 6 ∧
      Tendsto (fun p : ℝ × ℝ => shapeF k p.1 p.2)
        (𝓝[{p : ℝ × ℝ | IsMomentumTriangle k p.1 p.2}] (k, 0)) (𝓝 0) := by
  have hk0 : k ≠ 0 := hk.ne'
  constructor
  · simp only [shapeF, shapeBracket]
    field_simp
    ring
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun p : ℝ × ℝ => shapeF k p.1 p.2) (k, 0) := by
      simp only [shapeF, shapeBracket]
      apply ContinuousAt.sub _ continuousAt_const
      apply ContinuousAt.div _ (by fun_prop) (by simp [hk0])
      apply ContinuousAt.add (by fun_prop)
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simp; linarith
    have hv : shapeF k k 0 = 0 := by
      simp only [shapeF, shapeBracket]
      field_simp
      ring
    simpa [hv] using hc.tendsto
