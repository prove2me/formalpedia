-- Prove2me | solution 1 for Maldacena2003.amplitudeA_squeezed_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:04:28.938024+00:00
-- url     : https://prove2.me/submissions/5998eaf7-2a02-4859-a60b-410ec94ee609

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

theorem solution (ρd φd φdd k : ℝ) (hk : 0 < k) :
    Tendsto (fun p : ℝ × ℝ => amplitudeA ρd φd φdd k p.1 p.2)
      (𝓝[{p : ℝ × ℝ | IsMomentumTriangle k p.1 p.2}] (k, 0))
      (𝓝 (-(2 * k ^ 3) * scalarTilt ρd φd φdd)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds
  have hc : ContinuousAt (fun p : ℝ × ℝ => amplitudeA ρd φd φdd k p.1 p.2) (k, 0) := by
    simp only [amplitudeA, shapeBracket]
    apply ContinuousAt.add (by fun_prop)
    apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.add (by fun_prop)
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simp; linarith
  have hv : amplitudeA ρd φd φdd k k 0 = -(2 * k ^ 3) * scalarTilt ρd φd φdd := by
    simp only [amplitudeA, shapeBracket, scalarTilt]
    have : k ≠ 0 := hk.ne'
    field_simp
    ring
  have := hc.tendsto
  simpa [hv] using this
