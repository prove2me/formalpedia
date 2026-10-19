-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.const_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:08:51.921687+00:00
-- url     : https://prove2.me/submissions/035b80ee-3950-4151-b7cc-05e15ee4c689

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Topology
open Filter

theorem solution (c : ℝ) : Tendsto (fun H : ℝ => c / H) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds (x := c)).mul tendsto_inv_atTop_zero