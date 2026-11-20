-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryPositiveLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:01:13.785177+00:00
-- url     : https://prove2.me/submissions/208279d7-2edb-487d-942a-4bbc36cdb2bc

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryNormNearZero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Lower integration-by-parts boundary of the stable compensated kernel vanishes. -/
theorem solution
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    Tendsto
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) * ((r ^ (-alpha) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℂ)) := by
  have hzero : 0 < 2 - alpha := by linarith
  have hpower : Tendsto (fun r : ℝ => r ^ (2 - alpha))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)) := by
    have hc : ContinuousAt (fun r : ℝ => r ^ (2 - alpha))
        (0 : ℝ) :=
      Real.continuousAt_rpow_const 0 (2 - alpha)
        (Or.inr hzero.le)
    simpa [Real.zero_rpow (ne_of_gt hzero)] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' ?_ hpower
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with r hr hr1
  exact Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormNearZero
    alpha r h1 h2 hr hr1.le
