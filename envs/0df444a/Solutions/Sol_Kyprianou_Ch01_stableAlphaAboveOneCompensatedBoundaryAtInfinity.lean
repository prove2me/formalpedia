-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryAtInfinity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:01:23.32053+00:00
-- url     : https://prove2.me/submissions/538e25d7-a592-41a9-9ff1-ef2bf538c700

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedBoundaryNormTail
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Upper integration-by-parts boundary of the stable compensated kernel vanishes. -/
theorem solution
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    Tendsto
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) * ((r ^ (-alpha) : ℝ) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
  have hpower : Tendsto
      (fun r : ℝ => 2 * r ^ (1 - alpha))
      Filter.atTop (nhds (0 : ℝ)) := by
    have ht := tendsto_rpow_neg_atTop
      (show 0 < alpha - 1 by linarith)
    have heq :
        (fun r : ℝ => 2 * r ^ (1 - alpha)) =
          (fun r : ℝ => 2 * r ^ (-(alpha - 1))) := by
      funext r
      congr 1
      ring
    rw [heq]
    simpa only [mul_zero] using ht.const_mul 2
  apply squeeze_zero_norm' ?_ hpower
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  exact Kyprianou.Ch01.stableAlphaAboveOneCompensatedBoundaryNormTail
    alpha r h1 h2 hr
