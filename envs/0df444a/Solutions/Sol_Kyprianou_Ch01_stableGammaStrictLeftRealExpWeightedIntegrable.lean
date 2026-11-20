-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftRealExpWeightedIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:36:39.292708+00:00
-- url     : https://prove2.me/submissions/2f317e81-d443-4ca1-9c4f-0b59cc7ccfe7

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

/-- Real Gamma envelope is integrable at every negative exponential rate. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (t : ℝ) (ht : t < 0) :
    IntegrableOn (fun r : ℝ => Real.exp (t * r) * r ^ (-alpha))
      (Set.Ioi (0 : ℝ)) := by
  have hb : 0 < -t := by linarith
  have hs : (-1 : ℝ) < -alpha := by linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := -alpha) (b := -t)
    hs (by norm_num) hb
  simpa only [Real.rpow_one, neg_mul, neg_neg, mul_comm] using h
