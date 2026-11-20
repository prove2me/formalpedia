-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaImaginaryDampingEnvelopeIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:58:42.239348+00:00
-- url     : https://prove2.me/submissions/0c2e3d1a-10df-4bb3-a227-0cf91f25288e

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaPowerEnvelopeIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The source-exact uniform damping envelope is integrable for 0 < alpha < 1. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) (w : ℂ) :
    IntegrableOn
      (fun x : ℝ => (‖w‖ + 2) *
        (if x ≤ 1 then x ^ (-alpha) else x ^ (-alpha - 1)))
      (Set.Ioi (0 : ℝ)) volume := by
  have hbase :=
    Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
      alpha 1 h0 h1 (by norm_num)
  change Integrable
    (fun x : ℝ => (‖w‖ + 2) *
      (if x ≤ 1 then x ^ (-alpha) else x ^ (-alpha - 1)))
    (volume.restrict (Set.Ioi (0 : ℝ)))
  simpa only [one_mul] using (hbase.const_mul (‖w‖ + 2))
