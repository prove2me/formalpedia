-- Prove2me | solution 2 for MarkovProcess.ContinuousPath.survivalSet_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:02:49.661847+00:00
-- url     : https://prove2.me/submissions/34b069dc-f865-420b-b26f-8292dae54ae3

import Mathlib

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
theorem solution :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} ∩ Set.Ioi 0 = Set.Ioi 0 := by
  ext t; simp
