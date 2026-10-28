-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.survivalSet_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T01:02:34.743197+00:00
-- url     : https://prove2.me/submissions/7f9fb557-c18e-4aaf-94b5-0f5463bbc20f

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

/-- Source: MarkovProcess/Path/ExitTime.lean:42-47 at pinned commit. -/
theorem solution :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} ∩ Set.Ioi 0 = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
  exact and_iff_right ENNReal.coe_lt_top
