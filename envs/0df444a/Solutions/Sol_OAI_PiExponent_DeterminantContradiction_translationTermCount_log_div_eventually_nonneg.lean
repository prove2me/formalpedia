-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translationTermCount_log_div_eventually_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:50:32.63688+00:00
-- url     : https://prove2.me/submissions/fd617300-ff77-48af-a3ee-d4927ed4d083

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent
theorem solution
    (m : ℕ) {v : ℝ} (hv : 0 < v) :
    ∀ᶠ H : ℝ in atTop,
      0 ≤ Real.log (translationTermCount m v H : ℝ) / H := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with H hH
  apply div_nonneg _ hH.le
  apply Real.log_nonneg
  have : 1 ≤ translationTermCount m v H := by
    unfold translationTermCount
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact_mod_cast this
