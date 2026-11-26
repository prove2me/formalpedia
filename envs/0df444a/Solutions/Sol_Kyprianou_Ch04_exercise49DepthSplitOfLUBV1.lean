-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DepthSplitOfLUBV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:47:58.970847+00:00
-- url     : https://prove2.me/submissions/8e9c58a1-7ecd-478f-ba51-f55cc293bf28

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- The all-time depth splits into the first deficit and the shifted future depth. -/
theorem solution
    (Y : NNReal → ℝ) (t : NNReal) (d e : ℝ)
    (hpre : ∀ u : NNReal, u < t → 0 ≤ Y u)
    (ht : Y t ≤ 0)
    (hd : IsLUB (Set.range (fun u => -Y u)) d)
    (he : IsLUB (Set.range (fun u => -(Y (t + u) - Y t))) e) :
    d = -Y t + e := by
  have he0 : 0 ≤ e := by simpa using he.1 (Set.mem_range_self (0 : NNReal))
  apply le_antisymm
  · apply hd.2
    rintro x ⟨u, rfl⟩
    by_cases hu : u < t
    · linarith [hpre u hu]
    · have htu : t ≤ u := le_of_not_gt hu
      have hh := he.1 (Set.mem_range_self (u - t))
      change -(Y (t + (u - t)) - Y t) ≤ e at hh
      rw [add_tsub_cancel_of_le htu] at hh
      linarith
  · have hle : e ≤ d + Y t := by
      apply he.2
      rintro x ⟨u, rfl⟩
      have hh := hd.1 (Set.mem_range_self (t + u))
      change -Y (t + u) ≤ d at hh
      linarith
    linarith
