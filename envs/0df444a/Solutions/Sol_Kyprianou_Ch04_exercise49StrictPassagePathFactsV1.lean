-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49StrictPassagePathFactsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:05:25.357116+00:00
-- url     : https://prove2.me/submissions/5438e24d-aa20-4011-b123-88f1e349aa76

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Before the first strict negative passage the path is nonnegative, and at finite passage it is nonpositive. -/
theorem solution
    (Y : NNReal → ℝ) (h0 : Y 0 = 0)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (s : NNReal)
    (hs : (s : WithTop NNReal) = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ Y t < 0}) :
    (∀ t : NNReal, t < s → 0 ≤ Y t) ∧ Y s ≤ 0 := by
  constructor
  · intro t ht
    by_contra! hn
    have hp : 0 < t := by
      by_contra! h
      have he : t = 0 := le_antisymm h bot_le
      rw [he, h0] at hn
      exact (lt_irrefl 0) hn
    have hle : (s : WithTop NNReal) ≤ ↑t := by
      rw [hs]
      exact sInf_le ⟨t, rfl, hp, hn⟩
    exact (not_lt_of_ge (WithTop.coe_le_coe.mp hle)) ht
  · by_contra! hp
    have hpos : ∀ᶠ u in nhdsWithin s (Ici s), 0 < Y u :=
      (hr s).tendsto.eventually (eventually_gt_nhds hp)
    have hpos' : ∀ᶠ u in nhdsWithin s (Ioi s), 0 < Y u :=
      hpos.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
    obtain ⟨r, hsr, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hpos'
    have hlt : (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ Y t < 0}) < (r : WithTop NNReal) := by
      rw [← hs]
      exact WithTop.coe_lt_coe.mpr hsr
    obtain ⟨_, ⟨t, rfl, ht0, ht⟩, htr⟩ := sInf_lt_iff.mp hlt
    have hst : s ≤ t := WithTop.coe_le_coe.mp (by
      rw [hs]
      exact sInf_le ⟨t, rfl, ht0, ht⟩)
    have hst' : s < t := lt_of_le_of_ne hst (fun he => (not_lt_of_ge hp.le) (he ▸ ht))
    exact (not_lt_of_ge (hsub ⟨hst', WithTop.coe_lt_coe.mp htr⟩).le) ht
