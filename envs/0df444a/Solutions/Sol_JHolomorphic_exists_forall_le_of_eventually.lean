-- Prove2me | solution 1 for JHolomorphic.exists_forall_le_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T23:54:30.435667+00:00
-- url     : https://prove2.me/submissions/093ca33d-06e5-4d28-bad6-47431a3be2b0

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Data.ENNReal.BigOperators



namespace JHolomorphic

open scoped ENNReal NNReal

theorem exists_forall_le_of_eventually_aux {f : ℕ → ℝ≥0∞} (hf : ∀ ν, f ν ≠ ⊤)
    (h : ∃ N : ℕ, ∃ C : ℝ≥0, ∀ ν, N ≤ ν → f ν ≤ C) : ∃ C : ℝ≥0, ∀ ν, f ν ≤ C := by
  obtain ⟨N, C, hC⟩ := h
  refine ⟨max C (∑ ν ∈ Finset.range N, (f ν).toNNReal), fun ν => ?_⟩
  rcases lt_or_ge ν N with hν | hν
  · rw [← ENNReal.coe_toNNReal (hf ν)]
    refine ENNReal.coe_le_coe.2 (le_max_of_le_right ?_)
    exact Finset.single_le_sum (f := fun ν => (f ν).toNNReal) (fun _ _ => bot_le)
      (Finset.mem_range.2 hν)
  · exact (hC ν hν).trans (ENNReal.coe_le_coe.2 (le_max_left _ _))

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem solution {f : ℕ → ℝ≥0∞} (hf : ∀ ν, f ν ≠ ⊤)
    (h : ∃ N : ℕ, ∃ C : ℝ≥0, ∀ ν, N ≤ ν → f ν ≤ C) : ∃ C : ℝ≥0, ∀ ν, f ν ≤ C :=
  exists_forall_le_of_eventually_aux hf h
