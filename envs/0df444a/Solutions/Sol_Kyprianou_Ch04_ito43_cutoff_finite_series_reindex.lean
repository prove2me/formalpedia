-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_finite_series_reindex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:03:23.163203+00:00
-- url     : https://prove2.me/submissions/b12b3b76-fe22-4235-bd5f-aaf629a3edde

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (G : NNReal → ℝ) (T : NNReal) (S : Finset NNReal)
    (hS : ∀ s ∈ S, 0 < s ∧ s ≤ T)
    (hz : ∀ s, 0 < s → s ≤ T → s ∉ S → G s = 0) :
    ∀ t ≤ T, (∑' s : Ioc (0 : NNReal) t, G s) =
      ∑ s ∈ S, if s ≤ t then G s else 0 := by
  classical
  intro t ht
  rw [tsum_subtype]
  have heq : (Ioc (0:NNReal) t).indicator G =
      (fun s => if s ∈ S then (if s ≤ t then G s else 0) else 0) := by
    funext s
    by_cases hm : s ∈ S
    · simp [Set.indicator_apply,hm,(hS s hm).1]
    · by_cases hs : s ∈ Ioc (0:NNReal) t
      · simp [Set.indicator_apply,hs,hm,hz s hs.1 (hs.2.trans ht) hm]
      · simp [Set.indicator_apply,hs,hm]
  rw [heq,tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro s hs
    simp [hs]
  · intro s hs
    simp [hs]
