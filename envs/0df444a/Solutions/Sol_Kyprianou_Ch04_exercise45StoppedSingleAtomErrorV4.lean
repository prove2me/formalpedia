-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StoppedSingleAtomErrorV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:34:47.791177+00:00
-- url     : https://prove2.me/submissions/dd020e70-edfb-47c2-b342-bb2874ec3710

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_uniformGridRightClosedCellExistsV1
import Theorems.Thm_Kyprianou_Ch04_uniformGridSingleAtomLimitV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (T r : NNReal) (hr : 0 < r) (hrT : r ≤ T) (H : NNReal → ℝ)
    (hH : Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal,
      |(∑ i ∈ Finset.range (n+1),
        if min t (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) < r ∧
          r ≤ min t (T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal))
        then H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) else 0) -
        (if r ≤ t then H r else 0)| < δ := by
  intro δ hδ
  choose k hk hc using fun n => Kyprianou.Ch04.uniformGridRightClosedCellExistsV1 T r hr hrT n
  have h := Kyprianou.Ch04.uniformGridSingleAtomLimitV1 T r H k hk hc hH
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 h δ hδ
  refine ⟨N,?_⟩
  intro n hn t
  by_cases ht : r ≤ t
  · rw [if_pos ht]
    have he (i : ℕ) :
        (min t (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) < r ∧
          r ≤ min t (T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal))) ↔
        (T * (i : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
          r ≤ T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)) := by
      simp [min_lt_iff,le_min_iff,ht,not_lt_of_ge ht]
    simp_rw [he]
    simpa [Real.dist_eq] using hN n hn
  · rw [if_neg ht]
    have he : (∑ i ∈ Finset.range (n+1),
        if min t (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) < r ∧
          r ≤ min t (T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal))
        then H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg (fun h => ht (h.2.trans (min_le_left _ _)))]
    rw [he,sub_zero,abs_zero]
    exact hδ