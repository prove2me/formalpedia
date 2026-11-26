-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41SuccessfulCellCardV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:43:17.618801+00:00
-- url     : https://prove2.me/submissions/c2922e61-c84b-46b2-8d96-528ee9151ecd

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

/-- If chosen times in occupied cells have all ordered pair gaps less than the cell width, all occupied cell indices lie among the smallest index and its successor. -/
theorem solution
    (A : Finset ℕ) (τ : ℕ → ℝ) (a h : ℝ) (hh : 0 < h)
    (hcell : ∀ i ∈ A, a + (i : ℝ) * h ≤ τ i ∧
      τ i < a + ((i : ℝ) + 1) * h)
    (hgap : ∀ i ∈ A, ∀ j ∈ A, i < j → τ j - τ i < h) :
    A.card ≤ 2 := by
  classical
  by_cases hA : A.Nonempty
  · let m := A.min' hA
    have hm : m ∈ A := A.min'_mem hA
    have hsub : A ⊆ ({m, m + 1} : Finset ℕ) := by
      intro i hi
      have hmi : m ≤ i := Finset.min'_le A i hi
      by_cases he : i = m
      · simp [he]
      have hlt : m < i := by omega
      have hδ := hgap m hm i hi hlt
      have hmcell := (hcell m hm).2
      have hicell := (hcell i hi).1
      have hi2 : i < m + 2 := by
        by_contra! hn
        have hnR : (m : ℝ) + 2 ≤ (i : ℝ) := by exact_mod_cast hn
        have hp := mul_le_mul_of_nonneg_right hnR hh.le
        linarith
      have hi1 : i = m + 1 := by omega
      simp [hi1]
    calc
      A.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by simp
  · have hEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [hEmpty]
