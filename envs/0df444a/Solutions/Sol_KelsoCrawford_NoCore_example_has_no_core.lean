-- Prove2me | solution 1 for KelsoCrawford.NoCore.example_has_no_core
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:11:18.333497+00:00
-- url     : https://prove2.me/submissions/21bc82f1-9589-49a7-b187-67f7ec855fb1

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Example
open KelsoCrawford.NoCore
open KelsoCrawford.Process (profit)
set_option maxHeartbeats 0
set_option maxRecDepth 4096
private theorem core_bound (A : Allocation (Fin 3) (Fin 2))
    (h : noCoreMarket.IsCore KelsoCrawford.ContinuousCore.anySalary A)
    (j : Fin 2) (C : Finset (Fin 3)) :
    profit (noCoreMarket.y j) C A.sal ≤
      profit (noCoreMarket.y j) (A.hired j) A.sal := by
  by_contra hn
  have gap : 0 < profit (noCoreMarket.y j) C A.sal -
      profit (noCoreMarket.y j) (A.hired j) A.sal := by linarith
  let n : ℝ := C.card
  let e := (profit (noCoreMarket.y j) C A.sal -
      profit (noCoreMarket.y j) (A.hired j) A.sal) / (2 * (n + 1))
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have he : 0 < e := div_pos gap (by positivity)
  have heq : e * (2 * (n + 1)) = profit (noCoreMarket.y j) C A.sal -
      profit (noCoreMarket.y j) (A.hired j) A.sal := by
    dsimp [e]; exact div_mul_cancel₀ _ (by positivity)
  apply h.2.2
  refine ⟨j, C, (fun i => A.sal i + e), ?_, ?_, ?_⟩
  · simp [KelsoCrawford.ContinuousCore.anySalary]
  · intro i hi; change A.sal i < A.sal i + e; linarith
  · simp only [profit, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    change noCoreMarket.y j (A.hired j) - ∑ i ∈ A.hired j, A.sal i <
      noCoreMarket.y j C - ((∑ i ∈ C, A.sal i) + n * e)
    dsimp [profit] at heq
    nlinarith
theorem solution :
    ¬ ∃ A : Allocation (Fin 3) (Fin 2), noCoreMarket.IsCore KelsoCrawford.ContinuousCore.anySalary A := by
  rintro ⟨A, h⟩
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  generalize h0 : A.assign 0 = a0
  generalize h1 : A.assign 1 = a1
  generalize h2 : A.assign 2 = a2
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2
  · have hj : A.hired 0 = {0, 1, 2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = ∅ := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 0 {0}
    have b1 := core_bound A h 1 {1, 2}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1
    linarith
  · have hj : A.hired 0 = {0, 1} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = {2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 1 {0}
    have b1 := core_bound A h 1 {1, 2}
    have b2 := core_bound A h 0 {2}
    have b3 := core_bound A h 0 {0}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1 b2 b3
    linarith
  · have hj : A.hired 0 = {0, 2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = {1} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 0 {0}
    have b1 := core_bound A h 1 {1, 2}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1
    linarith
  · have hj : A.hired 0 = {0} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = {1, 2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 0 {2}
    have b1 := core_bound A h 0 {0, 1}
    have b2 := core_bound A h 1 {0}
    have b3 := core_bound A h 1 {2}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1 b2 b3
    linarith
  · have hj : A.hired 0 = {1, 2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = {0} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 0 {0}
    have b1 := core_bound A h 1 {1, 2}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1
    linarith
  · have hj : A.hired 0 = {1} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = {0, 2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 0 {0}
    have b1 := core_bound A h 1 {1, 2}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1
    linarith
  · have hj : A.hired 0 = {2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = {0, 1} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 0 {0}
    have b1 := core_bound A h 1 {1, 2}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1
    linarith
  · have hj : A.hired 0 = ∅ := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have hk : A.hired 1 = {0, 1, 2} := by
      simp +decide [Allocation.hired, hu, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton]
    have b0 := core_bound A h 0 {0}
    have b1 := core_bound A h 1 {1, 2}
    simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at b0 b1
    linarith
#print axioms solution
