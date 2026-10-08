-- Prove2me | solution 1 for KelsoCrawford.NoCore.first_efficient_assignment_not_core
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:50:11.039767+00:00
-- url     : https://prove2.me/submissions/b984fea2-1cc6-48c6-8449-e8df28127407

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
theorem solution (A : Allocation (Fin 3) (Fin 2))
    (hj : A.hired 0 = {0}) (hk : A.hired 1 = {1, 2}) :
    ¬ noCoreMarket.IsCore KelsoCrawford.ContinuousCore.anySalary A := by
  intro h
  have h1 := core_bound A h 0 {2}
  have h2 := core_bound A h 0 {0, 1}
  have h3 := core_bound A h 1 {0}
  have h4 := core_bound A h 1 {2}
  simp +decide [hj, hk, noCoreMarket, profit, techJ, techK] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  linarith
#print axioms solution
