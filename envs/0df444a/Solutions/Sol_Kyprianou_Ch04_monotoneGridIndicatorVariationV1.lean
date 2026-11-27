-- Prove2me | solution 1 for Kyprianou.Ch04.monotoneGridIndicatorVariationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:49:14.774792+00:00
-- url     : https://prove2.me/submissions/043aaf42-2901-4a3f-b959-0bfd7f3aa546

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
open MeasureTheory Set
open scoped NNReal Classical
set_option autoImplicit false

/-- A monotone grid crosses a given jump threshold at most once. -/
theorem solution (v : ℕ → NNReal) (hm : Monotone v) (r : NNReal) (n : ℕ) :
    let J : ℕ → ℝ := fun k => if r ≤ v k then 1 else 0
    (∑ k ∈ Finset.range n, |J (k+1)-J k|) ≤ 1 := by
  intro J
  have hJ : Monotone J := by
    intro i j hij
    by_cases hi : r ≤ v i
    · have hj := hi.trans (hm hij)
      simp [J,hi,hj]
    · simp only [J,if_neg hi]
      split <;> norm_num
  exact Kyprianou.Ch04.kw47_positive_monotone_grid_variation J n 1
    (Or.inl hJ) (by dsimp [J]; split <;> norm_num)
    (by dsimp [J]; split <;> norm_num) (by dsimp [J]; split <;> norm_num)
    (by dsimp [J]; split <;> norm_num)
