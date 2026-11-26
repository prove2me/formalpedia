-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_stopped_grid_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:34:26.955247+00:00
-- url     : https://prove2.me/submissions/f0c91600-50ed-4d58-98a0-eed6953f93ca

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_crossing_card
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_cell_bound
open Set
open scoped NNReal
set_option autoImplicit false

/-- A stopped grid has full cells and at most one partial cell. Its energy is bounded
by full-grid energy plus the squared oscillation bound. -/
theorem solution (X : NNReal → ℝ) (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) (t R : NNReal)
    (hX : ∀ a b : NNReal, a ≤ t → b ≤ t → |X a - X b| ≤ (R : ℝ)) :
    (∑ k ∈ Finset.range n, (X (min t (u (k+1))) - X (min t (u k)))^2) ≤
      (∑ k ∈ Finset.range n, (X (u (k+1)) - X (u k))^2) + (R : ℝ)^2 := by
  classical
  let S := (Finset.range n).filter (fun k => u k < t ∧ t < u (k+1))
  have hcard : S.card ≤ 1 := Kyprianou.Ch04.ito43_stopped_grid_crossing_card u hu n t
  have hterm := Kyprianou.Ch04.ito43_stopped_grid_cell_bound X u hu n t R hX
  calc
    _ ≤ ∑ k ∈ Finset.range n, ((X (u (k+1)) - X (u k))^2 +
        (if k ∈ S then (R : ℝ)^2 else 0)) := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range n, (X (u (k+1)) - X (u k))^2) + (S.card : ℝ)*(R : ℝ)^2 := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      have he : (Finset.range n).filter (fun k => k ∈ S) = S := by
        ext k
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
      rw [he]
      simp
    _ ≤ _ := by
      have h : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg (R : ℝ))]
