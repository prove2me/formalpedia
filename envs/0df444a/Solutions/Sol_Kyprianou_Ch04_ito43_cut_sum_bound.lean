-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cut_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:30:54.435947+00:00
-- url     : https://prove2.me/submissions/0e6d4e53-b089-4a95-ba0e-c6d52b27c246

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_cell_geometry
open Set
set_option autoImplicit false

/-- Sum cell errors with an extra charge on the unique strictly cut cell. -/
theorem solution (u : ℕ → ℝ) (hu : Monotone u) (t c : ℝ) (hc : 0 ≤ c)
    (n : ℕ) (a b : ℕ → ℝ)
    (h : ∀ k < n, a k ≤ b k + if u k < t ∧ t < u (k+1) then c else 0) :
    (∑ k ∈ Finset.range n, a k) ≤ (∑ k ∈ Finset.range n, b k) + c := by
  classical
  let C := (Finset.range n).filter (fun k => u k < t ∧ t < u (k+1))
  have hcard : C.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact Kyprianou.Ch04.ito43_stopped_cell_geometry u hu t i j
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  calc
    _ ≤ ∑ k ∈ Finset.range n, (b k + if u k < t ∧ t < u (k+1) then c else 0) :=
      Finset.sum_le_sum fun k hk => h k (Finset.mem_range.mp hk)
    _ = (∑ k ∈ Finset.range n, b k) + (C.card : ℝ) * c := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [C]
    _ ≤ _ := by
      have hcr : (C.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      linarith [mul_le_mul_of_nonneg_right hcr hc]
