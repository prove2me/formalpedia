-- Prove2me | solution 1 for N4Code.Columns07_sum_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:35.955263+00:00
-- url     : https://prove2.me/submissions/2a58a19f-0321-4b29-a250-989d66891137

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_Columns07_le7
import Theorems.Thm_N4Code_count_eq_card
import Theorems.Thm_N4Code_sum_counts_eq_n


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    (∑ i ∈ Finset.Icc 0 7, count C i) = n := by
  have hsum := sum_counts_eq_n C
  have hzero : ∀ i ∈ Finset.Icc 8 15, count C i = 0 := by
    intro i hi
    rw [count_eq_card]
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro t ht
    have hcv : colVal (C t) = i := (Finset.mem_filter.mp ht).2
    have hle := Columns07_le7 C h07 t
    simp [Finset.mem_Icc] at hi
    omega
  have hS : (Finset.Icc 0 7 : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  -- Σ_{0..15} = Σ_{0..7} + Σ_{8..15}, and the latter is 0
  have hsplit : (∑ i ∈ Finset.Icc 0 15, count C i) =
      (∑ i ∈ Finset.Icc 0 7, count C i) +
        ∑ i ∈ Finset.Icc 0 15 \ (Finset.Icc 0 7 : Finset ℕ), count C i := by
    rw [← Finset.sum_sdiff hS]
    rw [add_comm]
  have hrest : (∑ i ∈ Finset.Icc 0 15 \ (Finset.Icc 0 7 : Finset ℕ), count C i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi8 : 8 ≤ i := by
      rw [Finset.mem_sdiff] at hi
      simp [Finset.mem_Icc] at hi
      omega
    have hi15 : i ≤ 15 := by
      rw [Finset.mem_sdiff] at hi
      simp [Finset.mem_Icc] at hi
      omega
    exact hzero i (by simp [Finset.mem_Icc, hi8, hi15])
  omega
end N4Code
