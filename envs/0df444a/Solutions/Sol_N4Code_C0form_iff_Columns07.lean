-- Prove2me | solution 1 for N4Code.C0form_iff_Columns07
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:12.142806+00:00
-- url     : https://prove2.me/submissions/6f8f9b8f-168d-4e6a-aa96-18b79ec3d780

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_Columns07_sum_counts
import Theorems.Thm_N4Code_Icc0_7_eq
import Theorems.Thm_N4Code_disjoint_056_12347

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h07 : Columns07 C) :
    C0form C ↔ (count C 1 = 0 ∧ count C 2 = 0 ∧ count C 3 = 0 ∧ count C 4 = 0 ∧
      count C 7 = 0 ∧ Odd (count C 5) ∧ Odd (count C 6)) := by
  constructor
  · intro h
    rcases h with ⟨hcnt, h5, h6⟩
    have hsum := Columns07_sum_counts C h07
    -- Σ_{0..7} = n = |0|+|5|+|6| → the rest sum to 0
    have hrest : (∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i) = 0 := by
      have hS : ({1, 2, 3, 4, 7} : Finset ℕ) ⊆ Finset.Icc 0 7 := by
        intro i hi
        simp at hi ⊢
        omega
      have hsplit : (∑ i ∈ Finset.Icc 0 7, count C i) =
          (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C i) +
            ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        rw [Icc0_7_eq, Finset.sum_union disjoint_056_12347]
      have hS05 : (∑ i ∈ ({0, 5, 6} : Finset ℕ), count C i) = n := by
        simp [Finset.sum_insert]
        omega
      omega
    have h1 : count C 1 = 0 := by
      have hle : count C 1 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h2 : count C 2 = 0 := by
      have hle : count C 2 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h3 : count C 3 = 0 := by
      have hle : count C 3 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h4 : count C 4 = 0 := by
      have hle : count C 4 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    have h7 : count C 7 = 0 := by
      have hle : count C 7 ≤ ∑ i ∈ ({1, 2, 3, 4, 7} : Finset ℕ), count C i := by
        exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) (by simp)
      omega
    exact ⟨h1, h2, h3, h4, h7, h5, h6⟩
  · intro h
    rcases h with ⟨h1, h2, h3, h4, h7, h5, h6⟩
    have hsum := Columns07_sum_counts C h07
    -- Σ_{0..7} = |0|+|5|+|6| since the others vanish
    have hcnt : count C 0 + count C 5 + count C 6 = n := by
      rw [Icc0_7_eq, Finset.sum_union disjoint_056_12347] at hsum
      simp [Finset.sum_insert, h1, h2, h3, h4, h7] at hsum
      omega
    exact ⟨hcnt, h5, h6⟩
end N4Code
