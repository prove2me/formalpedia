-- Prove2me | solution 1 for N4Code.C0form_types
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:24.802844+00:00
-- url     : https://prove2.me/submissions/47a93b19-a7b4-42a1-8290-a20a2d79ad1e

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_count_eq_card
import Theorems.Thm_N4Code_sum_counts_eq_n


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : C0form C) (t : Fin n) :
    colVal (C t) = 0 ∨ colVal (C t) = 5 ∨ colVal (C t) = 6 := by
  let i : ℕ := colVal (C t)
  have hcnti : 1 ≤ count C i := by
    have hmem : t ∈ (Finset.univ.filter fun u : Fin n => colVal (C u) = i) := by
      simp [i]
    have hcard : 1 ≤ (Finset.univ.filter fun u : Fin n => colVal (C u) = i).card := by
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨t, hmem⟩)
    rw [count_eq_card]
    exact hcard
  have hS : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
    intro x hx
    simp at hx ⊢
    omega
  have hcnt0 : count C 0 + count C 5 + count C 6 = n := h.1
  have hsumS : (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C j) = n := by
    have hs : (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C j) = count C 0 + (count C 5 + count C 6) := by
      simp [Finset.sum_insert]
    rw [hs]
    omega
  have hsumAll : (∑ j ∈ Finset.Icc 0 15, count C j) = n := sum_counts_eq_n C
  have hcomp : (∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C j) = 0 := by
    have hsplit : (∑ j ∈ Finset.Icc 0 15, count C j) =
        (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C j) +
          ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C j := by
      rw [← Finset.sum_sdiff hS]
      rw [add_comm]
    omega
  have hile : i ≤ 15 := colVal_le_15 (C t)
  by_contra h
  have hi : i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ) := by
    rw [Finset.mem_sdiff]
    constructor
    · simp [Finset.mem_Icc, hile]
    · intro hiS
      simp at hiS
      exact h hiS
  have hle : count C i ≤ ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C j := by
    exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) hi
  have hzero : count C i = 0 := by omega
  omega
end N4Code
