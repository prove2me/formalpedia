-- Prove2me | solution 1 for N4Code.zero_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:12.073414+00:00
-- url     : https://prove2.me/submissions/68948ef8-b942-446a-b817-67d048a12065

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_zero_column_C0
import Theorems.Thm_N4Code_count_eq_card
import Theorems.Thm_N4Code_lambda_equiv
import Theorems.Thm_N4Code_sum_counts_eq_n


set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (h0 : C t = col0)
    (hC0 : ∃ C0 : Code n, Equivalent C C0 ∧
      count C0 0 + count C0 5 + count C0 6 = n ∧
        Odd (count C0 5) ∧ Odd (count C0 6)) :
    ∀ s' : Column, UniversalEqual (replaceColumn C t s') C := by
  rcases hC0 with ⟨C0, hEq, hcnt, h5, h6⟩
  have hEq_full : Equivalent C C0 := hEq
  rcases hEq with ⟨ρ, p, f, hh⟩
  have hC0struct : ∀ u : Fin n, colVal (C0 u) = 0 ∨ colVal (C0 u) = 5 ∨ colVal (C0 u) = 6 := by
    intro u
    let i : ℕ := colVal (C0 u)
    have hcnti : 1 ≤ count C0 i := by
      have hmem : u ∈ (Finset.univ.filter fun t : Fin n => colVal (C0 t) = i) := by
        simp [i]
      have hcard : 1 ≤ (Finset.univ.filter fun t : Fin n => colVal (C0 t) = i).card := by
        exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨u, hmem⟩)
      rw [count_eq_card]
      exact hcard
    by_contra h
    have hS : ({0, 5, 6} : Finset ℕ) ⊆ Finset.Icc 0 15 := by
      intro x hx
      simp at hx ⊢
      omega
    have hsumS : (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C0 j) = n := by
      simp [Finset.sum_insert]
      omega
    have hsumAll : (∑ j ∈ Finset.Icc 0 15, count C0 j) = n := sum_counts_eq_n C0
    have hcomp : (∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 j) = 0 := by
      have hsplit : (∑ j ∈ Finset.Icc 0 15, count C0 j) =
          (∑ j ∈ ({0, 5, 6} : Finset ℕ), count C0 j) +
            ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 j := by
        rw [← Finset.sum_sdiff hS]
        rw [add_comm]
      omega
    have hile : i ≤ 15 := by
      exact colVal_le_15 (C0 u)
    have hi : i ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ) := by
      rw [Finset.mem_sdiff]
      constructor
      · simp [Finset.mem_Icc, hile]
      · intro hiS
        simp at hiS
        exact h hiS
    have hle : count C0 i ≤ ∑ j ∈ Finset.Icc 0 15 \ ({0, 5, 6} : Finset ℕ), count C0 j := by
      exact Finset.single_le_sum (by intro j _; exact Nat.zero_le _) hi
    have hzero : count C0 i = 0 := by omega
    omega
  intro s'
  have hEq' : Equivalent (replaceColumn C t s')
      (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) := by
    refine ⟨ρ, p, f, ?_⟩
    intro u
    by_cases hu : u = t
    · subst u
      simp [replaceColumn]
    · have hpu : p u ≠ p t := by
        intro h
        exact hu (p.injective h)
      simp [replaceColumn, hu, hpu, hh u]
  have h0' : C0 (p t) = col0 := by
    have hh' : C0 (p t) = rowPermute ρ (if f t then flipCol (C t) else C t) := hh t
    have hf : f t = false := by
      by_contra hft
      have hft' : f t = true := by
        cases hfb : f t
        · exfalso
          exact hft hfb
        · rfl
      have hc : colVal (C0 (p t)) = 15 := by
        have hsub : C0 (p t) = rowPermute ρ (flipCol col0) := by
          rw [hh', hft', h0]
          simp
        have hall : rowPermute ρ (flipCol col0) = col15 := by
          funext k
          simp [rowPermute, flipCol, col0, col15]
        have hcv : colVal col15 = 15 := by decide
        rw [hsub, hall]
        exact hcv
      rcases hC0struct (p t) with h0'' | h5'' | h6''
      · omega
      · omega
      · omega
    calc
      C0 (p t) = rowPermute ρ (if f t then flipCol (C t) else C t) := hh'
      _ = rowPermute ρ col0 := by rw [hf, h0]; simp
      _ = col0 := by
        funext k
        simp [rowPermute, col0]
  have heq_all := zero_column_C0 C0 (p t) h0' hC0struct h5 h6
    (rowPermute ρ (if f t then flipCol s' else s'))
  intro ε hε0 hε1
  have hleft : lambda (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) ε =
      lambda C0 ε := heq_all ε hε0 hε1
  have hC : Equivalent C C0 := hEq_full
  calc
    lambda (replaceColumn C t s') ε =
        lambda (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) ε :=
      (lambda_equiv (replaceColumn C t s')
        (replaceColumn C0 (p t) (rowPermute ρ (if f t then flipCol s' else s'))) hEq' ε).symm
    _ = lambda C0 ε := hleft
    _ = lambda C ε := lambda_equiv C C0 hC ε
end N4Code
