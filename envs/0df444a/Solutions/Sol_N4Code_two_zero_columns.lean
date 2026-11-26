-- Prove2me | solution 1 for N4Code.two_zero_columns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:39.449882+00:00
-- url     : https://prove2.me/submissions/2db1ef1c-e37d-4d90-a7d1-086b5a23ddb6

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_zero_column_better
import Theorems.Thm_N4Code_zero_column
import Theorems.Thm_N4Code_exists_col0_of_count_pos
import Theorems.Thm_N4Code_zero_column_strict
import Theorems.Thm_N4Code_twobitCount_equiv
import Theorems.Thm_N4Code_twobitCount_C0form
import Theorems.Thm_N4Code_twobitCount_replace_0_5
import Theorems.Thm_N4Code_count_replace_0_nonzero
import Theorems.Thm_N4Code_col0_ne_of_colVal_356
import Theorems.Thm_N4Code_strict_of_better_strict

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : count C 0 ≥ 2) :
    ∃ t₁ t₂ : Fin n, t₁ ≠ t₂ ∧ C t₁ = col0 ∧ C t₂ = col0 ∧
      ∃ s₁ s₂ : Column,
        (colVal s₁ = 3 ∨ colVal s₁ = 5 ∨ colVal s₁ = 6) ∧
        (colVal s₂ = 3 ∨ colVal s₂ = 5 ∨ colVal s₂ = 6) ∧
          UniversalStrictBetter (replaceColumn (replaceColumn C t₁ s₁) t₂ s₂) C := by
  by_cases hC0 : ∃ C0 : Code n, Equivalent C C0 ∧ C0form C0
  · -- case B: C is equivalent to the C0 code
    rcases hC0 with ⟨C0, hEqC0, hC0form⟩
    rcases exists_col0_of_count_pos C (by omega : 1 ≤ count C 0) with ⟨t₁, ht₁⟩
    let Cn : Code n := replaceColumn C t₁ col5
    have hcntn : 1 ≤ count Cn 0 := by
      have hc := count_replace_0_nonzero C t₁ col5 ht₁ (by decide : col5 ≠ col0)
      rw [hc]
      have h' : 1 < count C 0 := by omega
      exact Nat.le_pred_of_lt h'
    have hnotC0n : ¬ ∃ C0' : Code n, Equivalent Cn C0' ∧ C0form C0' := by
      intro hb
      rcases hb with ⟨C0', hEqn, hC0form'⟩
      have htw := twobitCount_equiv hEqn
      have hevenC0' : Even (twobitCount C0') := twobitCount_C0form C0' hC0form'
      have htwC : twobitCount Cn = twobitCount C + 1 := twobitCount_replace_0_5 C t₁ ht₁
      have htwC0 : twobitCount C = twobitCount C0 := twobitCount_equiv hEqC0
      have hevenC0 : Even (twobitCount C0) := twobitCount_C0form C0 hC0form
      have hoddn : Odd (twobitCount Cn) := by
        rcases hevenC0 with ⟨k, hk⟩
        rw [htwC, htwC0, hk]
        refine ⟨k, ?_⟩
        omega
      have : Even (twobitCount Cn) := by rwa [← htw] at hevenC0'
      rcases hoddn with ⟨a, ha⟩
      rcases this with ⟨b, hb⟩
      omega
    rcases zero_column_strict Cn hcntn (by simpa [C0form] using hnotC0n) with
      ⟨t₂, ht₂, s₂, hs₂, hstrict₂⟩
    have ht₂C : C t₂ = col0 := by
      -- t₂ is a 0-column of Cn and t₂ ≠ t₁, so it is unchanged in C
      have hne : t₂ ≠ t₁ := by
        intro heq
        subst t₁
        have : Cn t₂ = col0 := ht₂
        simp [Cn, replaceColumn] at this
        have hcv0 : colVal col5 = 0 := by
          rw [this]
          decide
        have hcv5 : colVal col5 = 5 := by decide
        omega
      simpa [Cn, replaceColumn, hne] using ht₂
    have heq : UniversalEqual Cn C :=
      zero_column C t₁ ht₁ (⟨C0, hEqC0, hC0form⟩) col5
    have hstrictC : UniversalStrictBetter (replaceColumn Cn t₂ s₂) C := by
      intro ε hε0 hε1
      have h1 : lambda (replaceColumn Cn t₂ s₂) ε > lambda Cn ε := hstrict₂ ε hε0 hε1
      have h2 : lambda Cn ε = lambda C ε := heq ε hε0 hε1
      rwa [h2] at h1
    refine ⟨t₁, t₂, ?_, ht₁, ht₂C, col5, s₂, ?_, hs₂, ?_⟩
    · intro heq
      subst t₁
      have : Cn t₂ = col0 := ht₂
      simp [Cn, replaceColumn] at this
      have hcv0 : colVal col5 = 0 := by
        rw [this]
        decide
      have hcv5 : colVal col5 = 5 := by decide
      omega
    · exact Or.inr (Or.inl (by decide : colVal col5 = 5))
    · simpa [Cn] using hstrictC
  · -- case A: C is not equivalent to the C0 code
    rcases zero_column_strict C (by omega : 1 ≤ count C 0) (by simpa [C0form] using hC0) with
      ⟨t₁, ht₁, s₁, hs₁, hstrict₁⟩
    let Cn : Code n := replaceColumn C t₁ s₁
    have hs₁' : s₁ ≠ col0 := col0_ne_of_colVal_356 hs₁
    have hcntn : 1 ≤ count Cn 0 := by
      have hc := count_replace_0_nonzero C t₁ s₁ ht₁ hs₁'
      rw [hc]
      have h' : 1 < count C 0 := by omega
      exact Nat.le_pred_of_lt h'
    rcases exists_col0_of_count_pos Cn hcntn with ⟨t₂, ht₂⟩
    have hne : t₂ ≠ t₁ := by
      intro heq
      subst t₁
      have : Cn t₂ = col0 := ht₂
      simp [Cn, replaceColumn] at this
      exact hs₁' this
    have ht₂C : C t₂ = col0 := by
      simpa [Cn, replaceColumn, hne] using ht₂
    have hbetter : UniversalBetter (replaceColumn Cn t₂ col5) Cn :=
      (zero_column_better Cn t₂ col5 ht₂ colZeros_col5_nonempty colOnes_col5_nonempty).1
    have hstrict : UniversalStrictBetter (replaceColumn Cn t₂ col5) C :=
      strict_of_better_strict _ _ _ hbetter hstrict₁
    refine ⟨t₁, t₂, hne.symm, ht₁, ht₂C, s₁, col5, hs₁, ?_, ?_⟩
    · exact Or.inr (Or.inl (by decide : colVal col5 = 5))
    · simpa [Cn] using hstrict
end N4Code
