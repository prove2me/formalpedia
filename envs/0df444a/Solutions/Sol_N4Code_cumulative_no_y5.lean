-- Prove2me | solution 1 for N4Code.cumulative_no_y5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:10.142432+00:00
-- url     : https://prove2.me/submissions/71008d07-c299-4d63-9bfb-a8a746551092

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_y_rel_1
import Theorems.Thm_N4Code_y_rel_2
import Theorems.Thm_N4Code_y_rel_3
import Theorems.Thm_N4Code_y_rel_4
import Theorems.Thm_N4Code_Y1_Y4_disjoint
import Theorems.Thm_N4Code_Y2_Y3_disjoint
import Theorems.Thm_N4Code_Y1_Y2_disjoint
import Theorems.Thm_N4Code_Y3_Y4_disjoint
import Theorems.Thm_N4Code_y_mem
import Theorems.Thm_N4Code_compare_bij
import Theorems.Thm_N4Code_compare_bij_eq
import Theorems.Thm_N4Code_compare_bij_strict


set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (h5 : ∀ y : Word n, ¬ Y5 C t y) :
    UniversalBetter C' C ∧
      (UniversalEqual C' C ↔ ∀ y : Word n, ¬ Y3 C t y) := by
  let S : Finset (Word n) := Finset.univ.filter (Y3 C t)
  have hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g1 C t y) := by
    intro y hy
    have h3 : Y3 C t y := (Finset.mem_filter.mp hy).2
    have h := (y_rel_3 C C' t hcol hcol' hsame h3).2
    simp [g1, h3]
    omega
  have heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g1 C t y) := by
    intro y hy
    have h3 : ¬ Y3 C t y := by
      intro h3
      exact hy (Finset.mem_filter.mpr ⟨by simp, h3⟩)
    have hy14 : Y1 C t y ∨ Y2 C t y ∨ Y4 C t y := by
      rcases y_mem C t y with hy' | hy' | hy' | hy' | hy'
      · exact Or.inl hy'
      · exact Or.inr (Or.inl hy')
      · exfalso; exact h3 hy'
      · exact Or.inr (Or.inr hy')
      · exfalso; exact h5 y hy'
    rcases hy14 with hy1 | hy2 | hy4
    · have h := y_rel_1 C C' t hcol hcol' hsame hy1
      simp [g1, hy1, h.1]
    · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y2_disjoint C t y ⟨hy1, hy2⟩
      have h3' : ¬ Y3 C t y := fun hy3 => Y2_Y3_disjoint C t y ⟨hy2, hy3⟩
      have hg1 : g1 C t y = flipBit t y := by
        simp [g1, h1, h3']
      rw [hg1]
      exact (y_rel_2 C C' t hcol hcol' hsame hy2).1
    · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y4_disjoint C t y ⟨hy1, hy4⟩
      have h3' : ¬ Y3 C t y := fun hy3 => Y3_Y4_disjoint C t y ⟨hy3, hy4⟩
      have hg1 : g1 C t y = flipBit t y := by
        simp [g1, h1, h3']
      rw [hg1]
      exact (y_rel_4 C C' t hcol hcol' hsame hy4).2.1
  constructor
  · exact compare_bij C C' S (g1Equiv C t) hgt heq
  · constructor
    · intro heq2 y h3
      have hne : ∃ y : Word n, y ∈ S := ⟨y, Finset.mem_filter.mpr ⟨by simp, h3⟩⟩
      have hstrict := compare_bij_strict C C' S (g1Equiv C t) hgt heq hne
      have hgt' : lambda C' (1 / 4 : ℝ) > lambda C (1 / 4) :=
        hstrict (1 / 4) (by norm_num) (by norm_num)
      have heq' : lambda C' (1 / 4 : ℝ) = lambda C (1 / 4) :=
        heq2 (1 / 4) (by norm_num) (by norm_num)
      exact (lt_irrefl _ (hgt'.trans_eq heq')).elim
    · intro hy3
      have heqall : ∀ y : Word n, dCode C y = dCode C' (g1 C t y) := by
        intro y
        by_cases hy : y ∈ S
        · exact False.elim (hy3 y (Finset.mem_filter.mp hy).2)
        · exact heq y hy
      exact compare_bij_eq C C' (g1Equiv C t) heqall
end N4Code
