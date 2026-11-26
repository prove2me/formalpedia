-- Prove2me | solution 1 for N4Code.lambda_diff_y3y5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:17.903416+00:00
-- url     : https://prove2.me/submissions/626991b5-8b86-4a0c-9c9d-5e44895fbf78

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_y_rel_1
import Theorems.Thm_N4Code_y_rel_2
import Theorems.Thm_N4Code_y_rel_3
import Theorems.Thm_N4Code_y_rel_4
import Theorems.Thm_N4Code_y_rel_5
import Theorems.Thm_N4Code_Y1_Y4_disjoint
import Theorems.Thm_N4Code_Y1_Y5_disjoint
import Theorems.Thm_N4Code_Y2_Y3_disjoint
import Theorems.Thm_N4Code_g1_involutive
import Theorems.Thm_N4Code_Y1_Y2_disjoint
import Theorems.Thm_N4Code_Y3_Y4_disjoint
import Theorems.Thm_N4Code_Y3_Y5_disjoint
import Theorems.Thm_N4Code_y_mem

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (ε : ℝ) :
    lambda C' ε - lambda C ε =
      (1 / 4 : ℝ) *
        ((∑ y ∈ Finset.univ.filter (Y3 C t),
            (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) +
         (∑ y ∈ Finset.univ.filter (Y5 C t),
            (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))) := by
  unfold lambda
  rw [← mul_sub]
  congr 1
  have hg : (∑ y : Word n, weight n ε (dCode C' y)) =
      ∑ y : Word n, weight n ε (dCode C' (g1 C t y)) := by
    refine Finset.sum_bij (fun y _ => g1Equiv C t y) ?_ ?_ ?_ ?_
    · intro y _; exact Finset.mem_univ _
    · intro a _ b _ hab
      exact (g1Equiv C t).injective hab
    · intro b _
      refine ⟨g1Equiv C t b, Finset.mem_univ _, ?_⟩
      change g1 C t (g1 C t b) = b
      exact g1_involutive C t b
    · intro y _
      have hg1 : g1 C t (g1Equiv C t y) = y := by
        change g1 C t (g1 C t y) = y
        exact g1_involutive C t y
      rw [hg1]
  change (∑ y : Word n, weight n ε (dCode C' y)) - ∑ y : Word n, weight n ε (dCode C y) =
      (∑ y ∈ Finset.univ.filter (Y3 C t),
          (weight n ε (dCode C y - 1) - weight n ε (dCode C y))) +
      (∑ y ∈ Finset.univ.filter (Y5 C t),
          (weight n ε (dCode C y + 1) - weight n ε (dCode C y)))
  rw [hg, ← Finset.sum_sub_distrib]
  have hf : ∀ y : Word n,
      weight n ε (dCode C' (g1 C t y)) - weight n ε (dCode C y) =
        (if Y3 C t y then weight n ε (dCode C y - 1) - weight n ε (dCode C y) else 0) +
        (if Y5 C t y then weight n ε (dCode C y + 1) - weight n ε (dCode C y) else 0) := by
    intro y
    by_cases h3 : Y3 C t y
    · have h5 : ¬ Y5 C t y := fun hy => Y3_Y5_disjoint C t y ⟨h3, hy⟩
      have hd : dCode C' (g1 C t y) = dCode C y - 1 := by
        have h := (y_rel_3 C C' t hcol hcol' hsame h3).2
        simp [g1, h3]
        omega
      simp [h3, h5, hd]
    · by_cases h5 : Y5 C t y
      · have h1 : ¬ Y1 C t y := fun hy => Y1_Y5_disjoint C t y ⟨hy, h5⟩
        have hg1 : g1 C t y = flipBit t y := by
          simp [g1, h1, h3]
        have hd : dCode C' (g1 C t y) = dCode C y + 1 := by
          rw [hg1]
          exact (y_rel_5 C C' t hcol hcol' hsame h5).1.symm
        simp [h3, h5, hd]
      · have h0 : weight n ε (dCode C' (g1 C t y)) - weight n ε (dCode C y) = 0 := by
          have hy : Y1 C t y ∨ Y2 C t y ∨ Y4 C t y := by
            rcases y_mem C t y with hy | hy | hy | hy | hy
            · exact Or.inl hy
            · exact Or.inr (Or.inl hy)
            · exfalso; exact h3 hy
            · exact Or.inr (Or.inr hy)
            · exfalso; exact h5 hy
          rcases hy with hy | hy | hy
          · have h := y_rel_1 C C' t hcol hcol' hsame hy
            have hd : dCode C' (g1 C t y) = dCode C y := by
              simp [g1, hy, h.1]
            rw [hd]
            ring
          · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y2_disjoint C t y ⟨hy1, hy⟩
            have h3' : ¬ Y3 C t y := fun hy3 => Y2_Y3_disjoint C t y ⟨hy, hy3⟩
            have hg1 : g1 C t y = flipBit t y := by
              simp [g1, h1, h3']
            have hd : dCode C' (g1 C t y) = dCode C y := by
              rw [hg1]
              exact (y_rel_2 C C' t hcol hcol' hsame hy).1.symm
            rw [hd]
            ring
          · have h1 : ¬ Y1 C t y := fun hy1 => Y1_Y4_disjoint C t y ⟨hy1, hy⟩
            have h3' : ¬ Y3 C t y := fun hy3 => Y3_Y4_disjoint C t y ⟨hy3, hy⟩
            have hg1 : g1 C t y = flipBit t y := by
              simp [g1, h1, h3']
            have hd : dCode C' (g1 C t y) = dCode C y := by
              rw [hg1]
              exact (y_rel_4 C C' t hcol hcol' hsame hy).2.1.symm
            rw [hd]
            ring
        simp [h3, h5, h0]
  have hsum : (∑ y : Word n,
      (weight n ε (dCode C' (g1 C t y)) - weight n ε (dCode C y))) =
      ∑ y : Word n,
        ((if Y3 C t y then weight n ε (dCode C y - 1) - weight n ε (dCode C y) else 0) +
         (if Y5 C t y then weight n ε (dCode C y + 1) - weight n ε (dCode C y) else 0)) := by
    congr 1
    funext y
    exact hf y
  rw [hsum]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_filter]
  rw [Finset.sum_filter]
end N4Code
