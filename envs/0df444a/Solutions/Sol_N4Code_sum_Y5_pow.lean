-- Prove2me | solution 1 for N4Code.sum_Y5_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:53.302363+00:00
-- url     : https://prove2.me/submissions/8766398f-1fd8-4f4c-96de-994a7370eaa8

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_alpha5_n_zero
import Theorems.Thm_N4Code_sum_by_dist

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) (r : ℝ) :
    (∑ y ∈ Finset.univ.filter (Y5 C t), r ^ (dCode C y)) =
      ∑ d ∈ Finset.Icc 1 n, (alpha5 C t (d - 1) : ℝ) * r ^ (d - 1) := by
  have h0 : (alpha5 C t n : ℝ) = 0 := by simp [alpha5_n_zero C C' t hcol hcol' hsame]
  calc
    (∑ y ∈ Finset.univ.filter (Y5 C t), r ^ (dCode C y))
        = ∑ d ∈ Finset.Icc 0 n, (alpha5 C t d : ℝ) * r ^ d := by
          rw [sum_by_dist C (Y5 C t) (fun d => r ^ d)]
          simp [alpha5]
    _ = ∑ e ∈ Finset.Icc 1 (n + 1), (alpha5 C t (e - 1) : ℝ) * r ^ (e - 1) := by
          refine Finset.sum_bij (fun d _ => d + 1) ?_ ?_ ?_ ?_
          · intro d hd
            simp [Finset.mem_Icc] at hd ⊢
            omega
          · intro a _ b _ hab
            omega
          · intro e he
            refine ⟨e - 1, ?_, ?_⟩
            · simp [Finset.mem_Icc] at he ⊢
              omega
            · have he' : 1 ≤ e := (Finset.mem_Icc.mp he).1
              have hsub : e - 1 + 1 = e := by omega
              rw [hsub]
          · intro d hd
            simp
    _ = ∑ d ∈ Finset.Icc 1 n, (alpha5 C t (d - 1) : ℝ) * r ^ (d - 1) := by
          have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
            ext e
            constructor
            · intro he
              by_cases he' : e = n + 1
              · rw [Finset.mem_insert]
                exact Or.inl he'
              · rw [Finset.mem_insert]
                right
                simp [Finset.mem_Icc] at he ⊢
                omega
            · intro he
              rw [Finset.mem_insert] at he
              rcases he with he' | he1
              · simp [he']
              · simp [Finset.mem_Icc] at he1 ⊢
                omega
          rw [hsplit, Finset.sum_insert]
          · simp [h0]
          · simp
end N4Code
