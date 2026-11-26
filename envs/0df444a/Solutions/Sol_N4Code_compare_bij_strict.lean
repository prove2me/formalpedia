-- Prove2me | solution 1 for N4Code.compare_bij_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:47.004129+00:00
-- url     : https://prove2.me/submissions/91a2fb58-7615-4eac-97f9-cd155f1aed9d

import Definitions.Def_N4Code_Performance
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Comparison
import Theorems.Thm_N4Code_lambda_diff_eq
import Theorems.Thm_N4Code_weight_strictAnti


set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y))
    (hne : ∃ y : Word n, y ∈ S) : UniversalStrictBetter C' C := by
  intro ε hε0 hε1
  apply sub_pos.mp
  rw [lambda_diff_eq C C' S g hgt heq ε]
  have hgt0 : (0 : ℝ) < ∑ y ∈ S,
      (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
    apply Finset.sum_pos'
    · intro y hy
      exact sub_nonneg.mpr (le_of_lt (weight_strictAnti hε0 hε1 (hgt y hy)))
    · rcases hne with ⟨y, hy⟩
      refine ⟨y, hy, ?_⟩
      exact sub_pos.mpr (weight_strictAnti hε0 hε1 (hgt y hy))
  exact mul_pos (by norm_num : (0 : ℝ) < 1 / 4) hgt0
end N4Code
