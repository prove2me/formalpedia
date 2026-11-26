-- Prove2me | solution 1 for N4Code.compare_bij
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:46.478848+00:00
-- url     : https://prove2.me/submissions/28185f74-4111-4189-a299-cebe4d73a68a

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
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y)) :
    UniversalBetter C' C := by
  intro ε hε0 hε1
  apply sub_nonneg.mp
  rw [lambda_diff_eq C C' S g hgt heq ε]
  have hge : (0 : ℝ) ≤ ∑ y ∈ S,
      (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by
    apply Finset.sum_nonneg
    intro y hy
    exact sub_nonneg.mpr (le_of_lt (weight_strictAnti hε0 hε1 (hgt y hy)))
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hge
end N4Code
