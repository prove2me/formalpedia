-- Prove2me | solution 1 for N4Code.compare_bij_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:47.593643+00:00
-- url     : https://prove2.me/submissions/4f116477-d4d9-4c59-ac08-986710ea4814

import Definitions.Def_N4Code_Performance
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Comparison
import Theorems.Thm_N4Code_lambda_diff_eq

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (g : Word n ≃ Word n)
    (heq : ∀ y : Word n, dCode C y = dCode C' (g y)) :
    UniversalEqual C' C := by
  intro ε hε0 hε1
  apply sub_eq_zero.mp
  have hdiff := lambda_diff_eq C C' ∅ g (by intro y hy; simp at hy) (by intro y _; exact heq y) ε
  rw [hdiff]
  simp
end N4Code
