-- Prove2me | solution 1 for N4Code.y_rel_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:40.016655+00:00
-- url     : https://prove2.me/submissions/3ad17e2c-7e98-46bd-9762-57825cd6b8f0

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dCode_eq_min_dO_dP
import Theorems.Thm_N4Code_dCode_replace_1_3
import Theorems.Thm_N4Code_replace_1_3_eq

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y1 C t y) :
    dCode C y = dCode C' y ∧ dCode C y = dO C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp C t y) := by
    rw [hrep, dCode_replace_1_3 C t y hcol]
  rcases hy with hy | hy
  · rcases hy with ⟨h1, h2⟩
    have hdOp : dO C y ≤ dPp C t y := le_trans h1 (le_of_lt h2)
    constructor
    · rw [hdC, hdC', min_eq_left h1, min_eq_left hdOp]
    · rw [hdC, min_eq_left h1]
  · rcases hy with ⟨h1, h2, h3⟩
    have hdP : dO C y ≤ dP C y := le_trans h1 h2
    constructor
    · rw [hdC, hdC', min_eq_left hdP, min_eq_left h1]
    · rw [hdC, min_eq_left hdP]
end N4Code
