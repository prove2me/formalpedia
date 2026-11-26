-- Prove2me | solution 1 for N4Code.y_rel_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:33.484747+00:00
-- url     : https://prove2.me/submissions/8a79909a-3aa6-49fb-a0f0-7da54b93ae7c

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
    {y : Word n} (hy : Y3 C t y) :
    dCode C y = dP C y ∧ dCode C y = dCode C' y + 1 := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC' : dCode C' y = min (dO C y) (dPp C t y) := by
    rw [hrep, dCode_replace_1_3 C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdP : dCode C y = dP C y := by
    rw [hdC]
    rw [← h3]
    simp
  have hdC'p : dCode C' y = dPp C t y := by
    rw [hdC', min_eq_right (le_of_lt (lt_of_lt_of_eq h2 h3))]
  constructor
  · exact hdP
  · rw [hdP, hdC'p]
    have h := dP_le_dPp_add_one C t y
    omega
end N4Code
