-- Prove2me | solution 1 for N4Code.y_rel_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:33.186902+00:00
-- url     : https://prove2.me/submissions/df671fe0-e0d8-4d0c-9fbd-deae899ec329

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dCode_eq_min_dO_dP
import Theorems.Thm_N4Code_dCode_replace_flip
import Theorems.Thm_N4Code_replace_1_3_eq

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y2 C t y) :
    dCode C y = dCode C' (flipBit t y) ∧ dCode C y = dP C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipBit t y) = min (dOp C t y) (dP C y) := by
    rw [hrep, dCode_replace_flip C t y hcol]
  rcases hy with hy | hy
  · rcases hy with ⟨h1, h2⟩
    have hdP : dP C y ≤ dO C y := le_of_lt h2
    have hdPo : dP C y ≤ dOp C t y := by
      have h := dO_le_dOp_add_one C t y
      omega
    constructor
    · rw [hdC, hdC'f, min_eq_right hdP, min_eq_right hdPo]
    · rw [hdC, min_eq_right hdP]
  · rcases hy with ⟨h1, h2, h3⟩
    constructor
    · rw [hdC, hdC'f, min_eq_right h2, min_eq_right h3]
    · rw [hdC, min_eq_right h2]
end N4Code
