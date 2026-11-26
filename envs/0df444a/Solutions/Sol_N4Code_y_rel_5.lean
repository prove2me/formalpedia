-- Prove2me | solution 1 for N4Code.y_rel_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:37.451478+00:00
-- url     : https://prove2.me/submissions/c6cef5e3-4eb7-4d01-bfb3-cd3f6bbf48c1

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dOp_le_dO_add_one
import Theorems.Thm_N4Code_dCode_eq_min_dO_dP
import Theorems.Thm_N4Code_dCode_replace_flip
import Theorems.Thm_N4Code_replace_1_3_eq

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    {y : Word n} (hy : Y5 C t y) :
    dCode C y + 1 = dCode C' (flipBit t y) ∧ dCode C' (flipBit t y) = dP C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipBit t y) = min (dOp C t y) (dP C y) := by
    rw [hrep, dCode_replace_flip C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdO : dCode C y = dO C y := by
    rw [hdC]
    have hle : dO C y ≤ dP C y := le_of_lt (lt_of_lt_of_eq h3 h2)
    rw [min_eq_left hle]
  have hdP' : dCode C' (flipBit t y) = dP C y := by
    rw [hdC'f, h2]
    simp
  constructor
  · rw [hdO, hdP']
    have h := dOp_le_dO_add_one C t y
    omega
  · exact hdP'
end N4Code
