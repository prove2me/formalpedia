-- Prove2me | solution 1 for N4Code.y_rel_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:33.83219+00:00
-- url     : https://prove2.me/submissions/ca0e6c61-2efe-4367-b068-e7d5b031b596

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
    {y : Word n} (hy : Y4 C t y) :
    dCode C y = dO C y ∧ dCode C y = dCode C' (flipBit t y) ∧
      dCode C' (flipBit t y) = dP C y := by
  have hrep : C' = replaceColumn C t col3 := replace_1_3_eq C C' t hcol' hsame
  have hdC : dCode C y = min (dO C y) (dP C y) := dCode_eq_min_dO_dP C y
  have hdC'f : dCode C' (flipBit t y) = min (dOp C t y) (dP C y) := by
    rw [hrep, dCode_replace_flip C t y hcol]
  rcases hy with ⟨h1, h2, h3⟩
  have hdO : dCode C y = dO C y := by
    rw [hdC]
    rw [h1, h2]
    simp
  have hdP' : dCode C' (flipBit t y) = dP C y := by
    rw [hdC'f]
    have hle : dP C y ≤ dOp C t y := by
      have hd : dP C y = dO C y := h1.trans h2
      rw [hd]
      exact le_of_lt h3
    rw [min_eq_right hle]
  constructor
  · exact hdO
  · constructor
    · rw [hdO, hdP']
      exact (h1.trans h2).symm
    · exact hdP'
end N4Code
