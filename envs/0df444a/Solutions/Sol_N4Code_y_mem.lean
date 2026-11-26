-- Prove2me | solution 1 for N4Code.y_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:35.964829+00:00
-- url     : https://prove2.me/submissions/a2446167-ca78-44a5-ad57-d266890e305c

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_Y1_or_Y4_or_Y5_iff
import Theorems.Thm_N4Code_Y2_or_Y3_iff

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    Y1 C t y ∨ Y2 C t y ∨ Y3 C t y ∨ Y4 C t y ∨ Y5 C t y := by
  by_cases h : dO C y ≤ min (dP C y) (dPp C t y)
  · have hA := (Y1_or_Y4_or_Y5_iff C t y).mpr h
    rcases hA with hy | hy | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hy)))
  · have hB := (Y2_or_Y3_iff C t y).mpr (lt_of_not_ge h)
    rcases hB with hy | hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (Or.inl hy))
end N4Code
