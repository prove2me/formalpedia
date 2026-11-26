-- Prove2me | solution 1 for N4Code.dRow_replace_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:08.415514+00:00
-- url     : https://prove2.me/submissions/75d9fbd3-2095-432a-83f6-e481425ac86c

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dRow_eq_indicator_sum


set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (j : Fin 4) (y : Word n)
    (hcol : C t = col1) (hj : j ≠ 2) :
    dRow (replaceColumn C t col3) j y = dRow C j y := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u = t <;> simp [replaceColumn, h]
  · have hb : colBit j col3 = colBit j col1 := by
      fin_cases j <;> simp [colBit, col1, col3] at hj ⊢
    rw [hcol, hb]
end N4Code
