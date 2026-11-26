-- Prove2me | solution 1 for N4Code.dRow_replace_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:00.999367+00:00
-- url     : https://prove2.me/submissions/7d996a8b-9420-4a09-a8e9-6127c5101de1

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dRow_eq_indicator_sum


set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dRow (replaceColumn C t col3) ⟨2, by decide⟩ y = dRow C ⟨2, by decide⟩ (flipBit t y) := by
  rw [dRow_eq_indicator_sum, dRow_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : u = t <;> by_cases hy : y t = true <;>
    simp [replaceColumn, flipBit, colBit, col1, col3, h, hcol, hy]
end N4Code
