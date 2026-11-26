-- Prove2me | solution 1 for N4Code.dRow12_sum_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:40.218662+00:00
-- url     : https://prove2.me/submissions/27079a44-cc76-4dbb-bbd3-24882216bc20

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow12_columns07
import Theorems.Thm_N4Code_w_i_le_count


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (y : Word n) (h07 : Columns07 C) :
    dRow C 1 y + dRow C 2 y =
      count C 2 + count C 3 + count C 4 + count C 5 +
        2 * (w_i C 0 y + w_i C 1 y + (count C 6 - w_i C 6 y) + (count C 7 - w_i C 7 y)) := by
  rcases dRow12_columns07 C y h07 with ⟨hd1, hd2⟩
  rw [hd1, hd2]
  have hw2 : w_i C 2 y ≤ count C 2 := w_i_le_count C 2 y
  have hw3 : w_i C 3 y ≤ count C 3 := w_i_le_count C 3 y
  have hw4 : w_i C 4 y ≤ count C 4 := w_i_le_count C 4 y
  have hw5 : w_i C 5 y ≤ count C 5 := w_i_le_count C 5 y
  have hw6 : w_i C 6 y ≤ count C 6 := w_i_le_count C 6 y
  have hw7 : w_i C 7 y ≤ count C 7 := w_i_le_count C 7 y
  omega
end N4Code
