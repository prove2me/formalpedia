-- Prove2me | solution 1 for N4Code.even_W_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:39.59403+00:00
-- url     : https://prove2.me/submissions/3c4cd1a0-a122-4408-b8e4-6567f3b48a2a

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_row1_normalize
import Theorems.Thm_N4Code_Columns07_normalize
import Theorems.Thm_N4Code_sum_counts_4_7

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j)
    (hEven : Even (hammingDist (row C i) (row C j))) :
    Even (count (normalizeCode C i j) 4 + count (normalizeCode C i j) 5 +
      count (normalizeCode C i j) 6 + count (normalizeCode C i j) 7) := by
  have h07 := Columns07_normalize C i j hij
  have hsum := sum_counts_4_7 (normalizeCode C i j) h07
  have hrow := row1_normalize C i j hij
  have hw : hammingWeight (bitXor (row C i) (row C j)) = hammingDist (row C i) (row C j) := rfl
  rw [hsum, hrow, hw]
  exact hEven
end N4Code
