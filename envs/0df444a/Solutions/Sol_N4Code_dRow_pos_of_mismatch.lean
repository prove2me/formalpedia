-- Prove2me | solution 1 for N4Code.dRow_pos_of_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:44.311204+00:00
-- url     : https://prove2.me/submissions/9916ce07-bf73-4ce9-b5c6-cdb0c9f6dfee

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow_eq_indicator_sum


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (t : Fin n) (y : Word n)
    (h : y t ≠ row C j t) : 1 ≤ dRow C j y := by
  rw [dRow_eq_indicator_sum]
  rw [sum_split_at (fun u : Fin n => if colBit j (C u) ≠ y u then 1 else 0) t]
  have hterm : (if colBit j (C t) ≠ y t then 1 else 0) = 1 := by
    have : colBit j (C t) ≠ y t := by
      simpa [row, colBit] using h.symm
    simp [this]
  rw [hterm]
  omega
end N4Code
