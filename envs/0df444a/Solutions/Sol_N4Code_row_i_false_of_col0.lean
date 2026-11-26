-- Prove2me | solution 1 for N4Code.row_i_false_of_col0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:19.180843+00:00
-- url     : https://prove2.me/submissions/7d296500-4ad7-4af5-92f1-c43bc1dc805c

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i : Fin 4) (t : Fin n) (h0 : C t = col0) :
    (row C i) t = false := by
  simp [row, colBit, h0, col0]
end N4Code
