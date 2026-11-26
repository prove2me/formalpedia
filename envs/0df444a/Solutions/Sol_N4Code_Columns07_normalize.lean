-- Prove2me | solution 1 for N4Code.Columns07_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:59.618514+00:00
-- url     : https://prove2.me/submissions/e822668e-4bdb-4e94-835e-049e69cd50d6

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_row0_normalize

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    Columns07 (normalizeCode C i j) := by
  intro t
  have hrow := congrFun (row0_normalize C i j hij) t
  change colBit 0 (normalizeCode C i j t) = false
  simpa [row, colBit] using hrow
end N4Code
