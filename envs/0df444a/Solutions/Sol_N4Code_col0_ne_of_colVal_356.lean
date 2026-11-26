-- Prove2me | solution 1 for N4Code.col0_ne_of_colVal_356
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:51.322291+00:00
-- url     : https://prove2.me/submissions/40152065-398c-44b0-ac93-f96003b59921

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
theorem _root_.solution {s : Column} (h : colVal s = 3 ∨ colVal s = 5 ∨ colVal s = 6) :
    s ≠ col0 := by
  intro hs
  have : colVal s = 0 := by rw [hs]; decide
  rcases h with h3 | h5 | h6 <;> omega
end N4Code
