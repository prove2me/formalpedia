-- Prove2me | solution 1 for N4Code.flipCol_col5_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:22.318167+00:00
-- url     : https://prove2.me/submissions/d3b3b49c-12a2-4991-97c4-a07269e4c0eb

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
theorem _root_.solution (k : Fin 4) :
    (!(col5 k)) = decide (k = (0 : Fin 4) ∨ k = (2 : Fin 4)) := by
  fin_cases k <;> simp [col5]
end N4Code
