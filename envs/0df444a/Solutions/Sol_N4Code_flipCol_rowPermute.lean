-- Prove2me | solution 1 for N4Code.flipCol_rowPermute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:52.448172+00:00
-- url     : https://prove2.me/submissions/745fcd0a-0ffd-4fe6-9281-905df6ffb0e1

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
theorem _root_.solution (ρ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    flipCol (rowPermute ρ c) = rowPermute ρ (flipCol c) := by
  funext j
  rfl
end N4Code
