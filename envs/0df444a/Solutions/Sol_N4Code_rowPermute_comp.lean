-- Prove2me | solution 1 for N4Code.rowPermute_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:25.44987+00:00
-- url     : https://prove2.me/submissions/3f7a3e5b-273c-458c-a83f-2d9ffefb4272

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
theorem _root_.solution (ρ₁ ρ₂ : Equiv (Fin 4) (Fin 4)) (c : Column) :
    rowPermute ρ₁ (rowPermute ρ₂ c) = rowPermute (ρ₁.trans ρ₂) c := by
  funext j
  rfl
end N4Code
