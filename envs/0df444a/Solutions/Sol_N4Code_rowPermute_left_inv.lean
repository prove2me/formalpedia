-- Prove2me | solution 1 for N4Code.rowPermute_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:49.434044+00:00
-- url     : https://prove2.me/submissions/6d753185-366c-4eca-b4e9-f992766d6a84

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
    rowPermute ρ.symm (rowPermute ρ c) = c := by
  funext j
  simp [rowPermute, Equiv.apply_symm_apply]
end N4Code
