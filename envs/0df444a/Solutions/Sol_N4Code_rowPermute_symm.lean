-- Prove2me | solution 1 for N4Code.rowPermute_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:29.58422+00:00
-- url     : https://prove2.me/submissions/7413531b-75e4-48c4-9dab-6c4bfc35cf1e

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
    rowPermute ρ (rowPermute ρ.symm c) = c := by
  funext j
  simp [rowPermute, Equiv.symm_apply_apply]
end N4Code
