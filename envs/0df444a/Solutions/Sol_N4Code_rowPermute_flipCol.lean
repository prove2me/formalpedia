-- Prove2me | solution 1 for N4Code.rowPermute_flipCol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:33.339432+00:00
-- url     : https://prove2.me/submissions/4eaf4ef8-9d63-407c-bcf8-1b301e7b3319

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
    rowPermute ρ (flipCol c) = flipCol (rowPermute ρ c) := by
  ext j
  simp [rowPermute, flipCol]
end N4Code
