-- Prove2me | solution 1 for N4Code.rowPermute_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:13:00.537256+00:00
-- url     : https://prove2.me/submissions/f314a1a6-79db-497e-bd51-e3e709bb2d46

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
theorem _root_.solution (c : Column) : rowPermute (Equiv.refl (Fin 4)) c = c := by
  funext j
  rfl
end N4Code
