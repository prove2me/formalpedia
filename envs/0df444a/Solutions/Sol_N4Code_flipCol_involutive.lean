-- Prove2me | solution 1 for N4Code.flipCol_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:30.080657+00:00
-- url     : https://prove2.me/submissions/fab89c13-a28e-42c5-9bec-23d53ee9b954

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
theorem _root_.solution (c : Column) : flipCol (flipCol c) = c := by
  ext j
  simp [flipCol]
end N4Code
