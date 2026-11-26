-- Prove2me | solution 1 for N4Code.disjoint_056_12347
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:38.364808+00:00
-- url     : https://prove2.me/submissions/459b0976-64e8-444a-89a9-50cbf4c0b807

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
theorem _root_.solution : Disjoint ({0, 5, 6} : Finset ℕ) ({1, 2, 3, 4, 7} : Finset ℕ) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp at hx hx'
  omega
end N4Code
