-- Prove2me | solution 1 for N4Code.dCode_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:49.578631+00:00
-- url     : https://prove2.me/submissions/fb6b981a-2764-4622-adb2-add1b1f7400a

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
import Theorems.Thm_N4Code_hammingDist_le
import Theorems.Thm_N4Code_dCode_le_dRow

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (y : Word n) : dCode C y ≤ n := by
  exact (dCode_le_dRow C ⟨0, by decide⟩ y).trans (hammingDist_le _ _)
end N4Code
