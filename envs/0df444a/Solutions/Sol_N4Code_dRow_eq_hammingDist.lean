-- Prove2me | solution 1 for N4Code.dRow_eq_hammingDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:14.190105+00:00
-- url     : https://prove2.me/submissions/3e9f8f77-6947-4dce-8c3b-b62f2b46aa84

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

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = hammingDist (row C j) y := rfl
end N4Code
