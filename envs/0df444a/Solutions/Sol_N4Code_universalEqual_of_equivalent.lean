-- Prove2me | solution 1 for N4Code.universalEqual_of_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:47.9573+00:00
-- url     : https://prove2.me/submissions/072ee7b9-3290-4d42-bdc8-5004b40fdc43

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_lambda_equiv

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (h : Equivalent C C') :
    UniversalEqual C' C := by
  intro ε h0 h1
  exact lambda_equiv C C' h ε
end N4Code
