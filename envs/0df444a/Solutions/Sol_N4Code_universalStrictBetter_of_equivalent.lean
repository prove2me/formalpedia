-- Prove2me | solution 1 for N4Code.universalStrictBetter_of_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:48.582251+00:00
-- url     : https://prove2.me/submissions/50e9b1c9-f6c5-45f1-b154-e6bf45215ee4

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
theorem _root_.solution {n : ℕ} (C₁ C₁' C₂ C₂' : Code n)
    (h1 : Equivalent C₁ C₁') (h2 : Equivalent C₂ C₂') (h : UniversalStrictBetter C₁' C₂') :
    UniversalStrictBetter C₁ C₂ := by
  intro ε hε0 hε1
  have hlt := h ε hε0 hε1
  have heq1 := lambda_equiv C₁ C₁' h1 ε
  have heq2 := lambda_equiv C₂ C₂' h2 ε
  linarith
end N4Code
