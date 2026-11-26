-- Prove2me | solution 1 for N4Code.no_cross_class_linear_class2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:16.489936+00:00
-- url     : https://prove2.me/submissions/a5b0c41f-4ffa-4c10-8855-3168b5ab23d7

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_linear_not_equiv_weight1
import Theorems.Thm_N4Code_classII_count1_pos

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hC' : ClassII C') :
    ¬ Equivalent C C' :=
  linear_not_equiv_weight1 C C' hC (classII_count1_pos C' hC')
end N4Code
