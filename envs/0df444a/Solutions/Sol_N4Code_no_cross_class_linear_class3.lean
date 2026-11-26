-- Prove2me | solution 1 for N4Code.no_cross_class_linear_class3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:09:22.893695+00:00
-- url     : https://prove2.me/submissions/e48f202c-da86-4b35-aba6-505b4c417e31

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_linear_not_equiv_weight1
import Theorems.Thm_N4Code_classIII_count1_pos

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hC' : ClassIII C') :
    ¬ Equivalent C C' :=
  linear_not_equiv_weight1 C C' hC (classIII_count1_pos C' hC')
end N4Code
