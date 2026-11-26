-- Prove2me | solution 1 for N4Code.linear_not_equiv_weight1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:34.150871+00:00
-- url     : https://prove2.me/submissions/98ccd49b-496e-4419-afab-8e6d61ea0732

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_allEvenWeights_equiv
import Theorems.Thm_N4Code_IsLinear_all_even
import Theorems.Thm_N4Code_exists_weight1_of_count1_pos
import Theorems.Thm_N4Code_not_all_even_of_weight1

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C C' : Code n) (hC : IsLinear C) (hpos : count C' 1 > 0) :
    ¬ Equivalent C C' := by
  intro heq
  exact (not_all_even_of_weight1 C' (exists_weight1_of_count1_pos C' hpos))
    ((allEvenWeights_equiv C C' heq).mp (IsLinear_all_even C hC))
end N4Code
