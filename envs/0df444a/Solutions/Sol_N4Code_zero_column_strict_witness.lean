-- Prove2me | solution 1 for N4Code.zero_column_strict_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:55.636815+00:00
-- url     : https://prove2.me/submissions/7f10d693-84f5-4f3c-ab87-8d28ef72f5f6

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_zero_column_strict_better

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (hcol : C t = col0) :
    (∃ y : Word n, Y3c C col5 colZeros_col5_nonempty colOnes_col5_nonempty t y) →
      UniversalStrictBetter (replaceColumn C t col5) C := by
  rintro hy
  exact zero_column_strict_better C t col5 hcol colZeros_col5_nonempty colOnes_col5_nonempty hy
end N4Code
