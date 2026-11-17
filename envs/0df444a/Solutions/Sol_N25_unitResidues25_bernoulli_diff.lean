-- Prove2me | solution 1 for N25.unitResidues25_bernoulli_diff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:09.39021+00:00
-- url     : https://prove2.me/submissions/1327fe66-7366-4b47-8155-15bc9acdeb98

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

namespace N25

theorem _root_.solution (i : Fin 5) :
    (25 / 2 : ℚ) *
      ((((unitResidues25 i).1 : ℚ) / 25) ^ 2 - ((unitResidues25 i).1 : ℚ) / 25 + 1 / 6 +
       (((unitResidues25 i).2 : ℚ) / 25) ^ 2 - ((unitResidues25 i).2 : ℚ) / 25 + 1 / 6 -
       ((((unitResidues25 (i + 1)).1 : ℚ) / 25) ^ 2 - ((unitResidues25 (i + 1)).1 : ℚ) / 25 + 1 / 6 +
        (((unitResidues25 (i + 1)).2 : ℚ) / 25) ^ 2 - ((unitResidues25 (i + 1)).2 : ℚ) / 25 + 1 / 6)) =
      (unitQOrder25 i : ℚ) := by
  fin_cases i <;> decide +kernel

end N25
