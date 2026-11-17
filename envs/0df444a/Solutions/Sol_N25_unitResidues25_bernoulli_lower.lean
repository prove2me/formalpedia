-- Prove2me | solution 1 for N25.unitResidues25_bernoulli_lower
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:11.35054+00:00
-- url     : https://prove2.me/submissions/5c8b2998-816b-4a11-819c-b56608b2c90e

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

namespace N25

theorem _root_.solution (a : Fin 25) (i : Fin 5) :
    let B : ℕ → ℚ := fun g =>
      (((a.val * g) % 25 : ℕ) : ℚ) ^ 2 / 625 -
        (((a.val * g) % 25 : ℕ) : ℚ) / 25 + 1 / 6
    (-6 / 25 : ℚ) ≤ B (unitResidues25 i).1 + B (unitResidues25 i).2 -
      (B (unitResidues25 (i + 1)).1 + B (unitResidues25 (i + 1)).2) := by
  fin_cases a <;> fin_cases i <;> decide +kernel

end N25
