-- Prove2me | solution 1 for OAI.SharpPlanar.table_range_mass_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:21:43.119701+00:00
-- url     : https://prove2.me/submissions/1752bd08-f8b0-427d-90ac-191bd777272f

import Mathlib
import Definitions.Def_OAIQ098E015

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
lemma table_range_mass_e_oai (a : Bool) :
    ∑ n ∈ Finset.range 101, (|(tableC a n:ℝ)|+|(tableD a n:ℝ)|) ≤ 3 := by
  have hq : ∑ n ∈ Finset.range 101, (|tableC a n|+|tableD a n|) ≤ 3 := by
    cases a <;> decide +kernel
  exact_mod_cast hq
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.table_range_mass_e_oai := @OAI.SharpPlanar.table_range_mass_e_oai
