-- Prove2me | solution 1 for OAI.SharpPlanar.table_range_mass_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:46:37.025912+00:00
-- url     : https://prove2.me/submissions/fdb44190-fdc7-491b-8072-4a964c6fe671

import Mathlib
import Definitions.Def_OAIQ098G015

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
lemma table_range_mass_g_oai (a : Bool) :
    ∑ n ∈ Finset.range 101, (|(tableC a n:ℝ)|+|(tableD a n:ℝ)|) ≤ 3 := by
  have hq : ∑ n ∈ Finset.range 101, (|tableC a n|+|tableD a n|) ≤ 3 := by
    cases a <;> decide +kernel
  exact_mod_cast hq
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.table_range_mass_g_oai := @OAI.SharpPlanar.table_range_mass_g_oai
