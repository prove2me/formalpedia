-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:51:40.460705+00:00
-- url     : https://prove2.me/submissions/abb6ccdd-8819-4cf6-a317-633343d3a75e

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a1_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow1_contains_g_oai (j : Fin 6) : (aRow1 j).Contains (basisAlpha 1 j.val) := by
  fin_cases j
  · exact a1_0_contains_g
  · exact a1_1_contains_g
  · exact a1_2_contains_g
  · exact a1_3_contains_g
  · exact a1_4_contains_g
  · exact a1_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow1_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow1_contains_g_oai
