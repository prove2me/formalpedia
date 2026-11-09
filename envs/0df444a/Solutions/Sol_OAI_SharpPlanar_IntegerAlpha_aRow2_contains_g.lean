-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow2_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:51:41.410852+00:00
-- url     : https://prove2.me/submissions/4a3b9a86-7a52-41a2-ab34-53781c26717b

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a2_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow2_contains_g_oai (j : Fin 6) : (aRow2 j).Contains (basisAlpha 2 j.val) := by
  fin_cases j
  · exact a2_0_contains_g
  · exact a2_1_contains_g
  · exact a2_2_contains_g
  · exact a2_3_contains_g
  · exact a2_4_contains_g
  · exact a2_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow2_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow2_contains_g_oai
