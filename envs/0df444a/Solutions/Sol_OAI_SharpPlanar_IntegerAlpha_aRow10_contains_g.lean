-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow10_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:51:38.719331+00:00
-- url     : https://prove2.me/submissions/65692808-abac-4709-a863-a21b5117967b

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a10_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow10_contains_g_oai (j : Fin 6) : (aRow10 j).Contains (basisAlpha 10 j.val) := by
  fin_cases j
  · exact a10_0_contains_g
  · exact a10_1_contains_g
  · exact a10_2_contains_g
  · exact a10_3_contains_g
  · exact a10_4_contains_g
  · exact a10_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow10_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow10_contains_g_oai
