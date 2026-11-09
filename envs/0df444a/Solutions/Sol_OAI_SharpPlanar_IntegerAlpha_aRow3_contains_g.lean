-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:51:42.437244+00:00
-- url     : https://prove2.me/submissions/9d65e633-c4dc-4a78-8c0e-0012b68f8267

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a3_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow3_contains_g_oai (j : Fin 6) : (aRow3 j).Contains (basisAlpha 3 j.val) := by
  fin_cases j
  · exact a3_0_contains_g
  · exact a3_1_contains_g
  · exact a3_2_contains_g
  · exact a3_3_contains_g
  · exact a3_4_contains_g
  · exact a3_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow3_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow3_contains_g_oai
