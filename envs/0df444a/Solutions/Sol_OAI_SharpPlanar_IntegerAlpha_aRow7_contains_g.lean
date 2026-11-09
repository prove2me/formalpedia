-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow7_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:52:12.832196+00:00
-- url     : https://prove2.me/submissions/a1ec9ba9-2dbe-4a02-b423-651b1da5873a

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a7_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow7_contains_g_oai (j : Fin 6) : (aRow7 j).Contains (basisAlpha 7 j.val) := by
  fin_cases j
  · exact a7_0_contains_g
  · exact a7_1_contains_g
  · exact a7_2_contains_g
  · exact a7_3_contains_g
  · exact a7_4_contains_g
  · exact a7_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow7_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow7_contains_g_oai
