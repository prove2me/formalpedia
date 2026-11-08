-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow6_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:52:11.731197+00:00
-- url     : https://prove2.me/submissions/5406e8c3-270e-421e-9dcc-9ec2f3652928
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a6_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow6_contains_g_oai (j : Fin 6) : (aRow6 j).Contains (basisAlpha 6 j.val) := by
  fin_cases j
  · exact a6_0_contains_g
  · exact a6_1_contains_g
  · exact a6_2_contains_g
  · exact a6_3_contains_g
  · exact a6_4_contains_g
  · exact a6_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow6_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow6_contains_g_oai
