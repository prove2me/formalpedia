-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow4_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:51:43.443413+00:00
-- url     : https://prove2.me/submissions/c5c0cf60-1f69-4ec1-bf30-bd8afacd7601
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a4_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow4_contains_g_oai (j : Fin 6) : (aRow4 j).Contains (basisAlpha 4 j.val) := by
  fin_cases j
  · exact a4_0_contains_g
  · exact a4_1_contains_g
  · exact a4_2_contains_g
  · exact a4_3_contains_g
  · exact a4_4_contains_g
  · exact a4_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow4_contains_g_oai
