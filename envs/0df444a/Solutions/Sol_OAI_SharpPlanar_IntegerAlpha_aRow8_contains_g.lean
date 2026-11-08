-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow8_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:52:45.733135+00:00
-- url     : https://prove2.me/submissions/35cf7b1d-b895-46e1-bc3e-76f5da654050
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a8_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow8_contains_g_oai (j : Fin 6) : (aRow8 j).Contains (basisAlpha 8 j.val) := by
  fin_cases j
  · exact a8_0_contains_g
  · exact a8_1_contains_g
  · exact a8_2_contains_g
  · exact a8_3_contains_g
  · exact a8_4_contains_g
  · exact a8_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow8_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow8_contains_g_oai
