-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:53:16.453134+00:00
-- url     : https://prove2.me/submissions/b4b5406e-f0be-446c-b5c6-10fa1f9491c7

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a9_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow9_contains_g_oai (j : Fin 6) : (aRow9 j).Contains (basisAlpha 9 j.val) := by
  fin_cases j
  · exact a9_0_contains_g
  · exact a9_1_contains_g
  · exact a9_2_contains_g
  · exact a9_3_contains_g
  · exact a9_4_contains_g
  · exact a9_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow9_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow9_contains_g_oai
