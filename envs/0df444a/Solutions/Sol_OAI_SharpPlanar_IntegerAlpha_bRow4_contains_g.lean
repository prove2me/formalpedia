-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow4_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:01:32.79257+00:00
-- url     : https://prove2.me/submissions/8045c74d-6a3c-495b-af2e-951fb92e7be9

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b4_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow4_contains_g_oai (j : Fin 6) : (bRow4 j).Contains (basisBeta 4 j.val) := by
  fin_cases j
  · exact b4_0_contains_g
  · exact b4_1_contains_g
  · exact b4_2_contains_g
  · exact b4_3_contains_g
  · exact b4_4_contains_g
  · exact b4_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow4_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow4_contains_g_oai
