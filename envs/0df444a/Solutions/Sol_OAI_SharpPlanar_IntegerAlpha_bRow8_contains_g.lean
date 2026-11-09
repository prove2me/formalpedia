-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow8_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:01:38.869132+00:00
-- url     : https://prove2.me/submissions/52b1984c-60b1-4a91-82a5-3a8a70a1ec4e

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b8_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow8_contains_g_oai (j : Fin 6) : (bRow8 j).Contains (basisBeta 8 j.val) := by
  fin_cases j
  · exact b8_0_contains_g
  · exact b8_1_contains_g
  · exact b8_2_contains_g
  · exact b8_3_contains_g
  · exact b8_4_contains_g
  · exact b8_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow8_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow8_contains_g_oai
