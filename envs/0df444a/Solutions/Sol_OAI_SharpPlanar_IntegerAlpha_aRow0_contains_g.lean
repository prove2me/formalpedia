-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.aRow0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:51:37.668168+00:00
-- url     : https://prove2.me/submissions/0addc557-46f7-4430-8035-174b7f65aed8

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_a0_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aRow0_contains_g_oai (j : Fin 6) : (aRow0 j).Contains (basisAlpha 0 j.val) := by
  fin_cases j
  · exact a0_0_contains_g
  · exact a0_1_contains_g
  · exact a0_2_contains_g
  · exact a0_3_contains_g
  · exact a0_4_contains_g
  · exact a0_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.aRow0_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.aRow0_contains_g_oai
