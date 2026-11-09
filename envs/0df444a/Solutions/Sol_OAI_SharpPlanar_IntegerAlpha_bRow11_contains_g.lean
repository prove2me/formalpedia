-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow11_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:00:10.649575+00:00
-- url     : https://prove2.me/submissions/3604c171-d6dc-49b9-8d01-81713309dc5e

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b11_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow11_contains_g_oai (j : Fin 6) : (bRow11 j).Contains (basisBeta 11 j.val) := by
  fin_cases j
  · exact b11_0_contains_g
  · exact b11_1_contains_g
  · exact b11_2_contains_g
  · exact b11_3_contains_g
  · exact b11_4_contains_g
  · exact b11_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow11_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow11_contains_g_oai
