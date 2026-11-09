-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow7_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:03:45.637166+00:00
-- url     : https://prove2.me/submissions/19795134-2090-4e12-8693-1e19f88198df

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b7_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow7_contains_g_oai (j : Fin 6) : (bRow7 j).Contains (basisBeta 7 j.val) := by
  fin_cases j
  · exact b7_0_contains_g
  · exact b7_1_contains_g
  · exact b7_2_contains_g
  · exact b7_3_contains_g
  · exact b7_4_contains_g
  · exact b7_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow7_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow7_contains_g_oai
