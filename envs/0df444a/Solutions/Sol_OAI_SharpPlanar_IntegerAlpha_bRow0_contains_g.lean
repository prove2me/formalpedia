-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerAlpha.bRow0_contains_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:01:17.209696+00:00
-- url     : https://prove2.me/submissions/15d50cd8-9a13-44b4-acc2-65376f9b6cb4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_2_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_4_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_b0_5_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma bRow0_contains_g_oai (j : Fin 6) : (bRow0 j).Contains (basisBeta 0 j.val) := by
  fin_cases j
  · exact b0_0_contains_g
  · exact b0_1_contains_g
  · exact b0_2_contains_g
  · exact b0_3_contains_g
  · exact b0_4_contains_g
  · exact b0_5_contains_g
end SharpPlanar.IntegerAlpha

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerAlpha.bRow0_contains_g_oai := @OAI.SharpPlanar.IntegerAlpha.bRow0_contains_g_oai
