-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.defectminus_lt_one_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:03:41.837143+00:00
-- url     : https://prove2.me/submissions/fce07e39-972b-4ad0-bd3e-a802f4e424eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E004
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_norm_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma defectminus_lt_one_e_oai : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < 1 :=
  defectminus_norm_e.trans (by norm_num)
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.defectminus_lt_one_e_oai := @OAI.SharpPlanar.Numerical.defectminus_lt_one_e_oai
