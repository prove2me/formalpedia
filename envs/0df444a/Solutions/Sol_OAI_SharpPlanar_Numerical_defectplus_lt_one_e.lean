-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.defectplus_lt_one_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:32:47.824003+00:00
-- url     : https://prove2.me/submissions/0f76e84d-c731-4dac-ab13-1429d6e738fd

import Mathlib
import Definitions.Def_OAIQ098E005
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectplus_norm_e

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
lemma defectplus_lt_one_e_oai : ‖1-(matrixL1 Wplus)*(matrixL1 Aplus)‖ < 1 :=
  defectplus_norm_e.trans (by norm_num)
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.defectplus_lt_one_e_oai := @OAI.SharpPlanar.Numerical.defectplus_lt_one_e_oai
