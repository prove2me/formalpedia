-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.phaseBase_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T02:47:20.838254+00:00
-- url     : https://prove2.me/submissions/1095d9dd-8c72-491e-8f12-09ad2a16a4c9

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_exp_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phaseBase_contains_e_oai : phaseBase.Contains (phase12 1) := by
  have hi := CBox.contains_scale_e piI_contains_e 1 6 (by norm_num)
  have he := CBox.contains_exp_e hi 1 (by decide +kernel)
  unfold phaseBase
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  unfold phase12
  congr 1
  norm_num
  ring

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.phaseBase_contains_e_oai := @OAI.SharpPlanar.IntegerBasis.phaseBase_contains_e_oai
