-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:22:03.339804+00:00
-- url     : https://prove2.me/submissions/06bbea4d-2175-4973-8be5-51f4e3842dd4

import Mathlib
import Definitions.Def_OAIQ098G075
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_exp_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phaseBase_contains_g_oai : phaseBase.Contains (phase12 1) := by
  have hi := CBox.contains_scale_g piI_contains_g 1 6 (by norm_num)
  have he := CBox.contains_exp_g hi 1 (by decide +kernel)
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

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g_oai := @OAI.SharpPlanar.IntegerBasis.phaseBase_contains_g_oai
