-- Prove2me | solution 1 for OAI.SharpPlanar.atomBase_pos_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:07:34.238209+00:00
-- url     : https://prove2.me/submissions/e4871415-5463-4bf4-be72-7d5a2956d606

import Mathlib
import Definitions.Def_OAIQ098G1643

section
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma atomBase_pos_g_oai (j : Fin 7) : 0<atomBase j := by fin_cases j <;> (first | (simp [atomBase]; all_goals first | (norm_num [atomBase]; done) | rfl | decide) | (norm_num [atomBase]; done) | norm_num [atomBase])
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.atomBase_pos_g_oai := @OAI.SharpPlanar.atomBase_pos_g_oai
