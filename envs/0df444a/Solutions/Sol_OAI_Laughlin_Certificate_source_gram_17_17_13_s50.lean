-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_17_17_13_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T07:05:05.05775+00:00
-- url     : https://prove2.me/submissions/568ffd81-4f5b-4e0b-96a0-d3ea76718f5f

import Mathlib
import Definitions.Def_OAIQ050L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_17_13_17_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem Z_symm (D r s : ℕ) : Z D r s = Z D s r := by
  unfold Z
  congr 1
  apply List.map_congr_left
  intro A hA
  dsimp
  ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_17_17_13_s50_oai : Z 17 17 13 = (-217094377500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_13_17_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_17_17_13_s50_oai := @OAI.Laughlin.Certificate.source_gram_17_17_13_s50_oai
