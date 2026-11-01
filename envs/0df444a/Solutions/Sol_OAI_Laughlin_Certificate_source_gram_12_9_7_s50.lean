-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_12_9_7_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:18:55.213119+00:00
-- url     : https://prove2.me/submissions/64bc514d-a4fc-47f4-b985-e13bc910d264

import Mathlib
import Definitions.Def_OAIQ050L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_12_7_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_12_9_7_s50_oai : Z 12 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_7_9_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_12_9_7_s50_oai := @OAI.Laughlin.Certificate.source_gram_12_9_7_s50_oai
