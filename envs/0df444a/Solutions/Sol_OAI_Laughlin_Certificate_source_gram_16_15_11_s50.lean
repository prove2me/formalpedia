-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_gram_16_15_11_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:32:38.800357+00:00
-- url     : https://prove2.me/submissions/a2e82082-3d92-4e5a-bdfd-cbeecb0569a0

import Mathlib
import Definitions.Def_OAIQ050L000
import Theorems.Thm_OAI_Laughlin_Certificate_source_gram_16_11_15_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_GramData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_16_15_11_s50_oai : Z 16 15 11 = (-19155386250 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_11_15_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.source_gram_16_15_11_s50_oai := @OAI.Laughlin.Certificate.source_gram_16_15_11_s50_oai
