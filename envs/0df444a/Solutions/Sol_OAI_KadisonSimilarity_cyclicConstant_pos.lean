-- Prove2me | solution 1 for OAI.KadisonSimilarity.cyclicConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:19:45.320328+00:00
-- url     : https://prove2.me/submissions/043f91f2-9049-4f63-986f-27d8f64bc043

import Mathlib
import Definitions.Def_KadisonSimilarity

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Constants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical constants fixed by the manuscript. -/

noncomputable section

namespace KadisonSimilarity

theorem rowConstant_pos : 0 < rowConstant := by unfold rowConstant; positivity

theorem cyclicConstant_pos_oai : 0 < cyclicConstant := by
  unfold cyclicConstant
  have := rowConstant_pos
  positivity

end KadisonSimilarity

end

end OAI
end

theorem solution : type_of% @OAI.KadisonSimilarity.cyclicConstant_pos_oai := @OAI.KadisonSimilarity.cyclicConstant_pos_oai
