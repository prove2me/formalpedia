-- Prove2me | solution 1 for OAI.SharpPlanar.lambda_sq_antitone_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:32:02.244918+00:00
-- url     : https://prove2.me/submissions/203b9fbe-d485-442b-ad80-4e233da39c55

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_lambda_sq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma lambda_sq_antitone_g_oai {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖lambda t‖^2 ≤ ‖lambda s‖^2 := by
  rw [lambda_sq_g,lambda_sq_g]
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.lambda_sq_antitone_g_oai := @OAI.SharpPlanar.lambda_sq_antitone_g_oai
