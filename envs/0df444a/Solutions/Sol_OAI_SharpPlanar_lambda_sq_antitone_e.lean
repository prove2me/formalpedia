-- Prove2me | solution 1 for OAI.SharpPlanar.lambda_sq_antitone_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:18:45.95648+00:00
-- url     : https://prove2.me/submissions/74260b8e-3e7e-440f-a3a8-97b91f8c9ade

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_lambda_sq_e

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


lemma lambda_sq_antitone_e_oai {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖lambda t‖^2 ≤ ‖lambda s‖^2 := by
  rw [lambda_sq_e,lambda_sq_e]
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.lambda_sq_antitone_e_oai := @OAI.SharpPlanar.lambda_sq_antitone_e_oai
