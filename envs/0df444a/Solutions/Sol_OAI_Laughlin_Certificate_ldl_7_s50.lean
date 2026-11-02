-- Prove2me | solution 1 for OAI.Laughlin.Certificate.ldl_7_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:34:58.383144+00:00
-- url     : https://prove2.me/submissions/ad6e74bf-7825-44b0-83e4-20058ab772ba

import Mathlib
import Definitions.Def_OAIQ050L010
import Theorems.Thm_OAI_Laughlin_Certificate_error_7_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Gram072
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem gram_7_1_1 : Z 7 1 1 = (1440 : ℚ) := by
  decide +kernel

theorem gram_7_1_3 : Z 7 1 3 = (0 : ℚ) := by
  decide +kernel

theorem gram_7_1_5 : Z 7 1 5 = (-360 : ℚ) := by
  decide +kernel

theorem gram_7_1_7 : Z 7 1 7 = (2520 : ℚ) := by
  decide +kernel

theorem gram_7_3_1 : Z 7 3 1 = (0 : ℚ) := by
  decide +kernel

theorem gram_7_3_3 : Z 7 3 3 = (0 : ℚ) := by
  decide +kernel

theorem gram_7_3_5 : Z 7 3 5 = (0 : ℚ) := by
  decide +kernel

theorem gram_7_3_7 : Z 7 3 7 = (0 : ℚ) := by
  decide +kernel

theorem gram_7_5_1 : Z 7 5 1 = (-360 : ℚ) := by
  decide +kernel

theorem gram_7_5_3 : Z 7 5 3 = (0 : ℚ) := by
  decide +kernel

theorem gram_7_5_5 : Z 7 5 5 = (90 : ℚ) := by
  decide +kernel

theorem gram_7_5_7 : Z 7 5 7 = (-630 : ℚ) := by
  decide +kernel

theorem gram_7_7_1 : Z 7 7 1 = (2520 : ℚ) := by
  decide +kernel

theorem gram_7_7_3 : Z 7 7 3 = (0 : ℚ) := by
  decide +kernel

theorem gram_7_7_5 : Z 7 7 5 = (-630 : ℚ) := by
  decide +kernel

theorem gram_7_7_7 : Z 7 7 7 = (4410 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Gram07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem gram_7 : gramRational 7 =
  !![1440, 0, -360, 2520;
    0, 0, 0, 0;
    -360, 0, 90, -630;
    2520, 0, -630, 4410] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact gram_7_1_1
  · exact gram_7_1_3
  · exact gram_7_1_5
  · exact gram_7_1_7
  · exact gram_7_3_1
  · exact gram_7_3_3
  · exact gram_7_3_5
  · exact gram_7_3_7
  · exact gram_7_5_1
  · exact gram_7_5_3
  · exact gram_7_5_5
  · exact gram_7_5_7
  · exact gram_7_7_1
  · exact gram_7_7_3
  · exact gram_7_7_5
  · exact gram_7_7_7

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Positive07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem ldl_7_s50_oai : compressedRational 7 =
    lower_7 * Matrix.diagonal pivots_7 * lower_7.transpose := by
  unfold compressedRational middleRational
  rw [gram_7, error_7_s50]
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.ldl_7_s50_oai := @OAI.Laughlin.Certificate.ldl_7_s50_oai
