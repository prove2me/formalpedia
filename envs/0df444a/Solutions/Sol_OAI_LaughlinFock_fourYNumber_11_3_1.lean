-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:36:43.859968+00:00
-- url     : https://prove2.me/submissions/bb3c97bf-a66b-4991-bdbb-300e0c8fd0ce

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate11Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_11_3_1_oai :
    (collectedFourPartsTrace 11 3 1 collectedFourData_11 : ℚ) / fourCommonDenominator = (-492518176620867562155352785603/26843545600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_3_1_oai := @OAI.LaughlinFock.fourYNumber_11_3_1_oai
