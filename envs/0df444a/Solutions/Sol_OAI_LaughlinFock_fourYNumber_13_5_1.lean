-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:49:43.172006+00:00
-- url     : https://prove2.me/submissions/fd28dc3f-54a8-47a3-b253-f6b6728a23c5

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_13_5_1_oai :
    (collectedFourPartsTrace 13 5 1 collectedFourData_13 : ℚ) / fourCommonDenominator = (-3952251593651960125174045120041/6710886400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_5_1_oai := @OAI.LaughlinFock.fourYNumber_13_5_1_oai
