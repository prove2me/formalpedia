-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:11:39.671252+00:00
-- url     : https://prove2.me/submissions/876e8c47-988f-4695-ad95-284981c79d06

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_9_3_3_oai :
    (collectedFourPartsTrace 9 3 3 collectedFourData_9 : ℚ) / fourCommonDenominator = (-128380238690076998480031524721/7516192768000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_9_3_3_oai := @OAI.LaughlinFock.fourYNumber_9_3_3_oai
