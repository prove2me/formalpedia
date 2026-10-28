-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_9_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:10:33.720492+00:00
-- url     : https://prove2.me/submissions/b2ac6015-2853-4c1e-8f81-9163cb58ff8f

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



theorem fourYNumber_9_3_1_oai :
    (collectedFourPartsTrace 9 3 1 collectedFourData_9 : ℚ) / fourCommonDenominator = (-27122971776637241097052043481/536870912000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_9_3_1_oai := @OAI.LaughlinFock.fourYNumber_9_3_1_oai
