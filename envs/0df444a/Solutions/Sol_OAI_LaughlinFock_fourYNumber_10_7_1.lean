-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_7_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:27:59.150143+00:00
-- url     : https://prove2.me/submissions/edf3b7e7-0f2b-42ad-a18e-c4bd14bd5b39

import Mathlib
import Definitions.Def_OAIQ084L002
import Definitions.Def_OAIQ084L009

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_10_7_1_oai :
    (collectedFourPartsTrace 10 7 1 collectedFourData_10 : ℚ) / fourCommonDenominator = (-424730358650114657260778608119/536870912000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_7_1_oai := @OAI.LaughlinFock.fourYNumber_10_7_1_oai
