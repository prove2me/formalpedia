-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_8_7_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:08:00.139104+00:00
-- url     : https://prove2.me/submissions/b0c991ff-ad32-4ad6-b5ca-c3c049d40ca6

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_8_7_3_oai :
    (collectedFourPartsTrace 8 7 3 collectedFourData_8 : ℚ) / fourCommonDenominator = (-12382701644617792221325809759/4294967296000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_8_7_3_oai := @OAI.LaughlinFock.fourYNumber_8_7_3_oai
