-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:27:35.409401+00:00
-- url     : https://prove2.me/submissions/116bb3a1-8b3b-4b1d-aaff-70b8224d3f2f

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



theorem fourYNumber_10_3_1_oai :
    (collectedFourPartsTrace 10 3 1 collectedFourData_10 : ℚ) / fourCommonDenominator = (-340762940414160772908009142467/134217728000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_3_1_oai := @OAI.LaughlinFock.fourYNumber_10_3_1_oai
