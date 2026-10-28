-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_11_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:46:21.881413+00:00
-- url     : https://prove2.me/submissions/270eadbd-2ba9-4b0b-8765-2c70abcb5971

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



theorem fourYNumber_13_11_7_oai :
    (collectedFourPartsTrace 13 11 7 collectedFourData_13 : ℚ) / fourCommonDenominator = (70075598168791046625716962809/214748364800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_11_7_oai := @OAI.LaughlinFock.fourYNumber_13_11_7_oai
