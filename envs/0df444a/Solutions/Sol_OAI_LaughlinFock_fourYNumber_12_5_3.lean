-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_12_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:45:52.695038+00:00
-- url     : https://prove2.me/submissions/6e3fd2b1-08f4-4e64-a932-b474afe87254

import Mathlib
import Definitions.Def_OAIQ084L015

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate12Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate12 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_12_5_3_oai :
    (shortNumericRowsFourTrace 12 5 3 : ℚ) / fourCommonDenominator = (213044818522802951430393957/13421772800000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_12_5_3_oai := @OAI.LaughlinFock.fourYNumber_12_5_3_oai
