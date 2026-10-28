-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_12_9_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:41:22.649478+00:00
-- url     : https://prove2.me/submissions/fa5a2b90-8cc0-4f88-b123-a4d8885a3229

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



theorem fourYNumber_12_9_3_oai :
    (shortNumericRowsFourTrace 12 9 3 : ℚ) / fourCommonDenominator = (60751252291694576857824915477/134217728000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_12_9_3_oai := @OAI.LaughlinFock.fourYNumber_12_9_3_oai
