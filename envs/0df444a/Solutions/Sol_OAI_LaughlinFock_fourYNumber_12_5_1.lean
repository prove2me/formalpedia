-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_12_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T22:45:30.25801+00:00
-- url     : https://prove2.me/submissions/cc3b18e7-6d08-4d0a-a4d7-00715a86d692

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



theorem fourYNumber_12_5_1_oai :
    (shortNumericRowsFourTrace 12 5 1 : ℚ) / fourCommonDenominator = (68097845461495289881861573857/1677721600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_12_5_1_oai := @OAI.LaughlinFock.fourYNumber_12_5_1_oai
