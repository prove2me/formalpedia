-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_13_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:48:13.41146+00:00
-- url     : https://prove2.me/submissions/0b83806c-27e7-4f6e-95a5-6dae6b580c73

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



theorem fourYNumber_13_13_13_oai :
    (collectedFourPartsTrace 13 13 13 collectedFourData_13 : ℚ) / fourCommonDenominator = (-1524949629653034503076717749619/26843545600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_13_13_oai := @OAI.LaughlinFock.fourYNumber_13_13_13_oai
