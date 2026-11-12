-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_43_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:53:43.358168+00:00
-- url     : https://prove2.me/submissions/e614014f-9d8a-4219-94f5-fb952c5adb13

import Mathlib
import Definitions.Def_OAIQ229C021

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_43_ca_oai : rowBuckets43.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_43_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_43_ca_oai
