-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_118_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:59:25.75193+00:00
-- url     : https://prove2.me/submissions/f1ea523c-092d-478f-bc0e-bc0c5fd6bc41

import Mathlib
import Definitions.Def_OAIQ229C020

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_118_ca_oai : rowBuckets118.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_118_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_118_ca_oai
