-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_104_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:30:21.031937+00:00
-- url     : https://prove2.me/submissions/e24f73fd-1ec4-4970-8d95-ae8f4164ad62

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
theorem row_length_104_ca_oai : rowBuckets104.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_104_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_104_ca_oai
