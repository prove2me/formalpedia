-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_120_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:25:36.112422+00:00
-- url     : https://prove2.me/submissions/3860cf72-646d-49ef-aa8a-c5bdc0fc52e2

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
theorem row_length_120_ca_oai : rowBuckets120.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_120_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_120_ca_oai
