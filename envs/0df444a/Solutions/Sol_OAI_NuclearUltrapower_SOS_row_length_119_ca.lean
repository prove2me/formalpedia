-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_119_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:42:00.387316+00:00
-- url     : https://prove2.me/submissions/1559ce74-a82d-4ffd-80da-1591c4ddbe22

import Mathlib
import Definitions.Def_OAIQ229C013

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_119_ca_oai : rowBuckets119.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_119_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_119_ca_oai
