-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_107_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:25:05.112254+00:00
-- url     : https://prove2.me/submissions/5b51f9dc-49ec-447b-bc9f-c8d8da3411fc

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
theorem row_length_107_ca_oai : rowBuckets107.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_107_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_107_ca_oai
