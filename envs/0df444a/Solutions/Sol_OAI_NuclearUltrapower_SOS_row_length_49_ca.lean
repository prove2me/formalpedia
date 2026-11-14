-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_49_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:48:21.391195+00:00
-- url     : https://prove2.me/submissions/696e10b2-d2aa-4ef1-a1b6-2928cb6f3f18

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
theorem row_length_49_ca_oai : rowBuckets49.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_49_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_49_ca_oai
