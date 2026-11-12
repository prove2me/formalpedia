-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_113_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:09:30.789+00:00
-- url     : https://prove2.me/submissions/81d2a742-5a7b-454b-9f50-b4f704afca85

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
theorem row_length_113_ca_oai : rowBuckets113.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_113_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_113_ca_oai
