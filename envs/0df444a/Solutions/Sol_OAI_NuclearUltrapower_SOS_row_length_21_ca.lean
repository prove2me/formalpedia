-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_21_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:33:50.611325+00:00
-- url     : https://prove2.me/submissions/5f5be1dc-5745-4ece-8306-27a6b2539093

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
theorem row_length_21_ca_oai : rowBuckets21.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_21_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_21_ca_oai
