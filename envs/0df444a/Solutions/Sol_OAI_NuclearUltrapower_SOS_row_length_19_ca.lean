-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_19_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:44:44.460812+00:00
-- url     : https://prove2.me/submissions/181dcf09-d450-4f22-8046-307e13866b7d

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
theorem row_length_19_ca_oai : rowBuckets19.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_19_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_19_ca_oai
