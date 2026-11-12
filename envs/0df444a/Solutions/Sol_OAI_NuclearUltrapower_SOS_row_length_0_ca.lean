-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_0_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:28:05.881614+00:00
-- url     : https://prove2.me/submissions/7e6ba13b-7e81-40b3-93ef-50d294e12705

import Mathlib
import Definitions.Def_OAIQ229C003

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_0_ca_oai : rowBuckets0.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_0_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_0_ca_oai
