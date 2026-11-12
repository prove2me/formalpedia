-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_31_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T00:06:46.404205+00:00
-- url     : https://prove2.me/submissions/c419f96a-0078-405c-87f4-5e763b7510c7

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
theorem row_length_31_ca_oai : rowBuckets31.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_31_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_31_ca_oai
