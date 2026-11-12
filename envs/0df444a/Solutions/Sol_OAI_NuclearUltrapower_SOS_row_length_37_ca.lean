-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_37_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:12:56.976662+00:00
-- url     : https://prove2.me/submissions/543e46fb-9d39-4e44-a230-fb36fc111ccd

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
theorem row_length_37_ca_oai : rowBuckets37.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_37_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_37_ca_oai
