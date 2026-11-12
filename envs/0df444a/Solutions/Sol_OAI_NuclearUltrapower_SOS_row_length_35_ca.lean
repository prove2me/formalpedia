-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_35_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:12:35.997437+00:00
-- url     : https://prove2.me/submissions/f59cf9c0-ce62-404c-a481-d94042cc014a

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
theorem row_length_35_ca_oai : rowBuckets35.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_35_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_35_ca_oai
