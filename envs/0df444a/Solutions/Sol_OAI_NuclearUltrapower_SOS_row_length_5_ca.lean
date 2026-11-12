-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_5_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:04:48.877975+00:00
-- url     : https://prove2.me/submissions/dbe78add-24c0-477c-ab6a-00f956096e9e

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
theorem row_length_5_ca_oai : rowBuckets5.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_5_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_5_ca_oai
