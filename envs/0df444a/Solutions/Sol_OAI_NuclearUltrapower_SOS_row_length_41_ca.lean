-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_41_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:14:41.350344+00:00
-- url     : https://prove2.me/submissions/124e29c5-8d2b-46cc-9608-a4d273883be6

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
theorem row_length_41_ca_oai : rowBuckets41.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_41_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_41_ca_oai
