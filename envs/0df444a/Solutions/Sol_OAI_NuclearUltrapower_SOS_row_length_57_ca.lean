-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_57_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:38:19.1462+00:00
-- url     : https://prove2.me/submissions/5be6b7f3-3587-4315-91bb-64260838ebcc

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
theorem row_length_57_ca_oai : rowBuckets57.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_57_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_57_ca_oai
