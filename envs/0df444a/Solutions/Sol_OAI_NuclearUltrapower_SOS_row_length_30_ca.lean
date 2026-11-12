-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_30_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T00:18:34.452216+00:00
-- url     : https://prove2.me/submissions/2b82b540-b36f-4244-8509-eba8e427555d

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
theorem row_length_30_ca_oai : rowBuckets30.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_30_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_30_ca_oai
