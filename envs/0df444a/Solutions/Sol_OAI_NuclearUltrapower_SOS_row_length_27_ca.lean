-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_27_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:13:12.007541+00:00
-- url     : https://prove2.me/submissions/5245bc0f-f8f0-4466-8cb4-158c336e1f1d

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
theorem row_length_27_ca_oai : rowBuckets27.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_27_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_27_ca_oai
