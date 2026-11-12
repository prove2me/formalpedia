-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_20_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:14:35.163232+00:00
-- url     : https://prove2.me/submissions/09c5e6f5-0ae9-47f3-90cd-f3ef3265a11d

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
theorem row_length_20_ca_oai : rowBuckets20.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_20_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_20_ca_oai
