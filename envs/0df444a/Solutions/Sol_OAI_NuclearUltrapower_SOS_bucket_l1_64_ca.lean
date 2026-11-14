-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_64_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:12:34.414977+00:00
-- url     : https://prove2.me/submissions/4e330988-6ee0-4947-9dd1-e670d6789625

import Mathlib
import Definitions.Def_OAIQ229C027

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem bucket_l1_64_ca_oai : intL1 (residualBucket 64) = 209492550 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_64_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_64_ca_oai
