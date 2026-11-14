-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_75_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:23:20.166995+00:00
-- url     : https://prove2.me/submissions/fc9d2de7-738d-4d94-841e-7a9347ac3433

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
theorem bucket_l1_75_ca_oai : intL1 (residualBucket 75) = 186198180 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_75_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_75_ca_oai
