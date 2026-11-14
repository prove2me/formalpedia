-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_13_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:08:59.543978+00:00
-- url     : https://prove2.me/submissions/718c88d4-4895-4f01-86d7-91ca7f16a59d

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
theorem bucket_l1_13_ca_oai : intL1 (residualBucket 13) = 280768760 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_13_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_13_ca_oai
