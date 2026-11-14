-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_22_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:24:43.263202+00:00
-- url     : https://prove2.me/submissions/4b751b19-715e-440c-85bb-2c10ff987c3c

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
theorem bucket_l1_22_ca_oai : intL1 (residualBucket 22) = 251588480 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_22_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_22_ca_oai
