-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_80_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:32:52.686658+00:00
-- url     : https://prove2.me/submissions/4d42cd5e-d773-4eb5-97ec-27d57c068f07

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
theorem bucket_l1_80_ca_oai : intL1 (residualBucket 80) = 117164430 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_80_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_80_ca_oai
