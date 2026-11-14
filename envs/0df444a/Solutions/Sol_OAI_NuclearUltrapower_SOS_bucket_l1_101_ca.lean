-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_101_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:54:39.900298+00:00
-- url     : https://prove2.me/submissions/9b6f8f6e-3b38-45cb-8945-d2f223c0e3b1

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
theorem bucket_l1_101_ca_oai : intL1 (residualBucket 101) = 271363160 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_101_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_101_ca_oai
