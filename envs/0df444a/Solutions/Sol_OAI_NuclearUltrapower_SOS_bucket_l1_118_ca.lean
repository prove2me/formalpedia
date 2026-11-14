-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_118_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:56:55.676819+00:00
-- url     : https://prove2.me/submissions/0b9f3949-4c73-4f98-8e65-bc7277e57f8a

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
theorem bucket_l1_118_ca_oai : intL1 (residualBucket 118) = 304887660 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_118_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_118_ca_oai
