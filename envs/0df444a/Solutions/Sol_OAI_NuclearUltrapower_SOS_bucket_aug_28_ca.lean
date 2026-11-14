-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_28_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:42:43.050657+00:00
-- url     : https://prove2.me/submissions/73db39fd-e40b-4001-bc19-89b00e637623

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
theorem bucket_aug_28_ca_oai : ((residualBucket 28).map Prod.snd).sum = 28815890 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_28_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_28_ca_oai
