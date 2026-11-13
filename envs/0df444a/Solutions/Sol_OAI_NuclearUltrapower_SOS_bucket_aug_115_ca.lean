-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_115_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T03:42:05.291718+00:00
-- url     : https://prove2.me/submissions/82f49d4a-dc25-405a-8aa7-f8bf8be84f38

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
theorem bucket_aug_115_ca_oai : ((residualBucket 115).map Prod.snd).sum = -433564200 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_115_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_115_ca_oai
