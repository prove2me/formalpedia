-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_4_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:32:06.614334+00:00
-- url     : https://prove2.me/submissions/a720f5a6-d344-42ed-b1fe-653f4e6df485

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
theorem bucket_aug_4_ca_oai : ((residualBucket 4).map Prod.snd).sum = -101262360 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_4_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_4_ca_oai
