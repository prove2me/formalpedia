-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_61_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:03:32.40675+00:00
-- url     : https://prove2.me/submissions/993363d2-890a-468c-b3c3-68ae8abc3a96

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
theorem bucket_aug_61_ca_oai : ((residualBucket 61).map Prod.snd).sum = 47824620 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_61_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_61_ca_oai
