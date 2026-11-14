-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_48_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:59:10.896422+00:00
-- url     : https://prove2.me/submissions/699029ee-67a8-4873-90e6-e301752df0b6

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
theorem bucket_aug_48_ca_oai : ((residualBucket 48).map Prod.snd).sum = -34618170 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_48_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_48_ca_oai
