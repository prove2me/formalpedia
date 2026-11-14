-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_20_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:57:38.340215+00:00
-- url     : https://prove2.me/submissions/9865e68c-9504-4daa-8df8-aad08e9773b8

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
theorem bucket_aug_20_ca_oai : ((residualBucket 20).map Prod.snd).sum = -8084230 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_20_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_20_ca_oai
