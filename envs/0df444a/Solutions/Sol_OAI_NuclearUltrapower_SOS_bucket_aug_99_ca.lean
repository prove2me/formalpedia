-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_99_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:43:53.438711+00:00
-- url     : https://prove2.me/submissions/2ea782f3-c1b8-454a-a422-78906a9c9be1

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
theorem bucket_aug_99_ca_oai : ((residualBucket 99).map Prod.snd).sum = 96655650 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_99_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_99_ca_oai
