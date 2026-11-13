-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_13_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:29:28.397199+00:00
-- url     : https://prove2.me/submissions/6b8f2b9a-54a5-4b5d-8d50-c3c7c1d56319

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
theorem bucket_aug_13_ca_oai : ((residualBucket 13).map Prod.snd).sum = 40000560 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_13_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_13_ca_oai
