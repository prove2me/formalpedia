-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_30_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:03:06.981222+00:00
-- url     : https://prove2.me/submissions/c11b27e1-4d3f-4b73-b9c0-16f23a3ca2ad

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
theorem bucket_aug_30_ca_oai : ((residualBucket 30).map Prod.snd).sum = -22839520 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_30_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_30_ca_oai
