-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_49_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:58:47.835141+00:00
-- url     : https://prove2.me/submissions/acb6c397-0ae0-4f90-9e99-7aa6d220d8ec

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
theorem bucket_aug_49_ca_oai : ((residualBucket 49).map Prod.snd).sum = -144536590 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_49_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_49_ca_oai
