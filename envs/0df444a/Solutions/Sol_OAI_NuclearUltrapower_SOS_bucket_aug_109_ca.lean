-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_109_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:45:22.465877+00:00
-- url     : https://prove2.me/submissions/c2ac6e64-23e0-433b-90ff-00a1dd1a9b1d

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
theorem bucket_aug_109_ca_oai : ((residualBucket 109).map Prod.snd).sum = -51857680 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_109_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_109_ca_oai
