-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_126_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:27:41.104195+00:00
-- url     : https://prove2.me/submissions/7d8398d1-c1c2-4f2a-84ad-bc10d230772b

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
theorem bucket_aug_126_ca_oai : ((residualBucket 126).map Prod.snd).sum = 145542560 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_126_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_126_ca_oai
