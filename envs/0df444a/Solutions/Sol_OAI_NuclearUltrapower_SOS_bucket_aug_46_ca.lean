-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_46_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:19:07.11821+00:00
-- url     : https://prove2.me/submissions/cb3b8bc7-595f-46d2-9eff-8b2be95935b7

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
theorem bucket_aug_46_ca_oai : ((residualBucket 46).map Prod.snd).sum = -38659920 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_46_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_46_ca_oai
