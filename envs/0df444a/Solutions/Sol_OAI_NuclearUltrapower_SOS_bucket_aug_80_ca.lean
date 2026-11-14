-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_80_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:35:24.594422+00:00
-- url     : https://prove2.me/submissions/6c0a26f7-34fd-4037-a446-67ac9f0b55de

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
theorem bucket_aug_80_ca_oai : ((residualBucket 80).map Prod.snd).sum = 3210730 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_80_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_80_ca_oai
