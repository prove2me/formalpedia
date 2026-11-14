-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_59_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:09:24.32134+00:00
-- url     : https://prove2.me/submissions/6f5aa52b-886f-478c-a4c6-0860b3cb6b70

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
theorem bucket_aug_59_ca_oai : ((residualBucket 59).map Prod.snd).sum = 14346260 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_59_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_59_ca_oai
