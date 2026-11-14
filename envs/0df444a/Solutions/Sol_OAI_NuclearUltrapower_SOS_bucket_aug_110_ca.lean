-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_110_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:07:05.681681+00:00
-- url     : https://prove2.me/submissions/6cb6b8a7-ee8e-4a33-a655-ac9792e8d7d2

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
theorem bucket_aug_110_ca_oai : ((residualBucket 110).map Prod.snd).sum = -15435340 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_110_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_110_ca_oai
