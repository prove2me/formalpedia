-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_12_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:06:47.46238+00:00
-- url     : https://prove2.me/submissions/a0ee52f9-3d53-4b6f-ad3b-8461148dd563

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
theorem bucket_aug_12_ca_oai : ((residualBucket 12).map Prod.snd).sum = -91472600 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_12_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_12_ca_oai
