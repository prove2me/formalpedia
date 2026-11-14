-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_73_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:23:55.534296+00:00
-- url     : https://prove2.me/submissions/0e88ae26-f125-4d84-82e1-204d88182fa5

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
theorem bucket_aug_73_ca_oai : ((residualBucket 73).map Prod.snd).sum = 63988550 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_73_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_73_ca_oai
