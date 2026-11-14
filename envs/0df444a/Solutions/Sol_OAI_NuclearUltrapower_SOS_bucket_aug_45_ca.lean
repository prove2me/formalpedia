-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_45_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:57:15.19728+00:00
-- url     : https://prove2.me/submissions/da5e5fda-1078-4c0c-9b50-31c0fba9342c

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
theorem bucket_aug_45_ca_oai : ((residualBucket 45).map Prod.snd).sum = 2229820 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_45_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_45_ca_oai
