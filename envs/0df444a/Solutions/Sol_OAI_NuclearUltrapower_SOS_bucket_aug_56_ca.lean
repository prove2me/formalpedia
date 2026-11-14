-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_56_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:10:58.022629+00:00
-- url     : https://prove2.me/submissions/a8aba2b6-6c2f-43ab-90f3-196cdb652a9d

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
theorem bucket_aug_56_ca_oai : ((residualBucket 56).map Prod.snd).sum = -7113600 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_56_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_56_ca_oai
