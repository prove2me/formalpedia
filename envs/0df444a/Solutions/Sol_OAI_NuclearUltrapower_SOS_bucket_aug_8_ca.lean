-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_8_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:46:04.824763+00:00
-- url     : https://prove2.me/submissions/54bc5e13-5fd2-4171-ac10-c2d7c75fb9f7

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
theorem bucket_aug_8_ca_oai : ((residualBucket 8).map Prod.snd).sum = -79173390 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_8_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_8_ca_oai
