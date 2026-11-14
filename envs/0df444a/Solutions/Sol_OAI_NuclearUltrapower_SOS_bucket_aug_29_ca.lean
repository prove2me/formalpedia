-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_29_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:44:37.927935+00:00
-- url     : https://prove2.me/submissions/84339802-e60c-4186-ac65-703253230527

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
theorem bucket_aug_29_ca_oai : ((residualBucket 29).map Prod.snd).sum = 29223400 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_29_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_29_ca_oai
