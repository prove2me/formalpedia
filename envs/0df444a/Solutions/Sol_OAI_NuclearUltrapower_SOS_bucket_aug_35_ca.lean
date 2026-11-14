-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_35_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:57.742205+00:00
-- url     : https://prove2.me/submissions/261c924f-bd90-4d70-ab2c-3013ad9b929b

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
theorem bucket_aug_35_ca_oai : ((residualBucket 35).map Prod.snd).sum = 17470230 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_35_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_35_ca_oai
