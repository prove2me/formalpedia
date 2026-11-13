-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_113_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:21:20.864365+00:00
-- url     : https://prove2.me/submissions/20d72e61-5755-4950-bf47-ab0ca604987e

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
theorem bucket_aug_113_ca_oai : ((residualBucket 113).map Prod.snd).sum = 146491880 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_113_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_113_ca_oai
