-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_102_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T03:23:14.599732+00:00
-- url     : https://prove2.me/submissions/e0cecf5e-1ccd-4b77-a45a-6b50bbf33053

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
theorem bucket_aug_102_ca_oai : ((residualBucket 102).map Prod.snd).sum = 113079350 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_102_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_102_ca_oai
