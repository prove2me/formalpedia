-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_120_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T02:16:47.648907+00:00
-- url     : https://prove2.me/submissions/9f5343c5-2d5b-4b13-9e0b-ec9c57f5b8e2

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
theorem bucket_aug_120_ca_oai : ((residualBucket 120).map Prod.snd).sum = -95260540 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_120_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_120_ca_oai
