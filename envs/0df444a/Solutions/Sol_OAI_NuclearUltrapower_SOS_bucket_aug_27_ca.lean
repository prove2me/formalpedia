-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_27_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:58:23.529252+00:00
-- url     : https://prove2.me/submissions/30ca9e69-0c60-4884-bd2f-b78f1ce501a2

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
theorem bucket_aug_27_ca_oai : ((residualBucket 27).map Prod.snd).sum = 18519550 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_27_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_27_ca_oai
