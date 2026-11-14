-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_3_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:55:42.402025+00:00
-- url     : https://prove2.me/submissions/17b2537c-7545-4de7-8f0b-2424eb58c5f9

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
theorem bucket_aug_3_ca_oai : ((residualBucket 3).map Prod.snd).sum = 4215470 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_3_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_3_ca_oai
