-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_75_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:43:08.412227+00:00
-- url     : https://prove2.me/submissions/4b450019-17ee-48f4-8b01-3afe2a22cb4f

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
theorem bucket_aug_75_ca_oai : ((residualBucket 75).map Prod.snd).sum = 5318400 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_75_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_75_ca_oai
