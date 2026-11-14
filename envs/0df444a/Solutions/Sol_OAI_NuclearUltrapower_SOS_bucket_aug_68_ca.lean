-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_68_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:05:32.641186+00:00
-- url     : https://prove2.me/submissions/7a0bdc7b-0568-42e5-a711-4c6766631f41

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
theorem bucket_aug_68_ca_oai : ((residualBucket 68).map Prod.snd).sum = -83458380 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_68_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_68_ca_oai
