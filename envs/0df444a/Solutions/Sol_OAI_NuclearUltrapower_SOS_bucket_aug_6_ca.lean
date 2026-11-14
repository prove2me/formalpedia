-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_6_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:13:31.979526+00:00
-- url     : https://prove2.me/submissions/d88c81ea-4d8b-4e9e-a35a-1d39f83e6b2e

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
theorem bucket_aug_6_ca_oai : ((residualBucket 6).map Prod.snd).sum = -38879790 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_6_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_6_ca_oai
