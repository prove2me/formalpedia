-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_89_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:24:24.225747+00:00
-- url     : https://prove2.me/submissions/9a038bc8-6d97-404c-9747-0281d55aba2a

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
theorem bucket_aug_89_ca_oai : ((residualBucket 89).map Prod.snd).sum = 121685800 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_89_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_89_ca_oai
