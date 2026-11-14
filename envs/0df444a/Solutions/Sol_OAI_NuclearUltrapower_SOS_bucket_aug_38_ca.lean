-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_38_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:22:28.066121+00:00
-- url     : https://prove2.me/submissions/7ee9f7d9-03ad-4210-b510-c0fe19d0bce4

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
theorem bucket_aug_38_ca_oai : ((residualBucket 38).map Prod.snd).sum = -93604140 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_38_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_38_ca_oai
