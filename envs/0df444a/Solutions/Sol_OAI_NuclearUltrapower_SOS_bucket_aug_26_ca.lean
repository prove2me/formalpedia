-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_26_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:39:21.770574+00:00
-- url     : https://prove2.me/submissions/f5a60f20-d849-4836-af61-1bc9462f27b2

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
theorem bucket_aug_26_ca_oai : ((residualBucket 26).map Prod.snd).sum = 141379490 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_26_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_26_ca_oai
