-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_50_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:27:35.685199+00:00
-- url     : https://prove2.me/submissions/e665aba3-fdaf-400e-a247-43cef135e14c

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
theorem bucket_aug_50_ca_oai : ((residualBucket 50).map Prod.snd).sum = 41605070 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_50_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_50_ca_oai
