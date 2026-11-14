-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_78_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:10:34.184206+00:00
-- url     : https://prove2.me/submissions/f8b4b0b9-4562-4440-8e16-5104d22f8d4b

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
theorem bucket_aug_78_ca_oai : ((residualBucket 78).map Prod.snd).sum = -110871470 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_78_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_78_ca_oai
