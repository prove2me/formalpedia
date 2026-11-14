-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_57_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:46:03.870131+00:00
-- url     : https://prove2.me/submissions/37aaf2e7-5158-4cca-8d52-6f9b1246ac25

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
theorem bucket_aug_57_ca_oai : ((residualBucket 57).map Prod.snd).sum = -9276780 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_57_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_57_ca_oai
