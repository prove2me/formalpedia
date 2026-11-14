-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_36_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:00:45.787207+00:00
-- url     : https://prove2.me/submissions/8f93dfbe-da1c-4080-ae3b-7308b2cc30df

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
theorem bucket_aug_36_ca_oai : ((residualBucket 36).map Prod.snd).sum = -77765930 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_36_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_36_ca_oai
