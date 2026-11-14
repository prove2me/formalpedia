-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_105_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:50:47.173208+00:00
-- url     : https://prove2.me/submissions/bbbb9daf-2264-4841-90bd-4090e330c068

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
theorem bucket_aug_105_ca_oai : ((residualBucket 105).map Prod.snd).sum = 51941160 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_105_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_105_ca_oai
