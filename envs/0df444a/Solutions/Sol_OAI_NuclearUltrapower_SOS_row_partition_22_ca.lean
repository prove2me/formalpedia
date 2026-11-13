-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_22_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:57:57.261069+00:00
-- url     : https://prove2.me/submissions/e28a1545-3516-477f-a042-6c8aca3682ff

import Mathlib
import Definitions.Def_OAIQ229C015
import Definitions.Def_OAIQ229C020

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_partition_22_ca_oai : normalize matLe residualRow22 = normalize matLe rowBuckets22.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_22_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_22_ca_oai
