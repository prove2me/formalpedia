-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_115_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:36.965672+00:00
-- url     : https://prove2.me/submissions/a7154ce3-f19d-4839-afe8-d13c47f35963

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
theorem row_partition_115_ca_oai : normalize matLe residualRow115 = normalize matLe rowBuckets115.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_115_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_115_ca_oai
