-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_104_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T15:18:26.748674+00:00
-- url     : https://prove2.me/submissions/c6771d70-d850-4338-8d3f-a63dbddf5db1

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
theorem row_partition_104_ca_oai : normalize matLe residualRow104 = normalize matLe rowBuckets104.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_104_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_104_ca_oai
