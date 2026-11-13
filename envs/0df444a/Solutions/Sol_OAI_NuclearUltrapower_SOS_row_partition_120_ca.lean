-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_120_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T15:08:50.143239+00:00
-- url     : https://prove2.me/submissions/c1b3f768-1b92-4872-9724-6a3c168c9955

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
theorem row_partition_120_ca_oai : normalize matLe residualRow120 = normalize matLe rowBuckets120.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_120_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_120_ca_oai
