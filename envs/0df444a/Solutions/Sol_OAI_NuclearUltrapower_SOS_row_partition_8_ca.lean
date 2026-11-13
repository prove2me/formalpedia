-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_8_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T02:11:52.128654+00:00
-- url     : https://prove2.me/submissions/ca267541-e758-48e6-86fe-3ac8ffb06839

import Mathlib
import Definitions.Def_OAIQ229C022

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
theorem row_partition_8_ca_oai : normalize matLe residualRow8 = normalize matLe rowBuckets8.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_8_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_8_ca_oai
