-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_16_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:31:06.510132+00:00
-- url     : https://prove2.me/submissions/dba8b38a-1cc4-488c-8e74-80b486829eef

import Mathlib
import Definitions.Def_OAIQ229C013
import Definitions.Def_OAIQ229C015

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
theorem row_partition_16_ca_oai : normalize matLe residualRow16 = normalize matLe rowBuckets16.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_16_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_16_ca_oai
