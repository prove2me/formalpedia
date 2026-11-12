-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_11_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:18:15.876742+00:00
-- url     : https://prove2.me/submissions/8a5f9910-2c0a-4032-a9f4-6281b2fd46ac

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
theorem row_partition_11_ca_oai : normalize matLe residualRow11 = normalize matLe rowBuckets11.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_11_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_11_ca_oai
