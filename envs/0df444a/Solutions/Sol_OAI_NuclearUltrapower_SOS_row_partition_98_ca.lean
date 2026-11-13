-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_98_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:55:49.309211+00:00
-- url     : https://prove2.me/submissions/7538715f-f377-4d02-aa6a-87c766be48c4

import Mathlib
import Definitions.Def_OAIQ229C023

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
theorem row_partition_98_ca_oai : normalize matLe residualRow98 = normalize matLe rowBuckets98.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_98_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_98_ca_oai
