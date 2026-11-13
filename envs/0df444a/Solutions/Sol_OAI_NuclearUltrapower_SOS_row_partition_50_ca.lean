-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_50_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:19:11.506208+00:00
-- url     : https://prove2.me/submissions/2940fe1c-e75a-4bd0-a673-ec0bac3dd24d

import Mathlib
import Definitions.Def_OAIQ229C015
import Definitions.Def_OAIQ229C021

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
theorem row_partition_50_ca_oai : normalize matLe residualRow50 = normalize matLe rowBuckets50.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_50_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_50_ca_oai
