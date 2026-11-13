-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_6_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T18:55:44.318753+00:00
-- url     : https://prove2.me/submissions/724255ee-dd8f-46da-aef3-c2bc8d80a5ec

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
theorem row_partition_6_ca_oai : normalize matLe residualRow6 = normalize matLe rowBuckets6.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_6_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_6_ca_oai
