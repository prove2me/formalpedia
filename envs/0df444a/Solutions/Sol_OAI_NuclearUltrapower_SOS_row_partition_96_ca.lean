-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_96_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:04:32.960563+00:00
-- url     : https://prove2.me/submissions/ec21d100-8a1f-4b9f-ba46-0ea0a6883b20

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
theorem row_partition_96_ca_oai : normalize matLe residualRow96 = normalize matLe rowBuckets96.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_96_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_96_ca_oai
