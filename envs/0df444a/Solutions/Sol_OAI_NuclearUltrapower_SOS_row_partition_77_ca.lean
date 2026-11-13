-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_77_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T00:57:50.341576+00:00
-- url     : https://prove2.me/submissions/b6f4f840-2fc6-4361-9645-904fe3a35f0a

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
theorem row_partition_77_ca_oai : normalize matLe residualRow77 = normalize matLe rowBuckets77.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_77_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_77_ca_oai
