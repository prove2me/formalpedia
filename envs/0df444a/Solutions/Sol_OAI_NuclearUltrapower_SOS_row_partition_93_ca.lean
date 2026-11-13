-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_93_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T01:57:28.466224+00:00
-- url     : https://prove2.me/submissions/8df6ab46-93ee-49f4-b4bd-8b6ee0d1f703

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
theorem row_partition_93_ca_oai : normalize matLe residualRow93 = normalize matLe rowBuckets93.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_93_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_93_ca_oai
