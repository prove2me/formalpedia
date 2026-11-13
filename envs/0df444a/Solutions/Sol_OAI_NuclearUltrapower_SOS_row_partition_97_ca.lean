-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_97_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:09:17.905362+00:00
-- url     : https://prove2.me/submissions/df8eec20-baf5-4422-b5e1-c75e5497889e

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
theorem row_partition_97_ca_oai : normalize matLe residualRow97 = normalize matLe rowBuckets97.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_97_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_97_ca_oai
