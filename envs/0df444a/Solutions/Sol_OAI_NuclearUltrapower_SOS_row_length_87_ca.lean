-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_87_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:22:35.010038+00:00
-- url     : https://prove2.me/submissions/f0c2ec33-583b-4009-8244-5e043dbc2027

import Mathlib
import Definitions.Def_OAIQ229C022

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_length_87_ca_oai : rowBuckets87.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_87_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_87_ca_oai
