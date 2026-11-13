-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_61_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:16:37.282366+00:00
-- url     : https://prove2.me/submissions/f75ff89b-0ee3-434e-aaa4-8a3f5d451d6e

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
theorem row_length_61_ca_oai : rowBuckets61.length = 128 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_61_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_61_ca_oai
