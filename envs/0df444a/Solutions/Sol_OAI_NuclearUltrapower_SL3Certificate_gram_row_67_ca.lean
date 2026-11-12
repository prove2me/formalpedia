-- Prove2me | solution 1 for OAI.NuclearUltrapower.SL3Certificate.gram_row_67_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:50:51.444524+00:00
-- url     : https://prove2.me/submissions/84a75df9-d165-4eb4-a5c2-a4f431ff2b60

import Mathlib
import Definitions.Def_OAIQ229C004
import Definitions.Def_OAIQ229C006

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
theorem gram_row_67_ca_oai : columns.map (dot q67) = g67 := by decide +kernel
end NuclearUltrapower.SL3Certificate
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SL3Certificate.gram_row_67_ca_oai := @OAI.NuclearUltrapower.SL3Certificate.gram_row_67_ca_oai
