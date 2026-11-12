-- Prove2me | solution 1 for OAI.NuclearUltrapower.SL3Certificate.gram_row_23_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:07:23.373621+00:00
-- url     : https://prove2.me/submissions/4a9a25c8-1456-49b1-8bea-4b0d195f9717

import Mathlib
import Definitions.Def_OAIQ229C004
import Definitions.Def_OAIQ229C005

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
theorem gram_row_23_ca_oai : columns.map (dot q23) = g23 := by decide +kernel
end NuclearUltrapower.SL3Certificate
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SL3Certificate.gram_row_23_ca_oai := @OAI.NuclearUltrapower.SL3Certificate.gram_row_23_ca_oai
