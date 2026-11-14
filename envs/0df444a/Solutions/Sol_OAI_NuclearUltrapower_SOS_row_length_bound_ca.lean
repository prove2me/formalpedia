-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_bound_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:40:49.762195+00:00
-- url     : https://prove2.me/submissions/c8f7e46c-5337-4c79-90e1-2f5b8ef9cf45

import Mathlib
import Definitions.Def_OAIQ229C031
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_lengths_ca

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {A : Type*} [AddCommGroup A]

theorem row_length_bound_ca_oai : ∀ r ∈ allRowBuckets, r.length ≤ 128 := by
  intro r hr
  have h := List.mem_map_of_mem (f := List.length) hr
  rw [row_lengths_ca] at h
  have : r.length = 128 := (List.mem_replicate.mp h).2
  omega

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_bound_ca_oai := @OAI.NuclearUltrapower.SOS.row_length_bound_ca_oai
