-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.intL1_flatten_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:01:45.975602+00:00
-- url     : https://prove2.me/submissions/5d9c6748-77b3-44c9-8d1e-07149edf7581

import Mathlib
import Definitions.Def_OAIQ229C012
import Definitions.Def_OAIQ229C015

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

theorem intL1_flatten_ca_oai {α : Type*} (rs : List (Poly α)) :
    intL1 rs.flatten = (rs.map intL1).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [intL1, List.map_append, List.sum_append, List.flatten_cons, List.map_cons, List.sum_cons] at *
    exact congrArg (fun t : ℤ => intL1 r + t) ih

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.NuclearUltrapower.SOS.intL1_flatten_ca_oai.{u_2} := @OAI.NuclearUltrapower.SOS.intL1_flatten_ca_oai.{u_2}
