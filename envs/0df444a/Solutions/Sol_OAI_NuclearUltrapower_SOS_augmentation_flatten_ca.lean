-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.augmentation_flatten_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:28:07.039528+00:00
-- url     : https://prove2.me/submissions/21228fba-fc45-4494-950f-7a5a151f00bb

import Mathlib
import Definitions.Def_OAIQ229C023

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

theorem augmentation_flatten_ca_oai {α : Type*} (rs : List (Poly α)) :
    augmentation rs.flatten = (rs.map augmentation).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [augmentation, List.map_append, List.sum_append, List.flatten_cons, List.map_cons, List.sum_cons] at *
    exact congrArg (fun t : ℤ => augmentation r + t) ih

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.NuclearUltrapower.SOS.augmentation_flatten_ca_oai.{u_2} := @OAI.NuclearUltrapower.SOS.augmentation_flatten_ca_oai.{u_2}
