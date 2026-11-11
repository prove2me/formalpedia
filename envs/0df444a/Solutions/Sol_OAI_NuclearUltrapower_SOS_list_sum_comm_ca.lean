-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.list_sum_comm_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T02:09:03.900674+00:00
-- url     : https://prove2.me/submissions/679f704a-3165-4e9b-a219-6b96e171d762

import Mathlib

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
section BucketSemantics
variable {α A β γ : Type*} [DecidableEq α] [AddCommGroup A]

omit [DecidableEq α] in
theorem list_sum_comm_ca_oai (x : List β) (y : List γ) (f : β → γ → A) :
    (x.map (fun i => (y.map (fun j => f i j)).sum)).sum =
      (y.map (fun j => (x.map (fun i => f i j)).sum)).sum := by
  induction x with
  | nil => simp
  | cons a x ih => simp [List.sum_map_add, ih]

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_2, u_3, u_4} : type_of% @OAI.NuclearUltrapower.SOS.list_sum_comm_ca_oai.{u_2, u_3, u_4} := @OAI.NuclearUltrapower.SOS.list_sum_comm_ca_oai.{u_2, u_3, u_4}
