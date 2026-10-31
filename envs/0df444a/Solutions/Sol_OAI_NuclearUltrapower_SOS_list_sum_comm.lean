-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.list_sum_comm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:00:23.750104+00:00
-- url     : https://prove2.me/submissions/07abd483-ce09-455a-8c25-cb3ad3ad8d7c

import Mathlib

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
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
theorem list_sum_comm_oai (x : List β) (y : List γ) (f : β → γ → A) :
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

theorem solution.{u_2, u_3, u_4} : type_of% @OAI.NuclearUltrapower.SOS.list_sum_comm_oai.{u_2, u_3, u_4} := @OAI.NuclearUltrapower.SOS.list_sum_comm_oai.{u_2, u_3, u_4}
