-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.mem_getD_flatten
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:00:25.119946+00:00
-- url     : https://prove2.me/submissions/d56331e3-24a4-4109-be8c-259736dce70c

import Mathlib

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace NuclearUltrapower.SOS
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem mem_getD_flatten_oai {a : α} (rs : List (List α)) (n : ℕ) (h : a ∈ rs.getD n []) :
    a ∈ rs.flatten := by
  induction rs generalizing n with
  | nil => simp at h
  | cons r rs ih =>
    cases n with
    | zero => exact List.mem_append_left _ (by simpa using h)
    | succ n => exact List.mem_append_right _ (ih n (by simpa using h))

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.mem_getD_flatten_oai.{u_1} := @OAI.NuclearUltrapower.SOS.mem_getD_flatten_oai.{u_1}
