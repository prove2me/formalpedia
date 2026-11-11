-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.sum_getD_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T02:09:05.079128+00:00
-- url     : https://prove2.me/submissions/80989c36-cc8d-4558-aa39-9f988d0c131b

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
theorem sum_getD_ca_oai (N : ℕ) (p : List A) (h : p.length ≤ N) :
    ((List.range N).map (fun i => p.getD i 0)).sum = p.sum := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    simp [hp]
  | succ N ih =>
    cases p with
    | nil => simp
    | cons a p =>
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
        List.getD_cons_zero, List.getD_cons_succ, List.sum_cons]
      rw [ih p (by simpa using h)]

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.NuclearUltrapower.SOS.sum_getD_ca_oai.{u_2} := @OAI.NuclearUltrapower.SOS.sum_getD_ca_oai.{u_2}
