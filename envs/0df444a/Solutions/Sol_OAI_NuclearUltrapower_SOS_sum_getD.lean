-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.sum_getD
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:00:26.407969+00:00
-- url     : https://prove2.me/submissions/86fe5420-0dbd-43b6-b231-016ebff3f33e

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
theorem sum_getD_oai (N : ℕ) (p : List A) (h : p.length ≤ N) :
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

theorem solution.{u_2} : type_of% @OAI.NuclearUltrapower.SOS.sum_getD_oai.{u_2} := @OAI.NuclearUltrapower.SOS.sum_getD_oai.{u_2}
