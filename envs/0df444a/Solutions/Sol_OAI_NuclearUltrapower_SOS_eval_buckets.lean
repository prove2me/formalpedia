-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.eval_buckets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:03:17.049964+00:00
-- url     : https://prove2.me/submissions/cbed710e-bd43-453e-a54c-a6eafef33997

import Mathlib
import Definitions.Def_OAIQ019N047
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_normalize
import Theorems.Thm_OAI_NuclearUltrapower_SOS_list_sum_comm
import Theorems.Thm_OAI_NuclearUltrapower_SOS_sum_getD

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
section BucketSemantics
variable {α A β γ : Type*} [DecidableEq α] [AddCommGroup A]

theorem eval_buckets_oai (n : ℕ) (rs : List (List (Poly α)))
    (h : ∀ r ∈ rs, r.length ≤ n) (f : α → A) (le : α → α → Bool) :
    eval f ((List.range n).flatMap (fun b => normalize le (rs.flatMap (fun r => r.getD b [])))) =
      eval f (rs.flatMap List.flatten) := by
  simp only [eval_flatMap, eval_normalize]
  rw [list_sum_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hg (i : ℕ) : eval f (r.getD i []) = (r.map (eval f)).getD i 0 := by
    simpa only [eval_nil] using (List.getD_map r [] (n := i) (eval f)).symm
  simp only [hg]
  rw [sum_getD n _ (by simpa only [List.length_map] using h r hr), eval_flatten]

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.NuclearUltrapower.SOS.eval_buckets_oai.{u_1, u_2} := @OAI.NuclearUltrapower.SOS.eval_buckets_oai.{u_1, u_2}
