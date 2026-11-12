-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.eval_buckets_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:33:12.553739+00:00
-- url     : https://prove2.me/submissions/1ab5036c-018c-433e-b560-d433edfc1d87

import Mathlib
import Definitions.Def_OAIQ229C012
import Definitions.Def_OAIQ229C015
import Theorems.Thm_OAI_NuclearUltrapower_SOS_list_sum_comm_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_sum_getD_ca

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.SOS.eval_append _root_.OAI.NuclearUltrapower.SOS.eval_flatMap _root_.OAI.NuclearUltrapower.SOS.eval_flatten
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

section Evaluation
variable [AddCommGroup A]

theorem eval_addHead (f : α → A) (p : α × ℤ) (ps : Poly α) :
    eval f (addHead p ps) = p.2 • f p.1 + eval f ps := by
  cases ps with
  | nil => simp [addHead]
  | cons q qs =>
    simp only [addHead]
    split_ifs with h
    · simp only [eval_cons, ← h, add_zsmul, add_assoc]
    · rfl

theorem eval_compress (f : α → A) (ps : Poly α) : eval f (compress ps) = eval f ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [compress, eval_addHead, ih, eval_cons]

/-- Sorting and collecting is a sound reflection procedure in any abelian group. -/
theorem eval_normalize (f : α → A) (le : α → α → Bool) (ps : Poly α) :
    eval f (normalize le ps) = eval f ps := by
  rw [normalize, eval_compress]
  exact List.Perm.sum_eq ((List.perm_insertionSort _ ps).map _)

end Evaluation

end NuclearUltrapower.SOS

end

end OAI
end

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
section BucketSemantics
variable {α A β γ : Type*} [DecidableEq α] [AddCommGroup A]

theorem eval_buckets_ca_oai (n : ℕ) (rs : List (List (Poly α)))
    (h : ∀ r ∈ rs, r.length ≤ n) (f : α → A) (le : α → α → Bool) :
    eval f ((List.range n).flatMap (fun b => normalize le (rs.flatMap (fun r => r.getD b [])))) =
      eval f (rs.flatMap List.flatten) := by
  simp only [eval_flatMap, eval_normalize]
  rw [list_sum_comm_ca]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hg (i : ℕ) : eval f (r.getD i []) = (r.map (eval f)).getD i 0 := by
    simpa only [eval_nil] using (List.getD_map r [] (n := i) (eval f)).symm
  simp only [hg]
  rw [sum_getD_ca n _ (by simpa only [List.length_map] using h r hr), eval_flatten]

end BucketSemantics
end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.NuclearUltrapower.SOS.eval_buckets_ca_oai.{u_1, u_2} := @OAI.NuclearUltrapower.SOS.eval_buckets_ca_oai.{u_1, u_2}
