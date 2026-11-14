-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.residual_eval_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:54:18.791202+00:00
-- url     : https://prove2.me/submissions/1a97ca66-d17c-4b2b-8f01-b30588a8dc0a

import Mathlib
import Definitions.Def_OAIQ229C031
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_buckets_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_length_bound_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_normalizations_ca

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
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {A : Type*} [AddCommGroup A]

theorem residual_eval_ca_oai (f : Mat3 → A) : eval f residual = eval f residualRows.flatten := by
  change eval f ((List.range 128).flatMap residualBucket) = _
  unfold residualBucket
  rw [eval_buckets_ca 128 allRowBuckets row_length_bound_ca]
  have he := congrArg (fun ps : List (Poly Mat3) => (ps.map (eval f)).sum) row_normalizations_ca
  simp only [List.map_map, Function.comp_def, eval_normalize] at he
  simpa only [eval_flatMap, eval_flatten] using he.symm

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.residual_eval_ca_oai.{u_1} := @OAI.NuclearUltrapower.SOS.residual_eval_ca_oai.{u_1}
