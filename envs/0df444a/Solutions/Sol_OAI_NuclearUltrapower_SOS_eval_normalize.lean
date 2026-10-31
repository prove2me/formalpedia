-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.eval_normalize
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:04:34.885581+00:00
-- url     : https://prove2.me/submissions/6f164d42-3a08-4b43-8ad6-7329a094236e

import Mathlib
import Definitions.Def_OAIQ019N047

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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
theorem eval_normalize_oai (f : α → A) (le : α → α → Bool) (ps : Poly α) :
    eval f (normalize le ps) = eval f ps := by
  rw [normalize, eval_compress]
  exact List.Perm.sum_eq ((List.perm_insertionSort _ ps).map _)

end Evaluation

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.NuclearUltrapower.SOS.eval_normalize_oai.{u_1, u_2} := @OAI.NuclearUltrapower.SOS.eval_normalize_oai.{u_1, u_2}
