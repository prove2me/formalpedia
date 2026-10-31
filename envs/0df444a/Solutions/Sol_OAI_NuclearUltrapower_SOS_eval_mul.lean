-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.eval_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:58:47.735147+00:00
-- url     : https://prove2.me/submissions/240d3622-7184-4896-81e1-4dac4f6336cd

import Mathlib
import Definitions.Def_OAIQ019N047

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
variable {α A : Type*} [DecidableEq α]

section EvalOperations
variable [Ring A]

omit [DecidableEq α] in
theorem eval_mul_oai (f : α → A) (μ : α → α → α) (ps qs : Poly α)
    (h : ∀ p ∈ ps, ∀ q ∈ qs, f (μ p.1 q.1) = f p.1 * f q.1) :
    eval f (ps.flatMap (fun p => qs.map (fun q => (μ p.1 q.1, p.2*q.2)))) =
      eval f ps * eval f qs := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hrow : eval f (qs.map (fun q => (μ p.1 q.1, p.2*q.2))) =
        (p.2 • f p.1) * eval f qs := by
      have hp := h p (by simp)
      clear h ih
      induction qs with
      | nil => simp
      | cons q qs ihq =>
        have hq := hp q (by simp)
        have hi := ihq (fun t ht => hp t (by simp [ht]))
        simp only [List.map_cons, eval_cons, hq, hi, mul_add]
        congr 1
        simp only [zsmul_eq_mul, Int.cast_mul, mul_assoc]
        rw [← mul_assoc (f p.1) (q.2 : A) (f q.1),
          ← (Int.cast_commute q.2 (f p.1)).eq, mul_assoc]
    simp only [List.flatMap_cons, eval_append, eval_cons, add_mul, hrow,
      ih (fun t ht q hq => h t (by simp [ht]) q hq)]
end EvalOperations
end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.NuclearUltrapower.SOS.eval_mul_oai.{u_1, u_2} := @OAI.NuclearUltrapower.SOS.eval_mul_oai.{u_1, u_2}
