-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:07:49.05634+00:00
-- url     : https://prove2.me/submissions/654b8f9d-1c68-4b36-af36-4abd7fd31609

import Mathlib
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_evaluate_correct

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable coefficient-array meaning of the row postfix interpreter.
Literal padding and all arithmetic operate on stored coefficient words. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT.SubexpSymbolicCost

/-- No degree restriction on intermediate expressions is required. The final
row degree bound alone restores the complete polynomial. -/
theorem evaluate_full_oai {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (J : ℕ) (e : SubexponentialSAT.Algorithm.Expr (List C))
    (hdegree : ((e.map (meaning ops)).eval).natDegree < J) :
    meaning ops (evaluate ops.program J e) = (e.map (meaning ops)).eval := by
  rw [(evaluate_correct ops J e).2]
  ext i
  rw [SubexponentialSAT.Truncation.coeff_trunc]
  split_ifs with hi
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (by omega))).symm

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full_oai.{u_1, u_2}
