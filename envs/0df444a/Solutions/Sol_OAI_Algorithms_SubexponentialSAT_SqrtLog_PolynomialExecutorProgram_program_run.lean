-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:31:32.656452+00:00
-- url     : https://prove2.me/submissions/1f4a7a0a-2e91-4494-b309-bb240e728af7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_add_implements
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_load_implements
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_mul_implements
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpRowPostfixInterpreter_global_complete_runsIn

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

theorem evaluate_eq {C : Type*} (ops : RingProgram C) (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List C)) :
    letI : Add (List C) := ⟨addValue ops⟩
    letI : Mul (List C) := ⟨mulValue ops J⟩
    evaluate ops J e = (e.map (loadValue ops J)).eval := by
  let _ : Add (List C) := ⟨addValue ops⟩
  let _ : Mul (List C) := ⟨mulValue ops J⟩
  induction e with
  | lit P => rfl
  | add e f he hf => exact congrArg₂ (addValue ops) he hf
  | mul e f he hf => exact congrArg₂ (mulValue ops J) he hf

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-sensitive costs and validity of the generic coefficient-array
interpreter, independently of its native arithmetic implementation. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT

theorem executionCost_eq {B d : ℕ}
    (ops : SubexpSymbolicCost.RingProgram (Coeff B d)) (J Ka Km : ℕ)
    (e : Algorithm.Expr (List (Coeff B d))) :
    letI : Add (List (Coeff B d)) := ⟨addValue ops⟩
    letI : Mul (List (Coeff B d)) := ⟨mulValue ops J⟩
    SubexpProjectedInterpreter.exprCost DensePolynomialProgram.encode (fun _ _ => Ka)
      (fun _ _ => Km) (loadValue ops J) (loadBound B d J) e =
      executionCost Ka Km (J*(d*B)) e := by
  let _ : Add (List (Coeff B d)) := ⟨addValue ops⟩
  let _ : Mul (List (Coeff B d)) := ⟨mulValue ops J⟩
  induction e with
  | lit P => simp only [SubexpProjectedInterpreter.exprCost,loadBound,executionCost]; omega
  | add e f he hf => simp only [SubexpProjectedInterpreter.exprCost,executionCost,he,hf]; omega
  | mul e f he hf => simp only [SubexpProjectedInterpreter.exprCost,executionCost,he,hf]; omega

theorem validity {C : Type*} (ops : SubexpSymbolicCost.RingProgram C) (J : ℕ) :
    letI : Add (List C) := ⟨addValue ops⟩
    letI : Mul (List C) := ⟨mulValue ops J⟩
    SubexpProjectedInterpreter.Validity (fun P : List C => P.length = J) (loadValue ops J) := by
  let _ : Add (List C) := ⟨addValue ops⟩
  let _ : Mul (List C) := ⟨mulValue ops J⟩
  constructor
  · exact SubexpDensePaddingSpec.padCells_length ops.zeroRun.1 J
  · intro P Q hP hQ
    change (SubexpDensePolynomial.addProgram ops P Q).1.length = J
    rw [SubexpPolynomialAddService.addProgram_length,hP,hQ,Nat.max_self]
  · intro P Q _ _
    exact DensePolynomialProgram.result_length ops J P Q

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native interpreter for raw row-polynomial postfix source.
All literal padding and coefficient-array arithmetic are included. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg)

/-- The output is computed from the supplied source expression by native
operations. No evaluated polynomial is supplied as an input or premise. -/
theorem program_run_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false)
    (e : Algorithm.Expr (List (Coeff (baseWidth p t) d))) :
    RunsIn program (executionCost (addCost (baseWidth p t) d J) (mulCost (baseWidth p t) d J)
        (J*(d*baseWidth p t)) e + 5)
      (physicalCfg (some program.entry) false false false
        (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] [] context)
      (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [evaluate ops J e])
        (Encoding.encodeList DensePolynomialProgram.encode [evaluate ops J e]) context) := by
  let _ : Add (List (Coeff (baseWidth p t) d)) := ⟨addValue ops⟩
  let _ : Mul (List (Coeff (baseWidth p t) d)) := ⟨mulValue ops J⟩
  have h := SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn addProgram mulProgram
    SubexpDenseLiteralPadding.program DensePolynomialProgram.encode (loadValue ops J)
    (fun P : List (Coeff (baseWidth p t) d) => P.length = J)
    (fun _ _ => addCost (baseWidth p t) d J) (fun _ _ => mulCost (baseWidth p t) d J)
    (loadBound (baseWidth p t) d J) context
    (add_implements p t M cache ops table J width frame context H hB hadd)
    (mul_implements p t M cache ops table J width frame context H hB hz hadd hmul)
    (load_implements p t M cache ops table J width frame context H hzero)
    (validity ops J) e
  simpa only [program,executionCost_eq,← evaluate_eq ops J e] using h

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.program_run_oai
