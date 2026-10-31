-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.model_flat_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:30:39.103948+00:00
-- url     : https://prove2.me/submissions/201486fa-3b60-4eff-9914-fad5ef6a220d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_evaluate_correct
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_flat_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_program_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact zero bytes for the native padded-polynomial constructors. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem toNat_false (n : ℕ) :
    SubexponentialSAT.BinaryArithmetic.toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem zero_cache_bits (p t : ℕ) [Fact p.Prime] (cache : RingProgram.ScalarCache p t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t) :
    cache.zero.val = List.replicate (baseWidth p t) false := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [cache.zero.property]
  · have hv := congrArg ZMod.val cache.zero_correct
    have hnum : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val = 0 := by
      simpa only [wordValue,ZMod.val_natCast,Nat.mod_eq_of_lt hz,ZMod.val_zero] using hv
    rw [hnum,toNat_false]

private theorem flatten_replicate_false (d B : ℕ) :
    (List.replicate d (List.replicate B false)).flatten = List.replicate (d*B) false := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]
      congr 1
      ring

theorem flat_constant_zero {B : ℕ} (z : Word B)
    (hz : z.val = List.replicate B false) (d : ℕ) :
    RingProgram.flat (fun _ : Fin d => z) = List.replicate (d*B) false := by
  simp only [RingProgram.flat,hz,List.ofFn_const]
  exact flatten_replicate_false d B

theorem model_zero_bits (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t) :
    RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1 =
      List.replicate (d*baseWidth 3 t) false := by
  change RingProgram.flat (fun _ : Fin d => cache.zero) = _
  exact flat_constant_zero cache.zero (zero_cache_bits 3 t cache hz) d

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dense-polynomial arithmetic with arbitrary runtime ring
coefficient width. Native ring multiplication and every convolution scan are
included in the cost, and the output has the usual polynomial meaning. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- An explicit polynomial upper bound for the fully native trace. -/
theorem nativeMulBudget_polynomial (J degree B : ℕ) :
    nativeMulBudget J degree B ≤ 100000 * (J+1)^3 * (degree+1)^3 * (B+1)^2 := by
  unfold nativeMulBudget mulBudget convolutionBudget outerCost Pair.budget
    RingCall.budget RingScan.serviceMulBudget RingTriple.expandBudget Cell.eventBudget Cell.addBudget
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

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

theorem evaluate_length {C : Type*} (ops : RingProgram C) (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List C)) : (evaluate ops J e).length = J := by
  induction e with
  | lit P => exact SubexponentialSAT.SubexpDensePaddingSpec.padCells_length _ _ _
  | add e f he hf =>
      change (SubexponentialSAT.SubexpDensePolynomial.addProgram ops (evaluate ops J e) (evaluate ops J f)).1.length = J
      rw [SubexponentialSAT.SubexpPolynomialAddService.addProgram_length, he, hf, Nat.max_self]
  | mul e f he hf => exact DensePolynomialProgram.result_length ops J _ _

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

theorem executionCost_polynomial {B d : ℕ} (Ka Km W : ℕ)
    (e : Algorithm.Expr (List (Coeff B d))) :
    executionCost Ka Km W e ≤ (e.size + literalBytes e) * (Ka+Km+16*W+100) := by
  induction e with
  | lit P => simp only [executionCost,Algorithm.Expr.size,literalBytes]; nlinarith
  | add e f he hf =>
      simp only [executionCost,Algorithm.Expr.size,literalBytes]
      nlinarith
  | mul e f he hf =>
      simp only [executionCost,Algorithm.Expr.size,literalBytes]
      nlinarith

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bit bounds for the fixed source interpreter. Source size and
raw literal bytes are charged separately from the retained coefficient count. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

theorem callbackCost_polynomial (B d J : ℕ) :
    addCost B d J + mulCost B d J + 16*(J*(d*B)) + 100 ≤
      300000*(J+1)^3*(d+1)^3*(B+1)^2 := by
  have hm := DensePolynomialProgram.nativeMulBudget_polynomial J d B
  unfold addCost mulCost binaryBound DensePolynomialProgram.AddService.budget
  ring_nf at *
  omega

theorem executionCost_native_polynomial {B d : ℕ} (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List (Coeff B d))) :
    executionCost (addCost B d J) (mulCost B d J) (J*(d*B)) e + 5 ≤ totalBudget J e := by
  have h := (executionCost_polynomial (addCost B d J) (mulCost B d J) (J*(d*B)) e).trans
    (Nat.mul_le_mul_left _ (callbackCost_polynomial B d J))
  let A := e.size + literalBytes e
  let C := 300000*(J+1)^3*(d+1)^3*(B+1)^2
  change executionCost (addCost B d J) (mulCost B d J) (J*(d*B)) e ≤ A*C at h
  have hC : 5 ≤ C := by
    let P := (J+1)^3*(d+1)^3*(B+1)^2
    have hP : 0 < P := by dsimp [P]; positivity
    have he : C = 300000*P := by dsimp [C,P]; ring
    rw [he]
    omega
  calc
    executionCost (addCost B d J) (mulCost B d J) (J*(d*B)) e + 5 ≤ A*C+C :=
      Nat.add_le_add h hC
    _ = (A+1)*C := by simpa only [Nat.one_mul] using (Nat.add_mul A 1 C).symm
    _ = totalBudget J e := by dsimp [A,C,totalBudget]; ring


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual arbitrary-degree RingModel semantics, with no supplied arithmetic
oracle and no supplied value of the input source expression. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg)

/-- The fixed interpreter reads source instructions, performs native arithmetic,
and leaves a framed coefficient array with the exact truncated meaning. -/
theorem model_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame context)
    (e : Algorithm.Expr (List (Coeff (baseWidth 3 t) d))) :
    ∃ out : List (Coeff (baseWidth 3 t) d),
      RunsIn program (totalBudget J e)
        (physicalCfg (some program.entry) false false false
          (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] [] context)
        (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
          (Encoding.encodeList DensePolynomialProgram.encode [out]) context) ∧
      out.length = J ∧
      meaning (RingProgram.modelRing t ht hd a M cache) out =
        Truncation.trunc J ((e.map (meaning (RingProgram.modelRing t ht hd a M cache))).eval) := by
  let ops := RingProgram.modelProgram t a M cache
  have he := program_run 3 t M cache ops (HornerProgram.modelTable t a M cache) J width frame context H
    (by rw [RingProgram.ternary_baseWidth]; omega) hz (fun _ _ => rfl) (fun _ _ => rfl)
    (DensePolynomialProgram.model_zero_bits t a M cache hz) e
  refine ⟨evaluate ops J e, he.mono (executionCost_native_polynomial J e), ?_, ?_⟩
  · exact evaluate_length ops J e
  · exact (evaluate_correct (RingProgram.modelRing t ht hd a M cache) J e).2

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete native source interpreter returns an ordinary flat
coefficient array on240, ready for the perturbation producer. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore )

/-- The actual RingModel interpreter has a plain, source-derived output array.
The runtime array length remains available in protected cache193. -/
theorem model_flat_run_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame context)
    (e : Algorithm.Expr (List (Coeff (baseWidth 3 t) d))) :
    ∃ (out : List (Coeff (baseWidth 3 t) d)) (rf : Fin 16 → Bool),
      RunsIn flatProgram (totalBudget J e+18*(J*(d*baseWidth 3 t))+28)
        (physicalCfg (some flatProgram.entry) false false false
          (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] [] context)
        ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none) ∧
      out.length = J ∧
      meaning (RingProgram.modelRing t ht hd a M cache) out =
        Truncation.trunc J ((e.map (meaning (RingProgram.modelRing t ht hd a M cache))).eval) := by
  obtain ⟨out,hr,hl,hv⟩ := model_run t ht hd a M cache hz J width frame context H e
  obtain ⟨rf,hf⟩ := flat_run context _ out _ H.empty21 H.arithmetic.scratch H.empty240 hr
  refine ⟨out,rf,?_,hl,hv⟩
  simpa only [DensePolynomialProgram.encode_length,hl] using hf

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.model_flat_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.model_flat_run_oai
