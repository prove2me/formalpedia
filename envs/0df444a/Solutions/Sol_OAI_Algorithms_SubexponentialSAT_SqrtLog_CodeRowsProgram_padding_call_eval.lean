-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.padding_call_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:35:04.72418+00:00
-- url     : https://prove2.me/submissions/bbfa530a-c2a6-4c8f-85f5-c34c6a98f2ce

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code ExecutesIn)

theorem padding_exit_any (regs : Fin 8 → Bool) (input output : List Bool) :
    Trace paddingProgram 3 (paddingCfg (some 0) regs [] input output)
      (paddingCfg none (readRegs regs 1 3 none) [] input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, operandStacks, Function.update_apply]

theorem padding_trace_any (regs : Fin 8 → Bool) (shape input output : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none rf [] (input.drop shape.length) ((padTo shape input).reverse ++ output)) := by
  induction shape generalizing regs input output with
  | nil =>
      refine ⟨readRegs regs 1 3 none, ?_⟩
      simpa [padTo] using padding_exit_any regs input output
  | cons bit shape ih =>
      obtain ⟨rf, ht⟩ := ih (paddingRegs regs bit input) input.tail
        (input.head?.getD false :: output)
      refine ⟨rf, ?_⟩
      have h := (padding_round regs bit shape input output).trans ht
      cases input <;> convert h using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] <;> omega

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls SubexponentialSAT.BinaryArithmetic

theorem low8_injective : Function.Injective low8 := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Appending fixed-width slot words does not require pre-normalized arithmetic
outputs. The physical padding loop drops high zeros and the caller clears any
unconsumed suffix, with both costs explicit. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms

theorem padTo_value_of_lt (shape xs : List Bool) (h : BinaryArithmetic.toNat xs < 2^shape.length) :
    BinaryArithmetic.toNat (padTo shape xs)=BinaryArithmetic.toNat xs := by
  induction shape generalizing xs with
  | nil => simp only [List.length_nil,pow_zero] at h; simp [padTo]; omega
  | cons a shape ih =>
    cases xs with
    | nil =>
      simp only [padTo,toNat_cons,bitVal_false,zero_add,toNat_nil]
      have hz := ih [] (by simp)
      simpa using hz
    | cons b xs =>
      have hx : BinaryArithmetic.toNat xs < 2^shape.length := by
        simp only [toNat_cons,List.length_cons,pow_succ] at h
        omega
      simp only [padTo,toNat_cons,ih xs hx]

theorem padTo_fixedBits (shape xs : List Bool) (h : BinaryArithmetic.toNat xs < 2^shape.length) :
    padTo shape xs=SubexpLiftRing.fixedBits shape.length (BinaryArithmetic.toNat xs) := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [padTo_length]
  · rw [padTo_value_of_lt shape xs h,SubexpLiftRing.toNat_fixedBits_of_lt _ _ h]

theorem appendWord_trace (regs : Fin 8 → Bool) (shape xs acc : List Bool)
    (h : BinaryArithmetic.toNat xs < 2^shape.length) :
    ∃ rf, Trace paddingProgram (4*shape.length+3)
      (paddingCfg (some 0) regs shape xs acc)
      (paddingCfg none rf [] (xs.drop shape.length)
        ((SubexpLiftRing.fixedBits shape.length (BinaryArithmetic.toNat xs)).reverse++acc)) := by
  obtain ⟨rf,ht⟩ := SubexpDenseLiteralPadding.padding_trace_any regs shape xs acc
  exact ⟨rf,by simpa only [padTo_fixedBits shape xs h] using ht⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPaddingCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularPrograms

theorem paddingStacks_injective : Function.Injective paddingStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [paddingStacks]

theorem padding_call_eval_oai (d : Data)
    (h : BinaryArithmetic.toNat (d.stacks 23) < 2^(d.stacks 25).length) :
    ∃ rf, Eval (.call (ProgramLinking.liftProgram paddingProgram low8 paddingStacks))
      (4*(d.stacks 25).length+3) d ⟨rf,paddedStacks d⟩ ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  obtain ⟨rr,ht⟩ := appendWord_trace (d.regs ∘ low8) (d.stacks 25)
    (d.stacks 23) (d.stacks 13) h
  let a : State 8 3 := ⟨d.regs ∘ low8,operandStacks (d.stacks 25) (d.stacks 23) (d.stacks 13)⟩
  let b : State 8 3 := ⟨rr,operandStacks [] ((d.stacks 23).drop (d.stacks 25).length)
    ((SubexpLiftRing.fixedBits (d.stacks 25).length (BinaryArithmetic.toNat (d.stacks 23))).reverse++d.stacks 13)⟩
  have hin : embedState low8 paddingStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective paddingStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> simp [a,paddingStacks,operandStacks]
    · intro i hi; rfl
  let rf := Function.extend low8 rr d.regs
  have hout : embedState low8 paddingStacks d b=⟨rf,paddedStacks d⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective paddingStacks_injective
    · intro i; exact low8_injective.extend_apply rr d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [paddedStacks,b,paddingStacks,operandStacks]
    · intro i hi
      have h25 : i≠25 := fun h => hi ⟨0,by simpa [paddingStacks] using h.symm⟩
      have h23 : i≠23 := fun h => hi ⟨1,by simpa [paddingStacks] using h.symm⟩
      have h13 : i≠13 := fun h => hi ⟨2,by simpa [paddingStacks] using h.symm⟩
      simp [paddedStacks,h25,h23,h13]
  have ht' : Trace paddingProgram (4*(d.stacks 25).length+3)
      (a.withPC (some paddingProgram.entry)) (b.withPC none) := by
    simpa [a,b,paddingCfg,StructuredProgram.State.withPC] using ht
  have he := eval_call_lifted paddingProgram low8 paddingStacks d
    low8_injective paddingStacks_injective ht'
  refine ⟨rf,by simpa only [hin,hout] using he,?_⟩
  intro i hi
  apply Function.extend_apply'
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  have hjlt := j.isLt
  dsimp [low8] at hh
  omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.padding_call_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.padding_call_eval_oai
