-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.initialize_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:34:07.571934+00:00
-- url     : https://prove2.me/submissions/edd7c3e2-26f9-4260-871a-63f7ecaf7896

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_eval (src dst : Fin 64) (d : Data)
    (hsd : src≠dst) (hst : src≠24) (htd : (24 : Fin 64)≠dst)
    (htmp : d.stacks 24=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  Subexp.TupleProgram.copy_eval src dst 24 0 1 hsd hst htd (by decide) d htmp

theorem push_eval (dst : Fin 64) (b : Bool) (d : Data) :
    Eval (push dst b) 2 d (pushed dst b d) :=
  Subexp.TupleProgram.pushConst_eval dst 0 b d

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularArithmetic

private theorem padTo_empty (xs : List Bool) : padTo xs []=List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [padTo,List.replicate_succ] using congrArg (List.cons false) ih

private theorem zeroVertexStacks_injective : Function.Injective zeroVertexStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [zeroVertexStacks]

theorem zeroVertex_eval (d : Data) (h2 : d.stacks 2=[]) (h26 : d.stacks 26=[]) :
    ∃ rf, Eval (.call (ProgramLinking.liftProgram paddingProgram low8 zeroVertexStacks))
      (4*(d.stacks 25).length+3) d
      ⟨rf,Function.update (Function.update d.stacks 25 []) 2
        (List.replicate (d.stacks 25).length false)⟩ := by
  obtain ⟨rr,ht⟩ := SubexponentialSAT.SubexpDenseLiteralPadding.padding_trace_any (d.regs ∘ low8)
    (d.stacks 25) [] []
  let a : State 8 3 := ⟨d.regs ∘ low8,operandStacks (d.stacks 25) [] []⟩
  let b : State 8 3 := ⟨rr,operandStacks [] [] (List.replicate (d.stacks 25).length false)⟩
  let rf := Function.extend low8 rr d.regs
  have hin : embedState low8 zeroVertexStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective zeroVertexStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> simp [a,zeroVertexStacks,operandStacks,h2,h26]
    · intro i hi; rfl
  have hout : embedState low8 zeroVertexStacks d b=
      (⟨rf,Function.update (Function.update d.stacks 25 []) 2
        (List.replicate (d.stacks 25).length false)⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective zeroVertexStacks_injective
    · intro i; exact low8_injective.extend_apply rr d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [b,zeroVertexStacks,operandStacks,h26]
    · intro i hi
      have h25 : i≠25 := fun h => hi ⟨0,by simpa [zeroVertexStacks] using h.symm⟩
      have h2i : i≠2 := fun h => hi ⟨2,by simpa [zeroVertexStacks] using h.symm⟩
      simp [h25,h2i]
  have ht' : Trace paddingProgram (4*(d.stacks 25).length+3)
      (a.withPC (some paddingProgram.entry)) (b.withPC none) := by
    simpa [a,b,paddingCfg,StructuredProgram.State.withPC,padTo_empty] using ht
  have he := eval_call_lifted paddingProgram low8 zeroVertexStacks d
    low8_injective zeroVertexStacks_injective ht'
  exact ⟨rf,by simpa only [hin,hout] using he⟩

theorem initialize_eval_oai (d : Data) (h2 : d.stacks 2=[]) (h12 : d.stacks 12=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h26 : d.stacks 26=[]) :
    ∃ rf, Eval initializeCommand (11*(d.stacks 11).length+10) d ⟨rf,initialStacks d⟩ := by
  have hp := push_eval 12 false d
  let d0 := pushed 12 false d
  have hc := copy_eval 11 25 d0 (by decide) (by decide) (by decide)
    (by simpa [d0,pushed] using h24)
  let d1 := copied 11 25 d0
  obtain ⟨rf,he⟩ := zeroVertex_eval d1
    (by simpa [d1,d0,copied,StackRoutines.copyStacks,pushed] using h2)
    (by simpa [d1,d0,copied,StackRoutines.copyStacks,pushed] using h26)
  refine ⟨rf,?_⟩
  convert hp.seq (hc.seq he) using 1
  · simp [d1,d0,copied,StackRoutines.copyStacks,pushed,h25] ; omega
  · apply congrArg (StructuredProgram.State.mk rf)
    funext i
    by_cases h25i : i=25
    · subst i; simp [d1,d0,copied,StackRoutines.copyStacks,pushed,initialStacks,h25]
    · by_cases h2i : i=2
      · subst i
        simp [d1,d0,copied,StackRoutines.copyStacks,pushed,initialStacks,h25,h12]
      · simp [d1,d0,copied,StackRoutines.copyStacks,pushed,initialStacks,h25,h12,h25i,h2i]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.initialize_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.initialize_eval_oai
