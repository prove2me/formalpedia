-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.writeRow_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:39:20.418046+00:00
-- url     : https://prove2.me/submissions/cab51eab-7c97-44c5-a6eb-8dd1c6d541dd

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S118

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramSelectFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed framing primitive for the scored-record writer. It consumes the
input bits and prepends the frame of their reversal to the output stack. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem frameBody_eval (b : Bool) (bs out : List Bool) :
    Eval frameBody 3 (framePopped (b::bs) out) (framePopped bs (true::b::out)) := by
  let d := framePopped (b::bs) out
  let d1 := (StructuredProgram.Atom.push (1 : Fin 2) (0 : Fin 3)).eval d
  let d2 := (StructuredProgram.Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  have h1 := Eval.base (StructuredProgram.Eval.atom (.push 1 0) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.push 1 2) d1)
  have h3 := Eval.base (StructuredProgram.Eval.atom (.pop 0 0 1) d2)
  convert h1.seq (h2.seq h3) using 1
  all_goals try with_reducible_and_instances rfl
  cases bs <;>
    simp [d2,d1,d,framePopped,frameState,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs] <;>
    all_goals first | (constructor <;> funext i <;> fin_cases i <;> simp) | (funext i <;> fin_cases i <;> simp)

theorem frameLoop_eval (bits out : List Bool) :
    Eval frameLoop (4*bits.length+1) (framePopped bits out)
      (frameState false false [] (frameOutput bits out)) := by
  induction bits generalizing out with
  | nil => exact Eval.while_false rfl
  | cons b bs ih =>
    have h := Eval.while_true (show (framePopped (b::bs) out).regs 1 = true from rfl)
      (frameBody_eval b bs out) (ih (true::b::out))
    convert h using 1 <;>
      simp [frameOutput,List.reverse_cons,List.flatMap_append,List.append_assoc] ; omega

theorem frameOutput_frame (bits out : List Bool) :
    frameOutput bits (false::out) = Encoding.frame bits.reverse ++ out := by
  have h (xs : List Bool) :
      xs.flatMap (fun b => [true,b]) ++ (false::out) = Encoding.frame xs ++ out := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [Encoding.frame] using congrArg (fun ys => true::x::ys) ih
  exact h bits.reverse

theorem frameCommand_eval (regs : Fin 3 → Bool) (bits out : List Bool) :
    Eval frameCommand (4*bits.length+5) ⟨regs,![bits,out]⟩
      (frameState false false [] (Encoding.frame bits.reverse ++ out)) := by
  let d : FrameData := ⟨regs,![bits,out]⟩
  let d1 := (StructuredProgram.Atom.set (2 : Fin 3) false).eval d
  let d2 := (StructuredProgram.Atom.push (1 : Fin 2) (2 : Fin 3)).eval d1
  let d3 := (StructuredProgram.Atom.set (2 : Fin 3) true).eval d2
  let d4 := (StructuredProgram.Atom.pop (0 : Fin 2) (0 : Fin 3) 1).eval d3
  have hd4 : d4 = framePopped bits (false::out) := by
    cases bits <;>
      simp [d4,d3,d2,d1,d,framePopped,frameState,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs] <;>
    all_goals first | (constructor <;> funext i <;> fin_cases i <;> simp) | (funext i <;> fin_cases i <;> simp)
  have hl := frameLoop_eval bits (false::out)
  rw [frameOutput_frame, ←hd4] at hl
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set 2 false) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.push 1 2) d1)
  have h3 := Eval.base (StructuredProgram.Eval.atom (.set 2 true) d2)
  have h4 := Eval.base (StructuredProgram.Eval.atom (.pop 0 0 1) d3)
  convert h1.seq (h2.seq (h3.seq (h4.seq hl))) using 1 ; omega

theorem frameProgram_trace (regs : Fin 3 → Bool) (bits out : List Bool) :
    Trace frameProgram (4*bits.length+6)
      ((⟨regs,![bits,out]⟩ : FrameData).withPC (some frameProgram.entry))
      ((frameState false false [] (Encoding.frame bits.reverse ++ out)).withPC none) := by
  convert compiled_halt_trace (frameCommand_eval regs bits out) 0 1 using 1
  all_goals try with_reducible_and_instances rfl

end SubexponentialSAT.SqrtLog.RowSelectionProgramSelect

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

theorem push_eval (dst : Fin 64) (b : Bool) (d : Data) :
    Eval (push dst b) 2 d (pushed dst b d) :=
  Subexp.TupleProgram.pushConst_eval dst 0 b d

theorem pushed_register (dst : Fin 64) (b : Bool) (d : Data) (i : Fin 16)
    (hi : 1 ≤ i.val) : (pushed dst b d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  simp [pushed,h0]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramWrite
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem low3_injective : Function.Injective low3 := Fin.castAdd_injective _ _
theorem frameStacks_injective : Function.Injective frameStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [frameStacks]

theorem writeRow_eval_oai (d : Data) :
    ∃ rf, Eval writeRow (4*(d.stacks 13).length+8) d
      ⟨rf,Function.update (Function.update d.stacks 13 []) 12
        (true::(Encoding.frame (d.stacks 13).reverse++d.stacks 12))⟩ ∧
      (∀ i : Fin 16, 3 ≤ i.val → rf i=d.regs i) := by
  let a : State 3 2 := ⟨d.regs ∘ low3,![d.stacks 13,d.stacks 12]⟩
  let b := RowSelectionProgramSelect.frameState false false []
    (Encoding.frame (d.stacks 13).reverse++d.stacks 12)
  let rr := Function.extend low3 b.regs d.regs
  let mid : Data := ⟨rr,Function.update (Function.update d.stacks 13 []) 12
    (Encoding.frame (d.stacks 13).reverse++d.stacks 12)⟩
  have hin : embedState low3 frameStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low3_injective frameStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hout : embedState low3 frameStacks d b=mid := by
    apply embedState_eq_of_ports _ _ _ _ _ low3_injective frameStacks_injective
    · intro i; exact low3_injective.extend_apply b.regs d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [mid,b,frameStacks]
    · intro i hi
      have h13 : i≠13 := fun h => hi ⟨0,by simpa [frameStacks] using h.symm⟩
      have h12 : i≠12 := fun h => hi ⟨1,by simpa [frameStacks] using h.symm⟩
      simp [mid,h13,h12]
  have he := eval_call_lifted RowSelectionProgramSelect.frameProgram low3 frameStacks d
    low3_injective frameStacks_injective
    (RowSelectionProgramSelect.frameProgram_trace (d.regs ∘ low3) (d.stacks 13) (d.stacks 12))
  change Eval (.call (ProgramLinking.liftProgram RowSelectionProgramSelect.frameProgram low3 frameStacks))
    (4*(d.stacks 13).length+6) (embedState low3 frameStacks d a) (embedState low3 frameStacks d b) at he
  rw [hin,hout] at he
  have hp := push_eval 12 true mid
  refine ⟨(pushed 12 true mid).regs,?_,?_⟩
  · convert he.seq hp using 1 ; simp [pushed, mid]
  · intro i hi
    rw [pushed_register 12 true mid i (by omega)]
    change Function.extend low3 b.regs d.regs i=d.regs i
    apply Function.extend_apply'
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hjlt := j.isLt
    dsimp [low3] at hv
    omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.writeRow_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.writeRow_eval_oai
