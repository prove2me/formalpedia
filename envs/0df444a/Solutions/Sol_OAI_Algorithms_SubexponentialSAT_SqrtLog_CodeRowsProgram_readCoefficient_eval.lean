-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:36:58.686083+00:00
-- url     : https://prove2.me/submissions/8b7c9bda-1d83-4052-8573-1b5693a70c67

import Mathlib
import Definitions.Def_OAIQ081S118

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native five-pop decoder for the scalar frames emitted by code search.
It consumes one frame and exposes its two little-endian scalar bits. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (regs : Fin 4 → Bool) (a b : Bool) (tail : List Bool) :
    Eval command 5 (state regs (frame a b++tail)) (state ![false,true,a,b] tail) := by
  let d := state regs (frame a b++tail)
  let d1 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d
  let d2 := (StructuredProgram.Atom.pop (0 : Fin 1) (2 : Fin 4) 1).eval d1
  let d3 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d2
  let d4 := (StructuredProgram.Atom.pop (0 : Fin 1) (3 : Fin 4) 1).eval d3
  let d5 := (StructuredProgram.Atom.pop (0 : Fin 1) (0 : Fin 4) 1).eval d4
  have h : Eval command 5 d d5 :=
    (Eval.base (.atom (.pop 0 0 1) d)).seq
      ((Eval.base (.atom (.pop 0 2 1) d1)).seq
        ((Eval.base (.atom (.pop 0 0 1) d2)).seq
          ((Eval.base (.atom (.pop 0 3 1) d3)).seq (Eval.base (.atom (.pop 0 0 1) d4)))))
  have he : d5=state ![false,true,a,b] tail := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [d4,d3,d2,d1,d,state,frame,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
    · funext i
      fin_cases i ; simp [d4,d3,d2,d1,d,state,frame,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr,readRegs]
  exact he ▸ h

theorem program_trace (regs : Fin 4 → Bool) (a b : Bool) (tail : List Bool) :
    Trace program 6 ((state regs (frame a b++tail)).withPC (some program.entry))
      ((state ![false,true,a,b] tail).withPC none) :=
  compiled_halt_trace (command_eval regs a b tail) 0 0

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem cellRegisters_injective : Function.Injective cellRegisters := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cellRegisters]

theorem cellStacks_injective : Function.Injective cellStacks := by
  intro i j h
  fin_cases i; fin_cases j; rfl

theorem readCoefficient_eval_oai (d : Data) (a b : Bool) (tail : List Bool)
    (hs : d.stacks 0=Cell.frame a b++tail) :
    Eval readCoefficient 6 d
      ⟨coefficientRegs d.regs a b,Function.update d.stacks 0 tail⟩ := by
  have hp : projectState cellRegisters cellStacks d=
      Cell.state (d.regs ∘ cellRegisters) (Cell.frame a b++tail) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i; exact hs
  have ht := Cell.program_trace (d.regs ∘ cellRegisters) a b tail
  rw [←hp] at ht
  have he := eval_call_from_state Cell.program cellRegisters cellStacks d
    cellRegisters_injective cellStacks_injective ht
  have hf : embedState cellRegisters cellStacks d (Cell.state ![false,true,a,b] tail)=
      (⟨coefficientRegs d.regs a b,Function.update d.stacks 0 tail⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ cellRegisters_injective cellStacks_injective
    · intro i; fin_cases i <;> simp [cellRegisters,coefficientRegs,Cell.state]
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellRegisters] using h.symm⟩
      have h1 : i≠1 := fun h => hi ⟨1,by simpa [cellRegisters] using h.symm⟩
      have h8 : i≠8 := fun h => hi ⟨2,by simpa [cellRegisters] using h.symm⟩
      have h9 : i≠9 := fun h => hi ⟨3,by simpa [cellRegisters] using h.symm⟩
      simp [coefficientRegs,h0,h1,h8,h9]
    · intro i; fin_cases i; simp [cellStacks,Cell.state]
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellStacks] using h.symm⟩
      simp [h0]
  simpa only [hf] using he

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.readCoefficient_eval_oai
