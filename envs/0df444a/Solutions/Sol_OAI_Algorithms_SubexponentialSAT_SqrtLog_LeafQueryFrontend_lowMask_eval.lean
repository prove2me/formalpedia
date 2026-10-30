-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowMask_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:56:15.421226+00:00
-- url     : https://prove2.me/submissions/7a7bfcef-7257-4d14-a897-21382baf63f0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S130

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramLowMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit order conversion between the reverse high-incidence mask and the
forward low-variable mask consumed by head-identifier selection. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask
open SubexponentialSAT BitProgram StructuredCalls

theorem cycle (regs : Fin 2 → Bool) (b : Bool) (xs out : List Bool) :
    Trace program 5 ((state regs (b::xs) out).withPC (some 0))
      ((state (stepRegs regs b) xs ((!b)::out)).withPC (some 0)) := by
  refine .cons (b := (state (readRegs regs 0 1 (some b)) xs out).withPC (some 1)) ?_ ?_
  · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
  · refine .cons (b := (state (readRegs regs 0 1 (some b)) xs out).withPC (some 2)) ?_ ?_
    · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
    · cases b
      · refine .cons (b := (state (readRegs regs 0 1 (some false)) xs out).withPC (some 4)) ?_ ?_
        · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
        · refine .cons (b := (state (stepRegs regs false) xs out).withPC (some 5)) ?_ ?_
          · simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr]
          · refine .cons ?_ (.refl _)
            simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr,readRegs]
      · refine .cons (b := (state (readRegs regs 0 1 (some true)) xs out).withPC (some 3)) ?_ ?_
        · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
        · refine .cons (b := (state (stepRegs regs true) xs out).withPC (some 5)) ?_ ?_
          · simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr]
          · refine .cons ?_ (.refl _)
            simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr,readRegs]

theorem finish (regs : Fin 2 → Bool) (out : List Bool) :
    Trace program 3 ((state regs [] out).withPC (some 0))
      ((state (readRegs regs 0 1 none) [] out).withPC none) := by
  refine .cons (b := (state (readRegs regs 0 1 none) [] out).withPC (some 1)) ?_ ?_
  · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
  · refine .cons (b := (state (readRegs regs 0 1 none) [] out).withPC (some 6)) ?_ ?_
    · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
    · refine .cons ?_ (.refl _)
      simp [state,StructuredProgram.State.withPC,step,execInstr]

theorem trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    ∃ rf, Trace program (5*xs.length+3) ((state regs xs out).withPC (some program.entry))
      ((state rf [] ((xs.map (fun b => !b)).reverse++out)).withPC none) := by
  induction xs generalizing regs out with
  | nil => exact ⟨_,finish regs out⟩
  | cons b xs ih =>
      obtain ⟨rf,ht⟩ := ih (stepRegs regs b) ((!b)::out)
      have he := (cycle regs b xs out).trans ht
      refine ⟨rf,?_⟩
      convert he using 1 <;> simp [List.reverse_cons,List.append_assoc] ; omega

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem registers_injective (n : ℕ) (hn : n ≤ 40) : Function.Injective (registers n hn) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun z : Fin 40 => z.val) h

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies and fixed constants used between frontend stages. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem copy_eval (a : Data) (src dst : Fin 768) (h : CopyReady a src dst) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a (copied a src dst) :=
  SubexpScanPrimitives.copy_eval a src dst 679 0 1 h.1 h.2.1 h.2.2.1 (by decide) h.2.2.2

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem lowPorts_injective : Function.Injective lowPorts := by decide

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem lowMask_eval_oai (a : Data) (descending : List Bool)
    (h338 : a.stacks 338=descending) (h134 : a.stacks 134=[])
    (h668 : a.stacks 668=[]) (ht : a.stacks 679=[]) :
    ∃ b, Eval lowMask (12*descending.length+8) a b ∧
      b.stacks 134=descending.reverse.map Bool.not ∧ b.stacks 668=[] ∧
      (∀ i, i≠134 → i≠668 → b.stacks i=a.stacks i) ∧ b.regs 8=a.regs 8 := by
  have hc := copy_eval a 338 668 ⟨by decide,by decide,by decide,ht⟩
  let c := copied a 338 668
  have hp : projectState r2 lowPorts c=HeadIdentifierProgram.LowMask.state (c.regs ∘ r2) descending [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [lowPorts,c,copied_stack,h338,h134,h668]
  obtain ⟨rf,he⟩ := HeadIdentifierProgram.LowMask.trace (c.regs ∘ r2) descending []
  rw [←hp] at he
  let small := HeadIdentifierProgram.LowMask.state rf [] ((descending.map Bool.not).reverse)
  let b := embedState r2 lowPorts c small
  have hl := eval_call_from_state HeadIdentifierProgram.LowMask.program r2 lowPorts c
    (registers_injective ..) lowPorts_injective he
  have hf (i : Fin 768) (hi : i≠134) (hj : i≠668) : b.stacks i=a.stacks i := by
    have h := embedState_stack_frame r2 lowPorts c small i (by
      rintro ⟨j,hj'⟩; fin_cases j <;> simp [lowPorts] at hj' <;> simp_all)
    exact h.trans (by simp [c,copied_stack,hj])
  refine ⟨b,?_,?_,?_,hf,?_⟩
  · simpa [b,small,lowMask,lowCall,h338,show 7*descending.length+5+(5*descending.length+3)=12*descending.length+8 by omega] using hc.seq hl
  · have h := embedState_stack r2 lowPorts c small lowPorts_injective 1
    simpa [b,small,lowPorts,HeadIdentifierProgram.LowMask.state,List.map_reverse] using h
  · exact embedState_stack r2 lowPorts c small lowPorts_injective 0
  · have h := embedState_register_frame r2 lowPorts c small 8 (by decide)
    simpa [b,c,copied,SubexpScanPrimitives.afterCopy,readRegs] using h

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowMask_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowMask_eval_oai
