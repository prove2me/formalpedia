-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.maskCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:57:10.522083+00:00
-- url     : https://prove2.me/submissions/5c3ed379-6d8e-4d8e-8dde-131588f3ef96

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S130

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion from descending high mask to forward high mask. The
descending mask is retained for the high-assignment iterator. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (regs : Fin 2 → Bool) (mask : List Bool) :
    ∃ rf, Eval command (10 * mask.length + 8)
      (state regs mask [] [] []) (state rf mask [] mask.reverse []) := by
  let r := readRegs regs 0 1 none
  have hc : Eval (.call (StackRoutines.copyProgram 0 1 3 0 1)) (7 * mask.length + 5)
      (state regs mask [] [] []) (state r mask mask [] []) := by
    have h := ListRegisterProgram.copy_run (0 : Fin 4) 1 3 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) regs (state regs mask [] [] []).stacks rfl
    have hs : StackRoutines.copyStacks 0 1 (state regs mask [] [] []).stacks =
        (state r mask mask [] []).stacks := by
      funext i; fin_cases i <;> simp [StackRoutines.copyStacks ]
    apply Eval.call
    simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, r, hs] using h
  have ht : Eval (.call (StackRoutines.transferProgram 1 2 0 1)) (3 * mask.length + 3)
      (state r mask mask [] []) (state (readRegs r 0 1 none) mask [] mask.reverse []) := by
    have h := ListRegisterProgram.transfer_run (1 : Fin 4) 2 (0 : Fin 2) 1
      (by decide) (by decide) r (state r mask mask [] []).stacks
    have hs : StackRoutines.transferStacks 1 2 (state r mask mask [] []).stacks =
        (state (readRegs r 0 1 none) mask [] mask.reverse []).stacks := by
      funext i; fin_cases i <;> simp [StackRoutines.transferStacks ]
    apply Eval.call
    simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, r, hs] using h
  exact ⟨_, by convert hc.seq ht using 1 ; omega⟩

theorem runsIn (regs : Fin 2 → Bool) (mask : List Bool) :
    ∃ rf, RunsIn program (10 * mask.length + 9)
      ((state regs mask [] [] []).withPC (some program.entry))
      ((state rf mask [] mask.reverse []).withPC none) := by
  obtain ⟨rf, he⟩ := command_eval regs mask
  refine ⟨rf, 10 * mask.length + 8 + 1, by omega, compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask

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

theorem mask_injective : Function.Injective mask := by decide

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem call_run {r s l : ℕ} (p : Program r s l) (rr : Fin r → Fin 40)
    (ss : Fin s → Fin 768) (hr : Function.Injective rr) (hs : Function.Injective ss)
    (a : Data) (b : State r s) (B : ℕ)
    (h : RunsIn p B ((projectState rr ss a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n ≤ B, Eval (.call (ProgramLinking.liftProgram p rr ss)) n a (embedState rr ss a b) := by
  obtain ⟨n,hn,ht⟩ := h
  exact ⟨n,hn,eval_call_from_state p rr ss a hr hs ht⟩

theorem maskCall_eval_oai (a : Data) (descending : List Bool)
    (hp : projectState r2 mask a = HighIncidenceProgram.Mask.state (a.regs ∘ r2) descending [] [] []) :
    ∃ n ≤ 10*descending.length+9, ∃ rf,
      Eval maskCall n a (embedState r2 mask a
        (HighIncidenceProgram.Mask.state rf descending [] descending.reverse [])) := by
  obtain ⟨rf,he⟩ := HighIncidenceProgram.Mask.runsIn (a.regs ∘ r2) descending
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r2 mask (registers_injective ..) mask_injective a _ _ he
  exact ⟨n,hn,rf,he⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.maskCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.maskCall_eval_oai
