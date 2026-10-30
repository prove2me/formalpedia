-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:54:50.193879+00:00
-- url     : https://prove2.me/submissions/d94ff5b0-b859-4688-ab0d-412d9c2e3f5f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S126

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

/-- Transport only a caller's initial state; do not rewrite through its program. -/
theorem transport_initial {r s l : ℕ} (p : Program r s l) (bound : ℕ)
    {a b final : State r s} (hab : a = b)
    (h : RunsIn p bound (a.withPC (some p.entry)) (final.withPC none)) :
    RunsIn p bound (b.withPC (some p.entry)) (final.withPC none) := by
  cases hab
  exact h


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem mask_eval_oai (regs : Fin 4 → Bool) (counter mask : List Bool) :
    ∃ n rf, n ≤ 10*mask.length+9 ∧ Eval maskStep n
      (state regs counter mask [] [] [] [] [] [] [] [])
      (state rf counter mask mask.reverse [] [] [] [] [] [] []) := by
  let a := state regs counter mask [] [] [] [] [] [] [] []
  obtain ⟨rf,hr⟩ := HighIncidenceProgram.Mask.runsIn (regs ∘ maskRegs) mask
  have ha : restrictState maskRegs maskStacks a =
      HighIncidenceProgram.Mask.state (regs ∘ maskRegs) mask [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have hr' := transport_initial _ _ ha.symm hr
  obtain ⟨n,hn,he⟩ := lifted_call _ maskRegs maskStacks (Fin.castAdd_injective 2 2)
    (by decide) a _ _ hr'
  let rout : Fin 4 → Bool := ![rf 0,rf 1,regs 2,regs 3]
  have hb : embedState maskRegs maskStacks a
      (HighIncidenceProgram.Mask.state rf mask [] mask.reverse []) =
      state rout counter mask mask.reverse [] [] [] [] [] [] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 2 2) (by decide)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;>
        first
        | rfl
        | exact (hi ⟨0,rfl⟩).elim
        | exact (hi ⟨1,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;>
        first
        | rfl
        | exact (hi ⟨0,rfl⟩).elim
        | exact (hi ⟨1,rfl⟩).elim
        | exact (hi ⟨2,rfl⟩).elim
  have he' := Eq.mp (congrArg (fun b => Eval maskStep n a b) hb) he
  exact ⟨n,rout,hn,he'⟩


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mask_eval_oai
