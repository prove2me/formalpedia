-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:59:53.683372+00:00
-- url     : https://prove2.me/submissions/aefe2f36-489b-409d-89b2-cb718b866855

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed eight-label program counts nonzero two-bit cells. The input is
consumed and the count is emitted in unary. This is an actual support counter,
not a unit-cost application of `List.countP`. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram
open scoped BigOperators

theorem framedSupport_round (regs : Fin 4 → Bool) (a b : Bool)
    (input output : List Bool) :
    Trace framedSupportProgram (if a || b then 10 else 8)
      (framedSupportCfg (some 0) regs (true :: a :: true :: b :: false :: input) output)
      (framedSupportCfg (some 0) (framedSupportRoundRegs regs a b) input
        ((if a || b then [true] else []) ++ output)) := by
  cases a <;> cases b <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, framedSupportProgram, framedSupportCfg,
      framedSupportRoundRegs, execInstr, readRegs, Function.update_apply] <;>
    funext i <;> fin_cases i <;> simp

theorem framedSupport_exit (regs : Fin 4 → Bool) (output : List Bool) :
    Trace framedSupportProgram 3
      (framedSupportCfg (some 0) regs [] output)
      (framedSupportCfg none (readRegs regs 2 1 none) [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, framedSupportProgram, framedSupportCfg,
    execInstr, readRegs, Function.update_apply]

theorem framedSupport_trace (xs : List (Bool × Bool)) (regs : Fin 4 → Bool)
    (output : List Bool) :
    ∃ rf, Trace framedSupportProgram (framedCellCost xs)
      (framedSupportCfg (some 0) regs (framedCellStream xs) output)
      (framedSupportCfg none rf [] (List.replicate (cellWeight xs) true ++ output)) := by
  induction xs generalizing regs output with
  | nil => exact ⟨readRegs regs 2 1 none, framedSupport_exit regs output⟩
  | cons x xs ih =>
      rcases x with ⟨a,b⟩
      obtain ⟨rf, ht⟩ := ih (framedSupportRoundRegs regs a b)
        ((if a || b then [true] else []) ++ output)
      refine ⟨rf, ?_⟩
      have h := (framedSupport_round regs a b (framedCellStream xs) output).trans ht
      cases a <;> cases b <;>
        simpa [framedCellCost, framedCellStream, cellWeight, List.replicate_add,
          List.append_assoc] using h

theorem framedCellCost_le (xs : List (Bool × Bool)) :
    framedCellCost xs ≤ 10 * xs.length + 3 := by
  induction xs with
  | nil => simp [framedCellCost]
  | cons x xs ih =>
      rcases x with ⟨a,b⟩
      cases a <;> cases b <;> simp [framedCellCost] <;> omega

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed support and unary comparison as framed subroutine calls. The port
maps are fixed finite maps; the lengths being scanned occur only on tapes. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem scanRegisters_injective : Function.Injective scanRegisters :=
  Fin.castAdd_injective _ _

theorem scanStacks_injective (input output : Fin 18) (h : input ≠ output) :
    Function.Injective (scanStacks input output) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [scanStacks]

theorem supportAt_eval (input output : Fin 18) (hne : input ≠ output)
    (cells : List (Bool × Bool)) (base : ScanState)
    (hin : base.stacks input = framedCellStream cells)
    (hout : base.stacks output = []) :
    ∃ (n : ℕ) (next : ScanState), n ≤ 10 * cells.length + 3 ∧
      Eval (supportAt input output) n base next ∧
      next.stacks input = [] ∧
      next.stacks output = List.replicate (cellWeight cells) true ∧
      (∀ i : Fin 8, 4 ≤ i.val → next.regs i = base.regs i) ∧
      (∀ j, j ≠ input → j ≠ output → next.stacks j = base.stacks j) := by
  obtain ⟨rf, ht⟩ := framedSupport_trace cells (base.regs ∘ scanRegisters) []
  let a : State 4 2 := ⟨base.regs ∘ scanRegisters, ![framedCellStream cells, []]⟩
  let b : State 4 2 := ⟨rf, ![[], List.replicate (cellWeight cells) true]⟩
  have ha : embedState scanRegisters (scanStacks input output) base a = base := by
    apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective
      (scanStacks_injective _ _ hne)
    · intro i; rfl
    · intro i; fin_cases i <;> simpa [a, scanStacks] using (by assumption)
    · intros; rfl
    · intros; rfl
  have htrace : Trace framedSupportProgram (framedCellCost cells)
      (a.withPC (some framedSupportProgram.entry)) (b.withPC none) := by
    simpa [a, b, framedSupportCfg] using ht
  have he := eval_call_lifted framedSupportProgram scanRegisters (scanStacks input output)
    base scanRegisters_injective (scanStacks_injective _ _ hne) htrace
  rw [ha] at he
  refine ⟨framedCellCost cells, _, framedCellCost_le cells, he, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack _ _ base b (scanStacks_injective _ _ hne) 0
  · exact embedState_stack _ _ base b (scanStacks_injective _ _ hne) 1
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hval := congrArg Fin.val hj
    simp [scanRegisters] at hval
    omega
  · intro j hi ho
    apply embedState_stack_frame
    rintro ⟨i, hij⟩
    fin_cases i <;> simp_all [scanStacks]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCountTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Two physical support counters for a Walsh query. The parity count is kept
on tape9, while register7 reports whether the input character is nonzero. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

theorem graphCountTail_eval_oai (ys xs : List (Bool × Bool)) (base : ScanState)
    (hy : base.stacks 8 = framedCellStream ys)
    (hx : base.stacks 12 = framedCellStream xs)
    (h9 : base.stacks 9 = []) (h10 : base.stacks 10 = []) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ 10 * ys.length + 10 * xs.length + 9 ∧
      Eval graphCountTail n base next ∧
      next.regs 7 = decide (cellWeight xs ≠ 0) ∧
      next.stacks 9 = List.replicate (cellWeight ys) true ∧
      next.stacks 16 = base.stacks 16 ∧ next.stacks 17 = base.stacks 17 := by
  obtain ⟨ny,y,hny,hey,hy8,hy9,hyr,hys⟩ := supportAt_eval 8 9 (by decide) ys base hy h9
  have hy12 : y.stacks 12 = framedCellStream xs := by
    rw [hys 12 (by decide) (by decide),hx]
  have hy10 : y.stacks 10 = [] := by rw [hys 10 (by decide) (by decide),h10]
  obtain ⟨nx,x,hnx,hex,hx12,hx10,hxr,hxs⟩ := supportAt_eval 12 10 (by decide) xs y hy12 hy10
  let peeked := (Atom.peek 10 0 1).eval x
  let out := (Atom.copy 7 1).eval peeked
  have hpresent : (List.replicate (cellWeight xs) true).head?.isSome =
      decide (cellWeight xs ≠ 0) := by cases cellWeight xs <;> simp
  refine ⟨ny+(nx+(1+1)),out,by omega,
    hey.seq (hex.seq ((Eval.base (.atom _ x)).seq (Eval.base (.atom _ peeked)))),?_,?_,?_,?_⟩
  · simp [out,peeked,Atom.eval,Atom.instr,StructuredProgram.State.ofCfg,execInstr,readRegs,hx10,hpresent]
  · change x.stacks 9 = _
    rw [hxs 9 (by decide) (by decide),hy9]
  · change x.stacks 16 = _
    rw [hxs 16 (by decide) (by decide),hys 16 (by decide) (by decide)]
  · change x.stacks 17 = _
    rw [hxs 17 (by decide) (by decide),hys 17 (by decide) (by decide)]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval_oai
