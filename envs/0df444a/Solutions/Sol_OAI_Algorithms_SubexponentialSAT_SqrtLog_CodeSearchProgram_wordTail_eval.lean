-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordTail_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:00:53.905734+00:00
-- url     : https://prove2.me/submissions/d61c4ee5-0e86-4dc2-bfc6-76b4b1ae6268

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An eight-label comparison of unary counts. Only stack presence is read;
the count values never occur in the finite instruction table. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram

theorem unaryLess_nil (regs : Fin 4 → Bool) (right : List Bool) :
    Trace unaryLessProgram 5 (unaryLessCfg (some 0) regs [] right)
      (unaryLessCfg none
        (Function.update (readRegs (readRegs regs 0 1 none) 0 2 right.head?)
          3 right.head?.isSome) [] right) := by
  cases right <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
      execInstr, readRegs, Function.update_apply]

theorem unaryLess_right_nil (regs : Fin 4 → Bool) (a : Bool) (left : List Bool) :
    Trace unaryLessProgram 6 (unaryLessCfg (some 0) regs (a :: left) [])
      (unaryLessCfg none
        (Function.update (readRegs (readRegs regs 0 1 (some a)) 0 2 none) 3 false)
        left []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals (funext i; fin_cases i <;> simp)

theorem unaryLess_round (regs : Fin 4 → Bool) (a b : Bool) (left right : List Bool) :
    Trace unaryLessProgram 4 (unaryLessCfg (some 0) regs (a :: left) (b :: right))
      (unaryLessCfg (some 0) (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
        left right) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals (funext i; fin_cases i <;> simp)

theorem unaryLess_trace (left right : List Bool) (regs : Fin 4 → Bool) :
    ∃ n rf l r, n ≤ 4 * left.length + 6 ∧
      Trace unaryLessProgram n (unaryLessCfg (some 0) regs left right)
        (unaryLessCfg none rf l r) ∧
      rf 3 = decide (left.length < right.length) := by
  induction left generalizing right regs with
  | nil =>
      refine ⟨5, _, [], right, by simp, unaryLess_nil regs right, ?_⟩
      cases right <;> simp
  | cons a left ih =>
      cases right with
      | nil =>
          exact ⟨6, _, left, [], by simp, unaryLess_right_nil regs a left, by simp⟩
      | cons b right =>
          obtain ⟨n, rf, l, r, hn, ht, hf⟩ :=
            ih right (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
          refine ⟨4 + n, rf, l, r, ?_, (unaryLess_round regs a b left right).trans ht, ?_⟩
          · simp only [List.length_cons]
            omega
          · simpa using hf

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

theorem lessAt_eval (left right : Fin 18) (hne : left ≠ right)
    (base : ScanState) :
    ∃ (n : ℕ) (next : ScanState), n ≤ 4 * (base.stacks left).length + 6 ∧
      Eval (lessAt left right) n base next ∧
      next.regs 3 = decide ((base.stacks left).length < (base.stacks right).length) ∧
      (∀ i : Fin 8, 4 ≤ i.val → next.regs i = base.regs i) ∧
      (∀ j, j ≠ left → j ≠ right → next.stacks j = base.stacks j) := by
  obtain ⟨n, rf, l, r, hn, ht, hf⟩ :=
    unaryLess_trace (base.stacks left) (base.stacks right) (base.regs ∘ scanRegisters)
  let a : State 4 2 := ⟨base.regs ∘ scanRegisters, ![base.stacks left, base.stacks right]⟩
  let b : State 4 2 := ⟨rf, ![l,r]⟩
  have ha : embedState scanRegisters (scanStacks left right) base a = base := by
    apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective
      (scanStacks_injective _ _ hne)
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have htrace : Trace unaryLessProgram n (a.withPC (some unaryLessProgram.entry))
      (b.withPC none) := by simpa [a, b, unaryLessCfg] using ht
  have he := eval_call_lifted unaryLessProgram scanRegisters (scanStacks left right)
    base scanRegisters_injective (scanStacks_injective _ _ hne) htrace
  rw [ha] at he
  refine ⟨n, _, hn, he, ?_, ?_, ?_⟩
  · exact (embedState_register _ _ base b scanRegisters_injective 3).trans hf
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramWordTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual decision tail for a proposed low-weight kernel word. It reads
both framed vectors, compares unary support with the runtime threshold, and
sets register 7 precisely on rejection. No semantic predicate is an opcode. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

private theorem replicate_present (w : ℕ) :
    (List.replicate w true).head?.isSome = decide (w ≠ 0) := by
  cases w <;> simp

private theorem cellWeight_le_length (xs : List (Bool × Bool)) :
    cellWeight xs ≤ xs.length := by
  induction xs with
  | nil => simp [cellWeight]
  | cons x xs ih =>
      simp only [cellWeight, List.length_cons]
      split <;> omega

theorem wordTail_eval_oai (ys xs : List (Bool × Bool)) (d : ℕ) (base : ScanState)
    (hy : base.stacks 8 = framedCellStream ys)
    (hx : base.stacks 12 = framedCellStream xs)
    (h9 : base.stacks 9 = []) (h10 : base.stacks 10 = [])
    (hd : base.stacks 16 = List.replicate d true) :
    ∃ (n : ℕ) (next : ScanState), n + 1 ≤ wordTailBudget ys.length xs.length ∧
      Eval wordTailCommand n base next ∧
      next.regs 7 = decide (cellWeight ys = 0 ∧ cellWeight xs ≠ 0 ∧ cellWeight xs < d) ∧
      next.stacks 17 = base.stacks 17 := by
  obtain ⟨na, a, hna, hea, ha8, ha9, har, has⟩ :=
    supportAt_eval 8 9 (by decide) ys base hy h9
  let b := (Atom.peek 9 0 1).eval a
  let c := (Atom.bnot 6 1).eval b
  have hc6 : c.regs 6 = decide (cellWeight ys = 0) := by
    simp [c, b, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs, ha9,
      replicate_present]
  have hc12 : c.stacks 12 = framedCellStream xs := by
    change a.stacks 12 = _
    rw [has 12 (by decide) (by decide), hx]
  have hc10 : c.stacks 10 = [] := by
    change a.stacks 10 = _
    rw [has 10 (by decide) (by decide), h10]
  obtain ⟨nb, e, hnb, heb, he12, he10, her, hes⟩ :=
    supportAt_eval 12 10 (by decide) xs c hc12 hc10
  let f := (Atom.peek 10 0 1).eval e
  let g := (Atom.band 7 6 1).eval f
  have hg7 : g.regs 7 = decide (cellWeight ys = 0 ∧ cellWeight xs ≠ 0) := by
    have he6 := her 6 (by decide)
    rw [hc6] at he6
    simp [g, f, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs, he10,
      replicate_present, he6]
  have hg10 : g.stacks 10 = List.replicate (cellWeight xs) true := he10
  have hg16 : g.stacks 16 = List.replicate d true := by
    change e.stacks 16 = _
    rw [hes 16 (by decide) (by decide)]
    change a.stacks 16 = _
    rw [has 16 (by decide) (by decide), hd]
  obtain ⟨nc, h, hnc, hec, hh3, hhr, hhs⟩ := lessAt_eval 10 16 (by decide) g
  have hh7 := hhr 7 (by decide)
  rw [hg7] at hh7
  rw [hg10, hg16, List.length_replicate, List.length_replicate] at hh3
  let out := (Atom.band 7 7 3).eval h
  have hout : out.regs 7 =
      decide (cellWeight ys = 0 ∧ cellWeight xs ≠ 0 ∧ cellWeight xs < d) := by
    simp [out, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg, execInstr, hh7, hh3, Bool.and_assoc]
  refine ⟨na + (1 + (1 + (nb + (1 + (1 + (nc + 1)))))), out, ?_, ?_, hout, ?_⟩
  · rw [hg10, List.length_replicate] at hnc
    have hw : cellWeight xs ≤ xs.length := cellWeight_le_length xs
    unfold wordTailBudget
    omega
  · exact hea.seq <| (Eval.base (.atom _ a)).seq <| (Eval.base (.atom _ b)).seq <|
      heb.seq <| (Eval.base (.atom _ e)).seq <| (Eval.base (.atom _ f)).seq <|
        hec.seq (Eval.base (.atom _ h))
  · change h.stacks 17 = _
    rw [hhs 17 (by decide) (by decide)]
    change e.stacks 17 = _
    rw [hes 17 (by decide) (by decide)]
    change a.stacks 17 = _
    exact has 17 (by decide) (by decide)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordTail_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordTail_eval_oai
