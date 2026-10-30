-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:04:11.355778+00:00
-- url     : https://prove2.me/submissions/a877d08a-d697-411d-b0f8-f175c474a623

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S111
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecPetalChildProgram_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded clause subset testing

The fixed program uses ten Boolean registers and eight Boolean stacks. The
source clause is scanned destructively on stack 0. Stack 2 preserves the entire
encoded target clause. All comparisons use the proved encoded membership
program, after a real preserving copy of the target.
-/
namespace SubexponentialSAT.ExecCNFSubset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem clear_eval (port : Fin 8) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace (r := 10) (s := 8) port 0 1 d.regs d.stacks
  have hh : step (clearProgram port)
      (StackRoutines.clearResult 2 port 0 1 d.regs d.stacks) =
      some ((cleared port d).withPC none) := by
    simp [step, StackRoutines.clearResult, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [clearProgram, cleared, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

end SubexponentialSAT.ExecCNFSubset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

private theorem negate_start (v p : Bool) (input output : List Bool) :
    Trace negateProgram 2 (cfg (some 0) v p input output)
      (cfg (some 2) false p input (false :: output)) := by
  refine .cons (b := cfg (some 1) false p input output) ?_ (.cons ?_ (.refl _)) <;>
    simp [step, cfg, execInstr]

/-- Eight fixed instructions consume one pair of unary marks. -/
theorem negate_pair (v p : Bool) (input output : List Bool) :
    Trace negateProgram 8 (cfg (some 2) v p (true :: true :: input) output)
      (cfg (some 2) true true input (true :: true :: output)) := by
  refine .cons (b := cfg (some 3) true true (true :: input) output) ?_
    (.cons (b := cfg (some 4) true true (true :: input) output) ?_
    (.cons (b := cfg (some 5) true true (true :: input) output) ?_
    (.cons (b := cfg (some 6) true true input output) ?_
    (.cons (b := cfg (some 7) true true input output) ?_
    (.cons (b := cfg (some 8) true true input output) ?_
    (.cons (b := cfg (some 9) true true input (true :: output)) ?_
    (.cons ?_ (.refl _)))))))) <;>
    simp [step, cfg, execInstr, readRegs]

private theorem negate_finish (v p : Bool) (input output : List Bool) :
    Trace negateProgram 3 (cfg (some 12) v p input output)
      (cfg none false false input output) := by
  refine .cons (b := cfg (some 13) false p input output) ?_
    (.cons (b := cfg (some 14) false false input output) ?_
    (.cons ?_ (.refl _))) <;>
    simp [step, cfg, execInstr]

private theorem negate_even_zero (v p : Bool) (input output : List Bool) :
    Trace negateProgram 8 (cfg (some 2) v p (false :: input) output)
      (cfg none false false input (true :: output)) := by
  have h : Trace negateProgram 5 (cfg (some 2) v p (false :: input) output)
      (cfg (some 12) true true input (true :: output)) := by
    refine .cons (b := cfg (some 3) false true input output) ?_
      (.cons (b := cfg (some 4) false true input output) ?_
      (.cons (b := cfg (some 10) false true input output) ?_
      (.cons (b := cfg (some 11) true true input output) ?_
      (.cons ?_ (.refl _))))) <;>
      simp [step, cfg, execInstr, readRegs]
  exact h.trans (negate_finish true true input (true :: output))

private theorem negate_odd_zero (v p : Bool) (input output : List Bool) :
    Trace negateProgram 9 (cfg (some 2) v p (true :: false :: input) output)
      (cfg none false false input output) := by
  have h : Trace negateProgram 6 (cfg (some 2) v p (true :: false :: input) output)
      (cfg (some 12) false true input output) := by
    refine .cons (b := cfg (some 3) true true (false :: input) output) ?_
      (.cons (b := cfg (some 4) true true (false :: input) output) ?_
      (.cons (b := cfg (some 5) true true (false :: input) output) ?_
      (.cons (b := cfg (some 6) false true input output) ?_
      (.cons (b := cfg (some 7) false true input output) ?_
      (.cons ?_ (.refl _)))))) <;>
      simp [step, cfg, execInstr, readRegs]
  exact h.trans (negate_finish false true input output)

private theorem negate_even_loop (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace negateProgram (8 * n + 8)
      (cfg (some 2) v p (Encoding.encodeNat (2 * n) ++ rest) output)
      (cfg none false false rest (List.replicate (2 * n + 1) true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using negate_even_zero v p rest output
  | succ n ih =>
      have h := (negate_pair v p (Encoding.encodeNat (2 * n) ++ rest) output).trans
        (ih (true :: true :: output) true true)
      have htime : 8 + (8 * n + 8) = 8 * (n + 1) + 8 := by omega
      have hin : Encoding.encodeNat (2 * (n + 1)) ++ rest =
          true :: true :: (Encoding.encodeNat (2 * n) ++ rest) := by
        rw [show 2 * (n + 1) = 2 + 2 * n by omega]
        simp [Encoding.encodeNat, List.replicate_add, List.append_assoc]
      have hout : List.replicate (2 * n + 1) true ++ true :: true :: output =
          List.replicate (2 * (n + 1) + 1) true ++ output := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
        simp [List.replicate_add, List.append_assoc]
      simpa only [htime, hin, hout] using h

private theorem negate_odd_loop (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace negateProgram (8 * n + 9)
      (cfg (some 2) v p (Encoding.encodeNat (2 * n + 1) ++ rest) output)
      (cfg none false false rest (List.replicate (2 * n) true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using negate_odd_zero v p rest output
  | succ n ih =>
      have h := (negate_pair v p (Encoding.encodeNat (2 * n + 1) ++ rest) output).trans
        (ih (true :: true :: output) true true)
      have htime : 8 + (8 * n + 9) = 8 * (n + 1) + 9 := by omega
      have hin : Encoding.encodeNat (2 * (n + 1) + 1) ++ rest =
          true :: true :: (Encoding.encodeNat (2 * n + 1) ++ rest) := by
        rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega]
        simp [Encoding.encodeNat, List.replicate_add, List.append_assoc]
      have hout : List.replicate (2 * n) true ++ true :: true :: output =
          List.replicate (2 * (n + 1)) true ++ output := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        simp [List.replicate_add, List.append_assoc]
      simpa only [htime, hin, hout] using h

/-- Actual execution on a valid encoded literal. The input suffix and output
accumulator are preserved exactly, so this is usable as a linked subroutine. -/
theorem negate_trace (c : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace negateProgram (negateSteps c)
      (cfg (some 0) v p (Encoding.encodeNat c ++ rest) output)
      (cfg none false false rest
        (Encoding.encodeNat (SubexpFrontend.negateCode c) ++ output)) := by
  have hmod : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · have hc : c = 2 * (c / 2) := by omega
    have hloop := negate_even_loop (c / 2) rest (false :: output) false p
    rw [← show Encoding.encodeNat c = Encoding.encodeNat (2 * (c / 2)) from
      congrArg Encoding.encodeNat hc] at hloop
    have h := (negate_start v p (Encoding.encodeNat c ++ rest) output).trans
      hloop
    have htime : 2 + (8 * (c / 2) + 8) = 8 * (c / 2) + 10 := by omega
    rw [htime] at h
    simpa [negateSteps, SubexpFrontend.negateCode, hmod, Encoding.encodeNat,
      List.append_assoc, Nat.add_assoc] using h
  · have hc : c = 2 * (c / 2) + 1 := by omega
    have hloop := negate_odd_loop (c / 2) rest (false :: output) false p
    rw [← show Encoding.encodeNat c = Encoding.encodeNat (2 * (c / 2) + 1) from
      congrArg Encoding.encodeNat hc] at hloop
    have h := (negate_start v p (Encoding.encodeNat c ++ rest) output).trans
      hloop
    have htime : 2 + (8 * (c / 2) + 9) = 8 * (c / 2) + 11 := by omega
    rw [htime] at h
    simpa [negateSteps, SubexpFrontend.negateCode, hmod, Encoding.encodeNat,
      List.append_assoc, Nat.add_assoc] using h

theorem negateSteps_le (c : ℕ) : negateSteps c ≤ 4 * c + 10 := by
  unfold negateSteps
  omega

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

open BitProgram StructuredCalls

theorem emitReg_injective : Function.Injective emitReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitReg]

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stackValues =>
      unfold embedState
      congr 1
      · funext i
        by_cases h : ∃ j, reg j = i
        · obtain ⟨j, rfl⟩ := h
          exact hr.extend_apply _ _ _
        · exact Function.extend_apply' _ _ _ h
      · funext i
        by_cases h : ∃ j, stk j = i
        · obtain ⟨j, rfl⟩ := h
          exact hs.extend_apply _ _ _
        · exact Function.extend_apply' _ _ _ h

theorem emitCall_eval (selected : Bool) (bits : List Bool) (d : Data)
    (hquery : d.stacks 1 = bits.reverse) (hselected : d.regs 9 = selected) :
    ∃ e : Data,
      Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if selected then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) ∧
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = d.stacks 5 ∧ e.stacks 6 = d.stacks 6 ∧ e.stacks 7 = d.stacks 7 ∧
      e.regs 7 = false ∧ e.regs 8 = true ∧ e.regs 9 = false := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ emitStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) selected
      (d.stacks 0) (d.stacks 7) (d.stacks 2) bits.reverse := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg, hselected]
    · funext i
      fin_cases i <;> simp [ emitStack, hquery]
  have ht := SubexpNormalizeProgram.emitIfSelected_trace selected bits
    (d.stacks 0) (d.stacks 7) (d.stacks 2) (d.regs 7) (d.regs 8)
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitReg emitStack d emitReg_injective emitStack_injective ht
  rw [embed_restricted emitReg emitStack emitReg_injective emitStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 7)
    (if selected then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) []
  let e := embedState emitReg emitStack d b
  have hstack (i : Fin 4) : e.stacks (emitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ emitStack_injective i
  have hreg (i : Fin 3) : e.regs (emitReg i) = b.regs i :=
    embedState_register _ _ _ _ emitReg_injective i
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 0
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 2

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNegatedQueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving complemented-literal queries

The clause iterator supplies a literal's unary word in reverse order. This
fixed program preserves that query on stack 0 and writes the reversed unary
word for the opposite literal on stack 1. Stacks 2 and 3 are empty workspaces
on entry and return. All costs below count actual finite-program transitions.
-/

namespace SubexponentialSAT.SubexpNegatedQueryProgram

open BitProgram StructuredCalls
open ParserProgram (pair)

theorem negatePorts_injective : Function.Injective negatePorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [negatePorts] at h ⊢

theorem copyQuery_eval (query : List Bool) (v p : Bool) :
    Eval (.call copyQuery) (7 * query.length + 5)
      (state v p query [] [] []) (state false false query [] query []) := by
  have h := StackRoutines.copyProgram_trace (0 : Fin 4) 2 3 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (pair v p) (slots query [] [] []) rfl
  have hh := StackRoutines.halt_after_trace copyQuery h 7 rfl rfl
  apply Eval.call
  simpa [copyQuery, StackRoutines.copyResult, StackRoutines.copyStacks,
    readRegs, state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem reverseWork_eval (query work : List Bool) (v p : Bool) :
    Eval (.call reverseWork) (9 * work.length + 7)
      (state v p query [] work []) (state false false query [] work.reverse []) := by
  have h := StackRoutines.reverseProgram_trace (2 : Fin 4) 1 3 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (pair v p) (slots query [] work []) rfl rfl
  have hh := StackRoutines.halt_after_trace reverseWork h 9 rfl rfl
  apply Eval.call
  simpa [reverseWork, StackRoutines.reverseResult, StackRoutines.reverseStacks,
    readRegs, state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem reverseResult_eval (query result : List Bool) (v p : Bool) :
    Eval (.call reverseResult) (9 * result.length + 7)
      (state v p query result [] []) (state false false query result.reverse [] []) := by
  have h := StackRoutines.reverseProgram_trace (1 : Fin 4) 2 3 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (pair v p) (slots query result [] []) rfl rfl
  have hh := StackRoutines.halt_after_trace reverseResult h 9 rfl rfl
  apply Eval.call
  simpa [reverseResult, StackRoutines.reverseResult, StackRoutines.reverseStacks,
    readRegs, state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem extend_negate_slots (query input output : List Bool) :
    Function.extend negatePorts (pair input output) (slots query [] [] []) =
      slots query output input [] := by
  funext i
  fin_cases i
  · apply Function.extend_apply'
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [negatePorts] at hj
  · exact negatePorts_injective.extend_apply _ _ 1
  · exact negatePorts_injective.extend_apply _ _ 0
  · apply Function.extend_apply'
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [negatePorts] at hj

theorem embed_negate_state (query input output : List Bool) (v p : Bool) :
    embedState id negatePorts (state false false query [] [] [])
      ⟨pair v p, pair input output⟩ = state v p query output input [] := by
  simp [embedState, state, extend_negate_slots]

theorem negateWork_eval (c : ℕ) (query : List Bool) (v p : Bool) :
    Eval (.call negateWork) (SubexpNormalizeProgram.negateSteps c)
      (state v p query [] (Encoding.encodeNat c) [])
      (state false false query (Encoding.encodeNat (SubexpFrontend.negateCode c)) [] []) := by
  have h : Trace SubexpNormalizeProgram.negateProgram
      (SubexpNormalizeProgram.negateSteps c)
      ((⟨pair v p, pair (Encoding.encodeNat c) []⟩ : State 2 2).withPC
        (some SubexpNormalizeProgram.negateProgram.entry))
      ((⟨pair false false, pair [] (Encoding.encodeNat (SubexpFrontend.negateCode c))⟩ :
        State 2 2).withPC none) := by
    simpa [StructuredProgram.State.withPC, SubexpNormalizeProgram.negateProgram,
      ParserProgram.cfg] using SubexpNormalizeProgram.negate_trace c [] [] v p
  have he := eval_call_lifted SubexpNormalizeProgram.negateProgram id negatePorts
    (state false false query [] [] []) Function.injective_id negatePorts_injective h
  simpa only [embed_negate_state, negateWork] using he

theorem command_eval (c : ℕ) (v p : Bool) :
    Eval command (steps c - 1)
      (state v p (Encoding.encodeNat c).reverse [] [] [])
      (state false false (Encoding.encodeNat c).reverse
        (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []) := by
  have hcopy := copyQuery_eval (Encoding.encodeNat c).reverse v p
  have hrev := reverseWork_eval (Encoding.encodeNat c).reverse
    (Encoding.encodeNat c).reverse false false
  simp only [List.reverse_reverse, List.length_reverse] at hcopy hrev
  have hneg := negateWork_eval c (Encoding.encodeNat c).reverse false false
  have hout := reverseResult_eval (Encoding.encodeNat c).reverse
    (Encoding.encodeNat (SubexpFrontend.negateCode c)) false false
  have h := Eval.seq hcopy (Eval.seq hrev (Eval.seq hneg hout))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [ steps]
  omega

theorem program_trace (c : ℕ) (v p : Bool) :
    Trace program (steps c)
      ((state v p (Encoding.encodeNat c).reverse [] [] []).withPC (some program.entry))
      ((state false false (Encoding.encodeNat c).reverse
        (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []).withPC none) := by
  have h := compiled_halt_trace (command_eval c v p) 0 1
  have hs : steps c - 1 + 1 = steps c := by unfold steps; omega
  simpa only [hs, program] using h

theorem negateCode_le (c : ℕ) : SubexpFrontend.negateCode c ≤ c + 1 := by
  unfold SubexpFrontend.negateCode
  split <;> omega

theorem steps_le (c : ℕ) : steps c ≤ 29 * (Encoding.encodeNat c).length + 35 := by
  have hn := negateCode_le c
  have hs := SubexpNormalizeProgram.negateSteps_le c
  simp only [steps, Encoding.length_encodeNat]
  omega

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded-clause tautology testing

The outer iterator reads unary literal records. For each literal, a concrete
program builds its opposite's query, copies the preserved clause, and runs the
proved encoded membership program. All data-dependent repetition is in those
finite programs and the record iterator.
-/

namespace SubexponentialSAT.SubexpTautologyProgram

open BitProgram StructuredCalls

theorem negateReg_injective : Function.Injective negateReg := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 10 => i.val) h)

theorem negateStack_injective : Function.Injective negateStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [negateStack]

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stackValues =>
    unfold embedState
    congr 1
    · funext i
      by_cases h : ∃ j, reg j = i
      · obtain ⟨j, rfl⟩ := h
        exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stk j = i
      · obtain ⟨j, rfl⟩ := h
        exact hs.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

theorem negateQuery_eval (c : ℕ) (d : Data)
    (hq : d.stacks 7 = (Encoding.encodeNat c).reverse)
    (h1 : d.stacks 1 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ e : Data,
      Eval negateQuery (SubexpNegatedQueryProgram.steps c) d e ∧
      e.stacks 1 = (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 2 = d.stacks 2 ∧
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = [] ∧ e.stacks 6 = [] ∧ e.stacks 7 = d.stacks 7 ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
  let a := SubexpNegatedQueryProgram.state (d.regs 0) (d.regs 1)
    (Encoding.encodeNat c).reverse [] [] []
  let b := SubexpNegatedQueryProgram.state false false (Encoding.encodeNat c).reverse
    (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []
  have ha : a = ⟨d.regs ∘ negateReg, d.stacks ∘ negateStack⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [
        SubexpNegatedQueryProgram.slots, negateStack, hq, h1, h5, h6]
  let e := embedState negateReg negateStack d b
  have he := eval_call_lifted SubexpNegatedQueryProgram.program negateReg negateStack d
    negateReg_injective negateStack_injective
    (SubexpNegatedQueryProgram.program_trace c (d.regs 0) (d.regs 1))
  change Eval negateQuery (SubexpNegatedQueryProgram.steps c)
    (embedState negateReg negateStack d a) e at he
  rw [ha, embed_restricted _ _ negateReg_injective negateStack_injective] at he
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack negateReg negateStack d b negateStack_injective 1
  · exact embedState_stack_frame negateReg negateStack d b 0 (by decide)
  · exact embedState_stack_frame negateReg negateStack d b 2 (by decide)
  · exact embedState_stack_frame negateReg negateStack d b 3 (by decide)
  · exact embedState_stack_frame negateReg negateStack d b 4 (by decide)
  · exact embedState_stack negateReg negateStack d b negateStack_injective 2
  · exact embedState_stack negateReg negateStack d b negateStack_injective 3
  · exact (embedState_stack negateReg negateStack d b negateStack_injective 0).trans hq.symm
  · exact embedState_register_frame negateReg negateStack d b 7 (by decide)
  · exact embedState_register_frame negateReg negateStack d b 8 (by decide)
  · exact embedState_register_frame negateReg negateStack d b 9 (by decide)

theorem encodedClause_records (C : List ℕ) :
    encodedClause C = Encoding.encodeList id (literalRecords C) := by
  induction C with
  | nil => rfl
  | cons c C ih => simpa [encodedClause, literalRecords, Encoding.encodeList] using ih

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete negated singleton generation for the disjoint B child.
The fixed routine consumes a unary literal-record list on stack 0 and prepends
its negated singleton clauses to the encoded formula on stack 2. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram

open BitProgram StructuredCalls

theorem copyQuery_eval (d : Data) (htmp : d.stacks 6 = []) :
    Eval copyQuery (7 * (d.stacks 1).length + 5) d (copied d) := by
  apply Eval.call
  simpa [copyQueryProgram, copied, StructuredProgram.State.withPC] using
    ListRegisterProgram.copy_run (r := 10) (s := 8) 1 7 6 0 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp

theorem seed_eval (d : Data) : Eval seed 2 d (seeded d) := by
  have h := (Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.set (r := 10) (s := 8) 0 false) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push 3 0)
      ((StructuredProgram.Atom.set 0 false).eval d)))
  simpa [seed, RecordPrograms.atom, seeded, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

theorem innerStack_injective : Function.Injective innerStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [innerStack]

theorem innerEmit_eval (bits : List Bool) (d : Data)
    (hq : d.stacks 1 = bits.reverse) :
    Eval innerEmit (5 * bits.length + 7) d (innerResult bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) (d.regs 9)
    (d.stacks 0) (d.stacks 6) (d.stacks 3) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 9)
    (d.stacks 0) (d.stacks 6) (true :: (Encoding.frame bits ++ d.stacks 3)) []
  have ha : embedState ExecLiteralDedupProgram.emitReg innerStack d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _
      ExecLiteralDedupProgram.emitReg_injective innerStack_injective
    · intro i
      fin_cases i <;> simp [a, ExecLiteralDedupProgram.emitReg,
        SubexpNormalizeProgram.filterState]
    · intro i _
      rfl
    · intro i
      fin_cases i <;> simp [a, innerStack, SubexpNormalizeProgram.filterState, hq]
    · intro i _
      rfl
  have hb : embedState ExecLiteralDedupProgram.emitReg innerStack d b = innerResult bits d := by
    apply embedState_eq_of_ports _ _ _ _ _
      ExecLiteralDedupProgram.emitReg_injective innerStack_injective
    · intro i
      fin_cases i <;> simp [b, innerResult, ExecLiteralDedupProgram.emitReg,
        SubexpNormalizeProgram.filterState]
    · intro i hi
      have h7 : i ≠ 7 := fun h => hi ⟨0, h.symm⟩
      have h8 : i ≠ 8 := fun h => hi ⟨1, h.symm⟩
      simp [innerResult, h7, h8]
    · intro i
      fin_cases i <;> simp [b, innerResult, innerStack,
        SubexpNormalizeProgram.filterState]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨2, h.symm⟩
      simp [innerResult, h1, h3]
  have he := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram
    ExecLiteralDedupProgram.emitReg innerStack d
    ExecLiteralDedupProgram.emitReg_injective innerStack_injective
    (SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 6)
      (d.stacks 3) (d.regs 7) (d.regs 8) (d.regs 9))
  change Eval innerEmit (5 * bits.length + 7)
    (embedState _ _ d a) (embedState _ _ d b) at he
  simpa only [ha, hb] using he

theorem transferClause_eval (d : Data) :
    Eval transferClause (3 * (d.stacks 3).length + 3) d (transferred d) := by
  apply Eval.call
  simpa [transferClauseProgram, transferred, StructuredProgram.State.withPC] using
    ListRegisterProgram.transfer_run (r := 10) (s := 8) 3 1 0 1
      (by decide) (by decide) d.regs d.stacks

theorem select_eval (d : Data) : Eval select 1 d (selected d) := by
  simpa [select, RecordPrograms.atom, selected, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using
    Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 9 true) d)

theorem callback_eval (c : ℕ) (d : Data)
    (hquery : d.stacks 1 = (Encoding.encodeNat c).reverse)
    (hclean : ExecLiteralDedupProgram.Clean d) :
    ∃ t ≤ 200 * ((Encoding.encodeNat c).length + 1), ∃ e : Data,
      Eval callback t d e ∧ ExecLiteralDedupProgram.Clean e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame (clauseCode [SubexpFrontend.negateCode c]) ++
        d.stacks 2) ∧ e.regs 7 = false ∧ e.regs 8 = true ∧ e.regs 9 = false := by
  rcases hclean with ⟨h3, h4, h5, h6, h7⟩
  let a := ExecCNFSubset.cleared 1 (copied d)
  have ha7 : a.stacks 7 = (Encoding.encodeNat c).reverse := by
    simp [a, StackRoutines.clearStacks, copied,
      StackRoutines.copyStacks, hquery, h7]
  obtain ⟨b, hb, hb1, hb0, hb2, hb3, hb4, hb5, hb6, hb7, _, _, _⟩ :=
    SubexpTautologyProgram.negateQuery_eval c a ha7
      (by simp [a, StackRoutines.clearStacks])
      (by simp [a, StackRoutines.clearStacks, copied,
        StackRoutines.copyStacks, h5])
      (by simp [a, StackRoutines.clearStacks, copied,
        StackRoutines.copyStacks, h6])
  let q := seeded (ExecCNFSubset.cleared 7 b)
  let bits := Encoding.encodeNat (SubexpFrontend.negateCode c)
  let w := innerResult bits q
  let z := selected (transferred w)
  have hq1 : q.stacks 1 = bits.reverse := by
    simpa [q, bits, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks] using hb1
  have hq3 : q.stacks 3 = [false] := by
    simp [q, seeded, StackRoutines.clearStacks, hb3,
      a, copied, StackRoutines.copyStacks, h3]
  have hw3 : w.stacks 3 = clauseCode [SubexpFrontend.negateCode c] := by
    simp [w, innerResult, hq3, clauseCode, SubexpTautologyProgram.encodedClause,
      Encoding.encodeList, bits]
  have hz1 : z.stacks 1 = (clauseCode [SubexpFrontend.negateCode c]).reverse := by
    have hw1 : w.stacks 1 = [] := by simp [w, innerResult]
    simpa [z, selected, transferred, StackRoutines.transferStacks, hw1] using
      congrArg List.reverse hw3
  obtain ⟨e, he, he0, he1, he2, he3, he4, he5, he6, he7, hr7, hr8, hr9⟩ :=
    ExecLiteralDedupProgram.emitCall_eval true (clauseCode [SubexpFrontend.negateCode c]) z
      hz1 (by simp [z, selected])
  let t := (7 * (d.stacks 1).length + 5) +
    ((2 * ((copied d).stacks 1).length + 3) +
    (SubexpNegatedQueryProgram.steps c + ((2 * (b.stacks 7).length + 3) +
    (2 + ((5 * bits.length + 7) + ((3 * (w.stacks 3).length + 3) +
    (1 + (SubexpNormalizeProgram.emitIfSelectedSteps true
      (clauseCode [SubexpFrontend.negateCode c]) + 1))))))))
  refine ⟨t, ?_, e, ?_, ?_, ?_, he1, ?_, hr7, hr8, hr9⟩
  · have hn := SubexpNegatedQueryProgram.steps_le c
    have hbits : bits.length ≤ (Encoding.encodeNat c).length + 1 := by
      dsimp [bits]
      simpa only [Encoding.length_encodeNat] using
        Nat.add_le_add_right (SubexpNegatedQueryProgram.negateCode_le c) 1
    have hc : (clauseCode [SubexpFrontend.negateCode c]).length = 2 * bits.length + 3 := by
      simp [clauseCode, SubexpTautologyProgram.encodedClause, bits]
    have hcopyLen : ((copied d).stacks 1).length = (Encoding.encodeNat c).length := by
      simp [copied, StackRoutines.copyStacks, hquery]
    simp only [t, hquery, hcopyLen, hb7, ha7, hw3, List.length_reverse,
      SubexpNormalizeProgram.emitIfSelectedSteps, ite_true, if_true]
    rw [hc]
    omega
  · exact (copyQuery_eval d h6).seq ((ExecCNFSubset.clear_eval 1 (copied d)).seq
      (hb.seq ((ExecCNFSubset.clear_eval 7 b).seq ((seed_eval _).seq
        ((innerEmit_eval bits q hq1).seq ((transferClause_eval w).seq
          ((select_eval (transferred w)).seq he)))))))
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [z, selected, transferred, StackRoutines.transferStacks] using he3
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb4,
        a, copied, StackRoutines.copyStacks, h4] using he4
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb5] using he5
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb6] using he6
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks] using he7
  · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
      q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb0,
      a, copied, StackRoutines.copyStacks] using he0
  · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
      q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb2,
      a, copied, StackRoutines.copyStacks] using he2

theorem callback_contract :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (fun bits => 200 * (bits.length + 1)) ExecLiteralDedupProgram.Clean
      (fun bits a b => b.stacks 2 = true :: (Encoding.frame (unitCode bits) ++ a.stacks 2))
      (fun bits => ∃ c, bits = Encoding.encodeNat c) := by
  intro bits tail base hbits hbase
  obtain ⟨c, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail (Encoding.encodeNat c).reverse
  have hd1 : d.stacks 1 = (Encoding.encodeNat c).reverse := by
    simp [d, RecordPrograms.state]
  have hd : ExecLiteralDedupProgram.Clean d := by
    simpa [d] using hbase
  obtain ⟨t, ht, e, he, hclean, h0, h1, h2, h7, h8, h9⟩ := callback_eval c d hd1 hd
  have h0' : e.stacks 0 = tail := by
    simpa [d, ports, RecordPrograms.state, ExecLiteralDedupProgram.ports] using h0
  have hend : RecordPrograms.state ports e false true false tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ h7 h8 h9 h0' h1
  refine ⟨t, e, ht, hclean, ?_, ?_⟩
  · simpa [d] using h2
  · rw [hend]
    exact he

theorem fold_units (H : List ℕ) (F : List (List ℕ)) :
    (H.map Encoding.encodeNat).foldl
      (fun acc bits => true :: (Encoding.frame (unitCode bits) ++ acc)) (formulaCode F) =
      formulaCode (units H ++ F) := by
  induction H generalizing F with
  | nil => rfl
  | cons c H ih =>
      simp only [List.map_cons, List.foldl_cons, unitCode_encodeNat]
      change (H.map Encoding.encodeNat).foldl _
        (formulaCode ([SubexpFrontend.negateCode c] :: F)) = _
      rw [ih]
      simp [units, List.reverse_cons, List.map_append, List.append_assoc]

theorem command_eval (H : List ℕ) (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = clauseCode H) (houtput : d.stacks 2 = formulaCode F)
    (hpayload : d.stacks 1 = []) (hclean : ExecLiteralDedupProgram.Clean d) :
    ∃ t, t + 1 ≤ 417 * ((clauseCode H).length + 1) ∧ ∃ e : Data,
      Eval command t d e ∧ e.stacks 2 = formulaCode (units H ++ F) ∧
      (∀ i : Fin 8, i ≠ 2 → e.stacks i = []) := by
  let records := H.map Encoding.encodeNat
  have hrecords : ∀ bits ∈ records, ∃ c, bits = Encoding.encodeNat c := by
    intro bits hbits
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hbits
    exact ⟨c, rfl⟩
  have hencode : Encoding.encodeList id records = clauseCode H :=
    (SubexpTautologyProgram.encodedClause_records H).symm
  have hstart : RecordPrograms.state ports d (d.regs 7) (d.regs 8) (d.regs 9)
      (Encoding.encodeList id records ++ []) [] = d :=
    RecordPrograms.state_eq_self ports d _ _ _ _ _ rfl rfl rfl
      (by simpa only [List.append_nil, hencode] using hsource) hpayload
  obtain ⟨t, next, ht, hn, hvisits, hrun⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (fun bits => 200 * (bits.length + 1))
    ExecLiteralDedupProgram.Clean
    (fun bits a b => b.stacks 2 = true :: (Encoding.frame (unitCode bits) ++ a.stacks 2))
    (fun bits => ∃ c, bits = Encoding.encodeNat c) callback_contract
    records [] d hrecords hclean (d.regs 7) (d.regs 8) (d.regs 9)
  have hunread : RecordPrograms.unread (fun _ => false) records [] = [] := by
    induction records with
    | nil => rfl
    | cons b rest ih => simp [RecordPrograms.unread, ih]
  have hany : records.any (fun _ => false) = false := by simp
  have hfold := hvisits.fold_of_false (fun _ _ => rfl) (fun a => a.stacks 2)
    (fun acc bits => true :: (Encoding.frame (unitCode bits) ++ acc))
    (fun _ _ _ h => h)
  have hout : next.stacks 2 = formulaCode (units H ++ F) := by
    rw [houtput] at hfold
    exact hfold.trans (fold_units H F)
  let e := RecordPrograms.state ports next false true false [] []
  have hb := RecordPrograms.program_budget_le_input
    (fun bits => 200 * (bits.length + 1)) records 200 200 (by
      intro bits _
      omega)
  change 4 + RecordPrograms.budget (fun bits => 200 * (bits.length + 1)) records ≤
    417 * ((Encoding.encodeList id records).length + 1) at hb
  rw [hencode] at hb
  refine ⟨t, by omega, e, ?_, ?_, ?_⟩
  · simpa only [hstart, hunread, hany, command] using hrun
  · simpa [e] using hout
  · rcases hn with ⟨h3, h4, h5, h6, h7⟩
    intro i hi
    fin_cases i <;> simp_all [e, ports, RecordPrograms.state, ExecLiteralDedupProgram.ports]

theorem program_runsIn (H : List ℕ) (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = clauseCode H) (houtput : d.stacks 2 = formulaCode F)
    (hpayload : d.stacks 1 = []) (hclean : ExecLiteralDedupProgram.Clean d) :
    ∃ e : Data, e.stacks 2 = formulaCode (units H ++ F) ∧
      (∀ i : Fin 8, i ≠ 2 → e.stacks i = []) ∧
      RunsIn program (417 * ((clauseCode H).length + 1))
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨t, ht, e, he, hout, hscratch⟩ := command_eval H F d hsource houtput hpayload hclean
  exact ⟨e, hout, hscratch, t + 1, ht, compiled_halt_trace he 0 2⟩

theorem output_length_le (H : List ℕ) (F : List (List ℕ)) :
    (formulaCode (units H ++ F)).length ≤
      (formulaCode F).length + 8 * (clauseCode H).length := by
  induction H generalizing F with
  | nil => simp [units]
  | cons c H ih =>
      have hneg : (Encoding.encodeNat (SubexpFrontend.negateCode c)).length ≤
          (Encoding.encodeNat c).length + 1 := by
        simpa only [Encoding.length_encodeNat] using
          Nat.add_le_add_right (SubexpNegatedQueryProgram.negateCode_le c) 1
      have hrec := ih ([SubexpFrontend.negateCode c] :: F)
      have heq : units (c :: H) ++ F = units H ++ ([SubexpFrontend.negateCode c] :: F) := by
        simp [units, List.reverse_cons, List.map_append, List.append_assoc]
      rw [heq]
      simp only [formulaCode, Encoding.length_encodeList_cons] at hrec ⊢
      simp only [clauseCode, SubexpTautologyProgram.encodedClause,
        Encoding.length_encodeList_cons, Encoding.length_encodeList_nil] at hrec ⊢
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

theorem unitRegister_injective : Function.Injective unitRegister :=
  Fin.castAdd_injective 10 5

theorem unitStack_injective : Function.Injective unitStack := by decide

theorem copyCore_eval (d : State 15 16) (h0 : d.stacks 0 = [])
    (h10 : d.stacks 10 = []) :
    Eval copyCore (7 * (d.stacks 9).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 (d.stacks 9)⟩ := by
  have h := ListRegisterProgram.copy_run (r := 15) (s := 16) 9 0 10 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h10
  apply Eval.call
  simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, h0, List.append_nil] using h

theorem prepareB_eval (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
    (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
    (hready : ExecCoreChildProgram.InputReady d) :
    ∃ t ≤ 430 * ExecCoreChildProgram.inputVolume F S H, ∃ e : State 15 16,
      Eval prepareB t d e ∧ ExecCoreChildProgram.InputReady e ∧
      e.stacks 9 = ExecCoreChildProgram.clauseCode H ∧
      e.stacks 12 = ExecCoreChildProgram.formulaCode S ∧
      e.stacks 13 = ExecCoreChildProgram.formulaCode
        (negatedUnits SubexpFrontend.negateCode H ++ F) := by
  let a : State 15 16 :=
    ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 (d.stacks 9)⟩
  let small : State 10 8 := ⟨a.regs ∘ unitRegister, a.stacks ∘ unitStack⟩
  have hl0 : small.stacks 0 = NegatedCoreProgram.clauseCode H := by
    simpa [small, a, unitStack, NegatedCoreProgram.clauseCode,
      ExecCoreChildProgram.clauseCode, SubexpTautologyProgram.encodedClause,
      ExecCleanLiteralsProgram.clauseCode] using hcore
  have hl2 : small.stacks 2 = NegatedCoreProgram.formulaCode F := by
    change small.stacks 2 = Encoding.encodeList ExecCleanLiteralsProgram.clauseCode F
    change d.stacks 13 = Encoding.encodeList ExecCleanLiteralsProgram.clauseCode F at hsource
    simpa [small, a, unitStack] using hsource
  have hl1 : small.stacks 1 = [] := by
    simpa [small, a, unitStack] using hready 1 (by decide) (by decide) (by decide)
  have hlclean : ExecLiteralDedupProgram.Clean small := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [small, Function.comp_apply, unitStack, a]
      first
      | exact hready 2 (by decide) (by decide) (by decide)
      | exact hready 3 (by decide) (by decide) (by decide)
      | exact hready 4 (by decide) (by decide) (by decide)
      | exact hready 5 (by decide) (by decide) (by decide)
      | exact hready 6 (by decide) (by decide) (by decide)
  obtain ⟨b, hbout, hbclean, t, ht, htrace⟩ :=
    NegatedCoreProgram.program_runsIn H F small hl0 hl2 hl1 hlclean
  have ha : embedState unitRegister unitStack a small = a := by
    apply embedState_eq_of_ports _ _ _ _ _ unitRegister_injective unitStack_injective
    · intro i; rfl
    · intro i _; rfl
    · intro i; rfl
    · intro i _; rfl
  let e := embedState unitRegister unitStack a b
  have he := eval_call_lifted NegatedCoreProgram.program unitRegister unitStack a
    unitRegister_injective unitStack_injective htrace
  rw [ha] at he
  have heport (i : Fin 8) : e.stacks (unitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ unitStack_injective i
  have heready : ExecCoreChildProgram.InputReady e := by
    intro i hi9 hi12 hi13
    by_cases hi : ∃ j, unitStack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (heport j).trans (hbclean j (fun hj => hi13 (hj ▸ rfl)))
    · have hi0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      rw [embedState_stack_frame _ _ _ _ _ hi]
      simpa [a, hi0] using hready i hi9 hi12 hi13
  have he9 : e.stacks 9 = ExecCoreChildProgram.clauseCode H := by
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    simpa [a] using hcore
  have he12 : e.stacks 12 = ExecCoreChildProgram.formulaCode S := by
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    simpa [a] using hselected
  have he13 : e.stacks 13 = ExecCoreChildProgram.formulaCode
      (negatedUnits SubexpFrontend.negateCode H ++ F) := by
    exact (heport 2).trans hbout
  have hcopy := copyCore_eval d (hready 0 (by decide) (by decide) (by decide))
    (hready 10 (by decide) (by decide) (by decide))
  refine ⟨7 * (d.stacks 9).length + 5 + t, ?_, e,
    hcopy.seq he, heready, he9, he12, he13⟩
  rw [hcore]
  change t ≤ 417 * ((ExecCoreChildProgram.clauseCode H).length + 1) at ht
  unfold ExecCoreChildProgram.inputVolume
  omega

theorem preparedB_volume_le (F S : List (List ℕ)) (H : List ℕ) :
    ExecPetalChildProgram.inputVolume
        (negatedUnits SubexpFrontend.negateCode H ++ F) S H ≤
      5 * ExecCoreChildProgram.inputVolume F S H := by
  have h := NegatedCoreProgram.output_length_le H F
  change (ExecCoreChildProgram.formulaCode
      (negatedUnits SubexpFrontend.negateCode H ++ F)).length ≤
    (ExecCoreChildProgram.formulaCode F).length +
      8 * (ExecCoreChildProgram.clauseCode H).length at h
  unfold ExecPetalChildProgram.inputVolume ExecCoreChildProgram.inputVolume
  dsimp only [ExecPetalChildProgram.formulaCode, ExecPetalChildProgram.clauseCode,
    ExecCoreChildProgram.formulaCode, ExecCoreChildProgram.clauseCode] at h ⊢
  omega

theorem commandB_eval (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
    (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
    (hready : ExecCoreChildProgram.InputReady d) :
    ∃ t ≤ 500000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2, ∃ e : State 15 16,
      Eval commandB t d e ∧ SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = ExecCoreChildProgram.formulaCode
        (resultB SubexpFrontend.negateCode F S H) := by
  obtain ⟨t, ht, a, ha, haready, ha9, ha12, ha13⟩ :=
    prepareB_eval F S H d hcore hselected hsource hready
  obtain ⟨u, hu, e, he, heready, he13⟩ := ExecPetalChildProgram.command_eval
    (negatedUnits SubexpFrontend.negateCode H ++ F) S H a ha9 ha12 ha13 haready
  refine ⟨t + u, ?_, e, ha.seq he, heready, he13⟩
  have hvol := preparedB_volume_le F S H
  have hsq := Nat.pow_le_pow_left hvol 2
  have hv : 1 ≤ ExecCoreChildProgram.inputVolume F S H := by
    unfold ExecCoreChildProgram.inputVolume
    omega
  nlinarith [Nat.mul_le_mul_left (ExecCoreChildProgram.inputVolume F S H) hv]

theorem programB_runsIn_oai (F S : List (List ℕ)) (H : List ℕ) (d : State 15 16)
    (hcore : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hselected : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hsource : d.stacks 13 = ExecCoreChildProgram.formulaCode F)
    (hready : ExecCoreChildProgram.InputReady d) :
    ∃ e : State 15 16, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = ExecCoreChildProgram.formulaCode
        (resultB SubexpFrontend.negateCode F S H) ∧
      RunsIn programB (600000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
        (d.withPC (some programB.entry)) (e.withPC none) := by
  obtain ⟨t, ht, e, he, heready, he13⟩ := commandB_eval F S H d hcore hselected hsource hready
  refine ⟨e, heready, he13, t + 1, ?_, compiled_halt_trace he 13 13⟩
  have hv : 0 < ExecCoreChildProgram.inputVolume F S H := by
    unfold ExecCoreChildProgram.inputVolume
    omega
  have hp := pow_pos hv 2
  omega

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn_oai
