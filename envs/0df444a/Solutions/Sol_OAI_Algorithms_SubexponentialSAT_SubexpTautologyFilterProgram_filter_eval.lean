-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.filter_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:41:19.663487+00:00
-- url     : https://prove2.me/submissions/7ebd9b9c-78b2-4be8-9f7a-bebf80731dd7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S111

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem copyClause_eval (d : Data) (h4 : d.stacks 4 = []) :
    Eval copyClause (7 * (d.stacks 2).length + 5) d (ExecCNFSubset.copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 10) (s := 8) 2 3 4 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h4
  have hh := StackRoutines.halt_after_trace copyClauseProgram h 7 rfl rfl
  apply Eval.call
  simpa [copyClauseProgram, StackRoutines.copyResult, StackRoutines.copyStacks,
    readRegs, ExecCNFSubset.copied, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem encodedClause_records (C : List ℕ) :
    encodedClause C = Encoding.encodeList id (literalRecords C) := by
  induction C with
  | nil => rfl
  | cons c C ih => simpa [encodedClause, literalRecords, Encoding.encodeList] using ih

theorem member_opposite (C : List ℕ) (c : ℕ) :
    decide (Encoding.encodeNat (SubexpFrontend.negateCode c) ∈ literalRecords C) =
      ExecCNF.contains (SubexpFrontend.negateCode c) C := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, literalRecords, List.mem_map, ExecCNF.contains_true]
  constructor
  · rintro ⟨x, hx, he⟩
    exact Encoding.encodeNat_injective he ▸ hx
  · intro h
    exact ⟨_, h, rfl⟩

theorem any_oppositePresent (C : List ℕ) :
    (literalRecords C).any (oppositePresent C) =
      ExecCNF.tautology SubexpFrontend.negateCode C := by
  simp [literalRecords, List.any_map, ExecCNF.tautology, Function.comp_def]

theorem mark_eval (d : Data) :
    Eval (RecordPrograms.atom (.copy 9 4)) 1 d (mark d) := by
  have h : (StructuredProgram.Atom.copy (r := 10) (s := 8) 9 4).eval d = mark d := rfl
  rw [← h]
  exact .base (.atom _ _)

theorem callback_eval (C : List ℕ) (c : ℕ) (d : Data)
    (hquery : d.stacks 7 = (Encoding.encodeNat c).reverse) (valid : invariant C d) :
    ∃ n ≤ perLiteralCost C (Encoding.encodeNat c), ∃ e : Data,
      Eval callback n d e ∧ invariant C e ∧
      e.regs 9 = ExecCNF.contains (SubexpFrontend.negateCode c) C ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 7 = [] ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 := by
  rcases valid with ⟨hd2, hd1, hd3, hd4, hd5, hd6⟩
  obtain ⟨a, hneg, ha1, ha0, ha2, ha3, ha4, ha5, ha6, ha7, har7, har8, har9⟩ :=
    negateQuery_eval c d hquery hd1 hd5 hd6
  have hsrc : (ExecCNFSubset.copied a).stacks 3 =
      Encoding.encodeList id (literalRecords C) := by
    simp [ StackRoutines.copyStacks, ha2, hd2, ha3, hd3,
      encodedClause_records]
  have hq : (ExecCNFSubset.copied a).stacks 1 =
      (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks] using ha1
  have ho : (ExecCNFSubset.copied a).stacks 4 = [] := by
    simp [ StackRoutines.copyStacks, ha4, hd4]
  have hc : (ExecCNFSubset.copied a).stacks 5 = [] := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks] using ha5
  have ht : (ExecCNFSubset.copied a).stacks 6 = [] := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks] using ha6
  obtain ⟨m, hm, b, hmem, hbans, hbres, hb4, hb1, hb5, hb6,
      hb0, hb2, hb7, hbr7, hbr8, hbr9⟩ :=
    ExecCNFSubset.memberCall_eval (Encoding.encodeNat (SubexpFrontend.negateCode c))
      (literalRecords C) (ExecCNFSubset.copied a) hsrc hq ho hc ht
  let result := ExecCNFSubset.cleared 7 (ExecCNFSubset.cleared 4
    (ExecCNFSubset.cleared 3 (ExecCNFSubset.cleared 1 (mark b))))
  let steps := SubexpNegatedQueryProgram.steps c +
    ((7 * (a.stacks 2).length + 5) +
    (m + (1 + ((2 * (b.stacks 1).length + 3) +
      ((2 * (b.stacks 3).length + 3) +
      ((2 * (b.stacks 4).length + 3) + (2 * (b.stacks 7).length + 3)))))))
  have hb7' : b.stacks 7 = (Encoding.encodeNat c).reverse := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks, ha7, hquery] using hb7
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn := SubexpNegatedQueryProgram.steps_le c
    have hlen : (Encoding.encodeNat (SubexpFrontend.negateCode c)).length ≤
        (Encoding.encodeNat c).length + 1 := by
      simpa only [Encoding.length_encodeNat] using
        Nat.add_le_add_right (SubexpNegatedQueryProgram.negateCode_le c) 1
    rw [← encodedClause_records] at hm hbres
    dsimp [steps, perLiteralCost]
    rw [ha2, hd2, hb1, hb4, hb7']
    simp only [List.length_reverse, List.length_cons, List.length_nil]
    nlinarith
  · apply Eval.seq hneg
    apply Eval.seq (copyClause_eval a (ha4.trans hd4))
    apply Eval.seq hmem
    apply Eval.seq (mark_eval b)
    apply Eval.seq (ExecCNFSubset.clear_eval 1 (mark b))
    apply Eval.seq (ExecCNFSubset.clear_eval 3 (ExecCNFSubset.cleared 1 (mark b)))
    apply Eval.seq (ExecCNFSubset.clear_eval 4
      (ExecCNFSubset.cleared 3 (ExecCNFSubset.cleared 1 (mark b))))
    simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark] using
      ExecCNFSubset.clear_eval 7 (ExecCNFSubset.cleared 4
        (ExecCNFSubset.cleared 3 (ExecCNFSubset.cleared 1 (mark b))))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark,
        ExecCNFSubset.copied, StackRoutines.copyStacks, ha2, hd2] using hb2
    · simp [result, StackRoutines.clearStacks, mark]
    · simp [result, StackRoutines.clearStacks, mark]
    · simp [result, StackRoutines.clearStacks, mark]
    · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark] using hb5
    · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark] using hb6
  · simp [result, readRegs, mark, hbans, member_opposite]
  · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark,
      ExecCNFSubset.copied, StackRoutines.copyStacks, ha0] using hb0
  · simp [result, StackRoutines.clearStacks]
  · simpa [result, ExecCNFSubset.cleared, readRegs, mark,
      ExecCNFSubset.copied, har7] using hbr7
  · simpa [result, ExecCNFSubset.cleared, readRegs, mark,
      ExecCNFSubset.copied, har8] using hbr8

theorem callback_contract (C : List ℕ) :
    RecordPrograms.CallbackContractOn ports callback (oppositePresent C)
      (perLiteralCost C) (invariant C) UnaryPayload := by
  intro bits tail base hbits hbase
  obtain ⟨c, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail (Encoding.encodeNat c).reverse
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state, ports]
  have hd7 : d.stacks 7 = (Encoding.encodeNat c).reverse := by
    simp [d, RecordPrograms.state, ports]
  have hr7 : d.regs 7 = false := by simp [d, RecordPrograms.state, ports]
  have hr8 : d.regs 8 = true := by simp [d, RecordPrograms.state, ports]
  have hv : invariant C d := by
    simpa [invariant, d, RecordPrograms.state, ports] using hbase
  obtain ⟨n, hn, e, he, hv, ha, hs, hp, h7, h8⟩ := callback_eval C c d hd7 hv
  have heState : RecordPrograms.state ports e false true
      (oppositePresent C (Encoding.encodeNat c)) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ (h7.trans hr7) (h8.trans hr8)
      (by simpa [ports] using ha) (hs.trans hd0) hp
  refine ⟨n, e, hn, hv, ?_⟩
  rw [heState]
  exact he

theorem valid_literalRecords (C : List ℕ) :
    ∀ bits ∈ literalRecords C, UnaryPayload bits := by
  intro bits h
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
  exact ⟨c, rfl⟩

theorem budget_le (C : List ℕ) (records : List (List Bool)) :
    3 + RecordPrograms.budget (perLiteralCost C) records ≤
      110 * ((encodedClause C).length + 1) * (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons bits records ih =>
    have hstep : 6 * bits.length + perLiteralCost C bits + 7 ≤
        110 * ((encodedClause C).length + 1) * (2 * bits.length + 2) := by
      unfold perLiteralCost
      nlinarith
    simp only [RecordPrograms.budget, Encoding.length_encodeList_cons, id_eq]
    calc
      3 + (6 * bits.length + perLiteralCost C bits + 7 +
          RecordPrograms.budget (perLiteralCost C) records)
          = (6 * bits.length + perLiteralCost C bits + 7) +
            (3 + RecordPrograms.budget (perLiteralCost C) records) := by omega
      _ ≤ 110 * ((encodedClause C).length + 1) * (2 * bits.length + 2) +
          110 * ((encodedClause C).length + 1) * (Encoding.encodeList id records).length :=
        Nat.add_le_add hstep ih
      _ = 110 * ((encodedClause C).length + 1) *
          (2 * bits.length + 2 + (Encoding.encodeList id records).length) := by ring

theorem initialize_eval (d : Data) (h4 : d.stacks 4 = []) :
    Eval initializeCmd (7 * (d.stacks 0).length + 5) d (initialized d) := by
  have h := StackRoutines.copyProgram_trace (r := 10) (s := 8) 0 2 4 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h4
  have hh := StackRoutines.halt_after_trace initializeProgram h 7 rfl rfl
  apply Eval.call
  simpa [initializeProgram, StackRoutines.copyResult, StackRoutines.copyStacks,
    readRegs, initialized, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem finish_eval (d : Data) (h1 : d.stacks 1 = []) :
    Eval finish (2 * (d.stacks 0).length + 4) d (finished d) := by
  have hpush : Eval (RecordPrograms.atom (.push 1 9)) 1
      (ExecCNFSubset.cleared 0 d) (finished d) := by
    have h : (StructuredProgram.Atom.push (r := 10) (s := 8) 1 9).eval
        (ExecCNFSubset.cleared 0 d) = finished d := by
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
        finished, StackRoutines.clearStacks, readRegs, h1]
    rw [← h]
    exact .base (.atom _ _)
  simpa [finish, Nat.add_assoc] using (ExecCNFSubset.clear_eval 0 d).seq hpush

/-- Complete clause testing, including its actual initialization and cleanup.
The clause remains on stack 2, and stack 1 contains the Boolean answer. -/
theorem tautology_eval (C : List ℕ) (d : Data)
    (hsource : d.stacks 0 = encodedClause C) (hready : Ready d) :
    ∃ n ≤ 199 * ((encodedClause C).length + 1) ^ 2, ∃ e : Data,
      Eval tautology n d e ∧
      e.regs 9 = ExecCNF.tautology SubexpFrontend.negateCode C ∧
      e.stacks 1 = [ExecCNF.tautology SubexpFrontend.negateCode C] ∧
      e.stacks 2 = encodedClause C ∧
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → e.stacks i = []) := by
  let a := initialized d
  have hinit := initialize_eval d (hready 4 (by decide))
  have ha0 : a.stacks 0 = encodedClause C := by
    simpa [a, initialized, StackRoutines.copyStacks] using hsource
  have ha7 : a.stacks 7 = [] := by
    simpa [a, initialized, StackRoutines.copyStacks] using hready 7 (by decide)
  have ha : invariant C a := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [a, initialized, StackRoutines.copyStacks, hsource,
        hready 1 (by decide), hready 2 (by decide), hready 3 (by decide),
        hready 4 (by decide), hready 5 (by decide), hready 6 (by decide)]
  have haState : RecordPrograms.state ports a (a.regs 7) (a.regs 8) (a.regs 9)
      (Encoding.encodeList id (literalRecords C) ++ []) [] = a :=
    RecordPrograms.state_eq_self ports a _ _ _ _ _ rfl rfl rfl
      (by simpa [ports, ← encodedClause_records] using ha0) ha7
  obtain ⟨m, b, hm, hb, hloop⟩ := RecordPrograms.iterate_run_on ports callback
    (oppositePresent C) (perLiteralCost C) (invariant C) UnaryPayload
    (callback_contract C) (literalRecords C) [] a (valid_literalRecords C) ha
    (a.regs 7) (a.regs 8) (a.regs 9)
  rw [haState, any_oppositePresent] at hloop
  let middle := RecordPrograms.state ports b false true
    (ExecCNF.tautology SubexpFrontend.negateCode C)
    (RecordPrograms.unread (oppositePresent C) (literalRecords C) []) []
  have hm1 : middle.stacks 1 = [] := by
    simpa [middle, RecordPrograms.state, ports] using hb.2.1
  have hfinish := finish_eval middle hm1
  let n := (7 * (d.stacks 0).length + 5) + (m + (2 * (middle.stacks 0).length + 4))
  refine ⟨n, ?_, finished middle, ?_, ?_, ?_, ?_, ?_⟩
  · have hbudget := budget_le C (literalRecords C)
    rw [← encodedClause_records] at hbudget
    have hres := ExecCNFSubset.unread_length_le (oppositePresent C) (literalRecords C)
    rw [← encodedClause_records] at hres
    have hm0 : middle.stacks 0 =
        RecordPrograms.unread (oppositePresent C) (literalRecords C) [] := by
      simp [middle, RecordPrograms.state, ports]
    dsimp [n]
    rw [hsource, hm0]
    nlinarith
  · exact hinit.seq (hloop.seq hfinish)
  · simp [finished, middle, readRegs, RecordPrograms.state, ports]
  · simp [finished, middle, RecordPrograms.state, ports]
  · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
      RecordPrograms.state, ports] using hb.1
  · intro i hi1 hi2
    fin_cases i
    · simp [finished, StackRoutines.clearStacks]
    · exact (hi1 rfl).elim
    · exact (hi2 rfl).elim
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.1
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.2.1
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.2.2.1
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.2.2.2
    · simp [finished, middle, StackRoutines.clearStacks,
        RecordPrograms.state, ports]

theorem tautology_runsIn (C : List ℕ) (d : Data)
    (hsource : d.stacks 0 = encodedClause C) (hready : Ready d) :
    ∃ e : Data,
      e.regs 9 = ExecCNF.tautology SubexpFrontend.negateCode C ∧
      e.stacks 1 = [ExecCNF.tautology SubexpFrontend.negateCode C] ∧
      e.stacks 2 = encodedClause C ∧
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → e.stacks i = []) ∧
      RunsIn program (200 * ((encodedClause C).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hr, ho, hc, hw⟩ := tautology_eval C d hsource hready
  refine ⟨e, hr, ho, hc, hw, n + 1, ?_, compiled_halt_trace he 0 1⟩
  have hpos : 0 < ((encodedClause C).length + 1) ^ 2 := pow_pos (by omega) _
  omega

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

open BitProgram StructuredCalls

theorem decodeFields_literalRecords (C : List ℕ) :
    decodeFields (SubexpTautologyProgram.literalRecords C) = some C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    change decodeFields (C.map Encoding.encodeNat) = some C at ih
    simp [SubexpTautologyProgram.literalRecords, decodeFields, ih]

@[simp] theorem decodeClause_encodedClause (C : List ℕ) :
    decodeClause (SubexpTautologyProgram.encodedClause C) = some C := by
  rw [SubexpTautologyProgram.encodedClause_records]
  change (do
    let (fields, rest) ← ProgramEncoding.readRecords
      (ProgramEncoding.encodeRecords (SubexpTautologyProgram.literalRecords C))
    if rest.isEmpty then decodeFields fields else none) = some C
  simp [decodeFields_literalRecords]

@[simp] theorem keepClause_encodedClause (C : List ℕ) :
    keepClause (SubexpTautologyProgram.encodedClause C) =
      !(ExecCNF.tautology SubexpFrontend.negateCode C) := by
  simp [keepClause]

theorem coreRegister_injective : Function.Injective coreRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 13 => i.val) h)

theorem coreStack_injective : Function.Injective coreStack := by
  intro i j h
  apply Fin.ext
  have he := congrArg (fun i : Fin 11 => i.val) h
  simp only [coreStack] at he
  omega

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

theorem coreCall_eval (C : List ℕ) (d : Data)
    (hsource : d.stacks 3 = SubexpTautologyProgram.encodedClause C)
    (hready : ∀ i : Fin 8, i ≠ 0 → d.stacks (coreStack i) = []) :
    ∃ n ≤ 200 * ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2,
      ∃ e : Data, Eval coreCall n d e ∧
      e.regs 9 = ExecCNF.tautology SubexpFrontend.negateCode C ∧
      e.stacks 4 = [ExecCNF.tautology SubexpFrontend.negateCode C] ∧
      e.stacks 5 = SubexpTautologyProgram.encodedClause C ∧
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → e.stacks (coreStack i) = []) ∧
      (∀ i : Fin 11, i.val < 3 → e.stacks i = d.stacks i) ∧
      (∀ i : Fin 13, 10 ≤ i.val → e.regs i = d.regs i) := by
  let a : SubexpTautologyProgram.Data :=
    ⟨d.regs ∘ coreRegister, d.stacks ∘ coreStack⟩
  have ha0 : a.stacks 0 = SubexpTautologyProgram.encodedClause C := hsource
  have ha : SubexpTautologyProgram.Ready a := hready
  obtain ⟨b, hbreg, hbout, hbclause, hbclear, n, hn, hbtrace⟩ :=
    SubexpTautologyProgram.tautology_runsIn C a ha0 ha
  let e := embedState coreRegister coreStack d b
  have he := eval_call_lifted SubexpTautologyProgram.program coreRegister coreStack d
    coreRegister_injective coreStack_injective hbtrace
  rw [embed_restricted _ _ coreRegister_injective coreStack_injective] at he
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (embedState_register coreRegister coreStack d b coreRegister_injective 9).trans hbreg
  · exact (embedState_stack coreRegister coreStack d b coreStack_injective 1).trans hbout
  · exact (embedState_stack coreRegister coreStack d b coreStack_injective 2).trans hbclause
  · intro i hi1 hi2
    exact (embedState_stack coreRegister coreStack d b coreStack_injective i).trans
      (hbclear i hi1 hi2)
  · intro i hi
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hval := congrArg (fun i : Fin 11 => i.val) hj
    simp only [coreStack] at hval
    omega
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hval := congrArg (fun i : Fin 13 => i.val) hj
    have hjlt := j.isLt
    simp only [coreRegister, Fin.val_castAdd] at hval
    omega

theorem transfer_eval (source target : Fin 11) (hne : source ≠ target) (d : Data) :
    Eval (transfer source target) (3 * (d.stacks source).length + 3)
      d (transferred source target d) := by
  have h := StackRoutines.transferProgram_trace (r := 13) (s := 11) source target 0 1
    hne (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace (transferProgram source target) h 3 rfl rfl
  apply Eval.call
  simpa [transferProgram, StackRoutines.transferResult, transferred,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem clear_eval (port : Fin 11) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace (r := 13) (s := 11) port 0 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace (clearProgram port) h 2 rfl rfl
  apply Eval.call
  simpa [clearProgram, StackRoutines.clearResult, cleared,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem emitRegister_injective : Function.Injective emitRegister := by
  intro i j h
  apply Fin.ext
  have he := congrArg (fun i : Fin 13 => i.val) h
  simp only [emitRegister] at he
  omega

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

theorem emitCall_eval (bits : List Bool) (d : Data) (hpayload : d.stacks 1 = bits.reverse) :
    ∃ e : Data,
      Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps (d.regs 12) bits + 1) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if d.regs 12 then true :: (Encoding.frame bits ++ d.stacks 2)
        else d.stacks 2) ∧
      (∀ i : Fin 11, 3 ≤ i.val → e.stacks i = d.stacks i) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a := SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) (d.regs 12)
    (d.stacks 0) (d.stacks 3) (d.stacks 2) bits.reverse
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 3)
    (if d.regs 12 then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) []
  have ha : a = ⟨d.regs ∘ emitRegister, d.stacks ∘ emitStack⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [
        SubexpPostfixControl.quadruple, emitStack, hpayload]
  let e := embedState emitRegister emitStack d b
  have he := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitRegister emitStack d emitRegister_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (d.regs 12) bits (d.stacks 0)
      (d.stacks 3) (d.stacks 2) (d.regs 10) (d.regs 11))
  change Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps (d.regs 12) bits + 1)
    (embedState emitRegister emitStack d a) e at he
  rw [ha, embed_restricted _ _ emitRegister_injective emitStack_injective] at he
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack emitRegister emitStack d b emitStack_injective 0
  · exact embedState_stack emitRegister emitStack d b emitStack_injective 3
  · exact embedState_stack emitRegister emitStack d b emitStack_injective 2
  · intro i hi
    by_cases h3 : i = 3
    · subst i
      exact embedState_stack emitRegister emitStack d b emitStack_injective 1
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [emitStack] at hj <;> subst i <;> omega
  · exact embedState_register emitRegister emitStack d b emitRegister_injective 0
  · exact embedState_register emitRegister emitStack d b emitRegister_injective 1
  · exact embedState_register emitRegister emitStack d b emitRegister_injective 2

theorem select_eval (d : Data) :
    Eval (RecordPrograms.atom (.bnot 12 9)) 1 d (selected d) := by
  have h : (StructuredProgram.Atom.bnot (r := 13) (s := 11) 12 9).eval d = selected d := rfl
  rw [← h]
  exact .base (.atom _ _)

theorem callback_eval (C : List ℕ) (d : Data)
    (hpayload : d.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse)
    (valid : invariant d) :
    ∃ n ≤ perClauseCost (SubexpTautologyProgram.encodedClause C), ∃ e : Data,
      Eval callback n d e ∧ invariant e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if keepClause (SubexpTautologyProgram.encodedClause C) then
        true :: (Encoding.frame (SubexpTautologyProgram.encodedClause C) ++ d.stacks 2)
        else d.stacks 2) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a := transferred 1 3 d
  have ha3 : a.stacks 3 = SubexpTautologyProgram.encodedClause C := by
    simp [a, transferred, StackRoutines.transferStacks, hpayload, valid 3 (by decide)]
  have haReady : ∀ i : Fin 8, i ≠ 0 → a.stacks (coreStack i) = [] := by
    intro i hi
    have hv : 0 < i.val := by
      have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    have hneq1 : coreStack i ≠ 1 := by
      intro h
      have := congrArg (fun j : Fin 11 => j.val) h
      simp only [coreStack] at this
      omega
    have hneq3 : coreStack i ≠ 3 := by
      intro h
      have := congrArg (fun j : Fin 11 => j.val) h
      simp only [coreStack] at this
      omega
    simpa [a, transferred, StackRoutines.transferStacks, hneq1, hneq3] using
      valid (coreStack i) (by simp [coreStack])
  obtain ⟨m, hm, b, hcore, hbreg, hb4, hb5, hbclear, hbframe, hbregs⟩ :=
    coreCall_eval C a ha3 haReady
  let c := transferred 5 1 b
  let f := selected (cleared 4 c)
  have hb1 : b.stacks 1 = [] := by
    simpa [a, transferred, StackRoutines.transferStacks] using hbframe 1 (by decide)
  have hc1 : c.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse := by
    simp [c, transferred, StackRoutines.transferStacks, hb1, hb5]
  have hc4 : c.stacks 4 = [ExecCNF.tautology SubexpFrontend.negateCode C] := by
    simpa [c, transferred, StackRoutines.transferStacks] using hb4
  have hf1 : f.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse := by
    simpa [f, selected, cleared, StackRoutines.clearStacks] using hc1
  have hf12 : f.regs 12 = !(ExecCNF.tautology SubexpFrontend.negateCode C) := by
    simp [f, selected, cleared, transferred, c, readRegs, hbreg]
  have hf0 : f.stacks 0 = d.stacks 0 := by
    simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
      StackRoutines.transferStacks, a] using hbframe 0 (by decide)
  have hf2 : f.stacks 2 = d.stacks 2 := by
    simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
      StackRoutines.transferStacks, a] using hbframe 2 (by decide)
  have hvalidf : invariant f := by
    intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · simp at hi
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 0 (by decide) (by decide)
    · simp [f, selected, cleared, StackRoutines.clearStacks]
    · simp [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks]
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 3 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 4 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 5 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 6 (by decide) (by decide)
    · simpa [f, selected, cleared, c, transferred, StackRoutines.clearStacks,
        StackRoutines.transferStacks, coreStack] using hbclear 7 (by decide) (by decide)
  obtain ⟨e, hemit, he0, he1, he2, heframe, he10, he11, he12⟩ :=
    emitCall_eval (SubexpTautologyProgram.encodedClause C) f hf1
  let n := (3 * (d.stacks 1).length + 3) +
    (m + ((3 * (b.stacks 5).length + 3) +
      ((2 * (c.stacks 4).length + 3) +
        (1 + (SubexpNormalizeProgram.emitIfSelectedSteps (f.regs 12)
          (SubexpTautologyProgram.encodedClause C) + 1)))))
  refine ⟨n, ?_, e, ?_, ?_, he0.trans hf0, he1, ?_, he10, he11, he12⟩
  · have hecost := SubexpNormalizeProgram.emitIfSelected_steps_le (f.regs 12)
      (SubexpTautologyProgram.encodedClause C)
    dsimp [n, perClauseCost]
    rw [hpayload, hb5, hc4]
    simp only [List.length_reverse, List.length_cons, List.length_nil]
    have hsquare : (SubexpTautologyProgram.encodedClause C).length + 1 ≤
        ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hslack : 11 * (SubexpTautologyProgram.encodedClause C).length + 24 ≤
        50 * ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2 := by
      calc
        11 * (SubexpTautologyProgram.encodedClause C).length + 24 ≤
            50 * ((SubexpTautologyProgram.encodedClause C).length + 1) := by omega
        _ ≤ 50 * ((SubexpTautologyProgram.encodedClause C).length + 1) ^ 2 :=
          Nat.mul_le_mul_left 50 hsquare
    omega
  · exact (transfer_eval 1 3 (by decide) d).seq
      (hcore.seq ((transfer_eval 5 1 (by decide) b).seq
        ((clear_eval 4 c).seq ((select_eval (cleared 4 c)).seq hemit))))
  · intro i hi
    exact (heframe i hi).trans (hvalidf i hi)
  · simpa [hf12, hf2] using he2

theorem callback_contract :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      perClauseCost invariant (SubexpNormalizeProgram.FilterEffect 2 keepClause) ClausePayload := by
  intro bits tail base hbits hbase
  obtain ⟨C, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail
    (SubexpTautologyProgram.encodedClause C).reverse
  have hd1 : d.stacks 1 = (SubexpTautologyProgram.encodedClause C).reverse := by
    simp [d, RecordPrograms.state, ports]
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state, ports]
  have hd2 : d.stacks 2 = base.stacks 2 := by simp [d, RecordPrograms.state, ports]
  have hdvalid : invariant d := by
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h1 : i ≠ 1 := by intro h; subst i; omega
    simpa [d, RecordPrograms.state, ports, h0, h1] using hbase i hi
  obtain ⟨n, hn, e, he, hv, he0, he1, he2, he10, he11, he12⟩ :=
    callback_eval C d hd1 hdvalid
  have heState : RecordPrograms.state ports e false true false tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ he10 he11 he12 (he0.trans hd0) he1
  refine ⟨n, e, hn, hv, ?_, ?_⟩
  · simpa [SubexpNormalizeProgram.FilterEffect, hd2] using he2
  · rw [heState]
    exact he

theorem encodedFormula_records (F : List (List ℕ)) :
    encodedFormula F = Encoding.encodeList id (formulaRecords F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [encodedFormula, formulaRecords, Encoding.encodeList] using ih

theorem valid_formulaRecords (F : List (List ℕ)) :
    ∀ bits ∈ formulaRecords F, ClausePayload bits := by
  intro bits hb
  obtain ⟨C, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨C, rfl⟩

theorem filtered_formulaRecords (F : List (List ℕ)) :
    (formulaRecords F).filter keepClause =
      formulaRecords (ExecCNF.removeTautologies SubexpFrontend.negateCode F) := by
  change (F.map SubexpTautologyProgram.encodedClause).filter keepClause =
    (F.filter (fun C => !(ExecCNF.tautology SubexpFrontend.negateCode C))).map
      SubexpTautologyProgram.encodedClause
  induction F with
  | nil => rfl
  | cons C F ih =>
    cases h : !(ExecCNF.tautology SubexpFrontend.negateCode C) <;>
      simp [ h, ih]

theorem filter_budget_le (records : List (List Bool)) :
    3 + RecordPrograms.budget perClauseCost records ≤
      300 * ((Encoding.encodeList id records).length + 1) ^ 2 := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]
  | cons bits records ih =>
    simp only [RecordPrograms.budget, perClauseCost, Encoding.length_encodeList_cons, id_eq]
    have hproduct : 0 ≤ bits.length * (Encoding.encodeList id records).length := Nat.zero_le _
    nlinarith

theorem encoded_filter_length_le (records : List (List Bool)) :
    (Encoding.encodeList id (records.filter keepClause)).length ≤
      (Encoding.encodeList id records).length := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
    cases h : keepClause bits <;>
      simp [ h, Encoding.length_encodeList_cons] <;> omega

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

theorem scan_eval (records acc : List (List Bool)) (d : Data)
    (valid : invariant d) (hacc : d.stacks 2 = Encoding.encodeList id acc)
    (hrecords : ∀ bits ∈ records, ClausePayload bits) (v p f : Bool) :
    ∃ n ≤ 300 * ((Encoding.encodeList id records).length + 1) ^ 2, ∃ next : Data,
      invariant next ∧
      next.stacks 2 = Encoding.encodeList id ((records.filter keepClause).reverse ++ acc) ∧
      Eval scan n
        (RecordPrograms.state ports d v p f (Encoding.encodeList id records) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) perClauseCost invariant
    (SubexpNormalizeProgram.FilterEffect 2 keepClause) ClausePayload callback_contract
    records [] d hrecords valid v p f
  have hout := SubexpNormalizeProgram.filterVisits_result 2 keepClause hhistory acc hacc
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  exact ⟨n, hn.trans (filter_budget_le records), next, hnext, hout,
    by simpa [scan, hany, SubexpNormalizeProgram.unread_false] using he⟩

theorem reverseStack_injective : Function.Injective reverseStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [reverseStack]

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data)
    (hsource : d.stacks 2 = Encoding.encodeList id records)
    (houtput : d.stacks 0 = Encoding.encodeList id acc) (hpayload : d.stacks 1 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧
      e.stacks 0 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 1 = [] ∧ e.stacks 2 = [] ∧
      (∀ i : Fin 11, 3 ≤ i.val → e.stacks i = d.stacks i) := by
  let a : State 3 4 := ⟨d.regs ∘ emitRegister, d.stacks ∘ reverseStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) (d.regs 12)
      (Encoding.encodeList id records) (d.stacks 3) (Encoding.encodeList id acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitRegister ]
    · funext i
      fin_cases i <;> simp [ reverseStack,
        hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 3) (d.regs 10) (d.regs 11) (d.regs 12)
  simp only [List.append_nil] at ht
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitRegister reverseStack d emitRegister_injective reverseStack_injective ht
  rw [embed_restricted _ _ emitRegister_injective reverseStack_injective] at he
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 3)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitRegister reverseStack d b
  have hstack (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_⟩
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · intro i hi
    by_cases h3 : i = 3
    · subst i
      simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 1
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [reverseStack] at hj <;> subst i <;> omega

theorem pushFalse_eval (stack : Fin 11) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 11) 0 false) d
  have h2 : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 13) (s := 11) stack 0) middle
  exact Eval.seq h1 h2

theorem filter_eval_oai (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = encodedFormula F) (hready : Ready d) :
    ∃ n ≤ 399 * ((encodedFormula F).length + 1) ^ 2, ∃ e : Data,
      Eval filter n d e ∧ Ready e ∧
      e.stacks 0 = encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F) := by
  rcases hready with ⟨hvalid, hpayload, houtput⟩
  let a := pushed 2 d
  have ha : invariant a := by
    intro i hi
    have hne : i ≠ 2 := by intro h; subst i; omega
    simpa [a, pushed, hne] using hvalid i hi
  have ha2 : a.stacks 2 = Encoding.encodeList id [] := by
    simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, hn, next, hnext, hout, hscan⟩ := scan_eval (formulaRecords F) [] a ha ha2
    (valid_formulaRecords F) (a.regs 10) (a.regs 11) (a.regs 12)
  have hstart : RecordPrograms.state ports a (a.regs 10) (a.regs 11) (a.regs 12)
      (Encoding.encodeList id (formulaRecords F)) [] = a :=
    RecordPrograms.state_eq_self ports a _ _ _ _ _ rfl rfl rfl
      (by
        change Function.update d.stacks 2 (false :: d.stacks 2) ports.source =
          Encoding.encodeList id (formulaRecords F)
        rw [show ports.source = (0 : Fin 11) from rfl]
        simpa [← encodedFormula_records] using hsource)
      (by
        change Function.update d.stacks 2 (false :: d.stacks 2) ports.payload = []
        rw [show ports.payload = (1 : Fin 11) from rfl]
        simpa using hpayload)
  rw [hstart] at hscan
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 0 b
  have hcvalid : invariant c := by
    intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h1 : i ≠ 1 := by intro h; subst i; omega
    simpa [c, pushed, b, RecordPrograms.state, ports, h0, h1] using hnext i hi
  have hc2 : c.stacks 2 =
      Encoding.encodeList id ((formulaRecords F).filter keepClause).reverse := by
    simpa [c, pushed, b, RecordPrograms.state, ports] using hout
  have hc0 : c.stacks 0 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, ports, Encoding.encodeList]
  have hc1 : c.stacks 1 = [] := by simp [c, pushed, b, RecordPrograms.state, ports]
  obtain ⟨m, hm, e, hreverse, he0, he1, he2, heframe⟩ :=
    reverseCall_eval ((formulaRecords F).filter keepClause).reverse [] c hc2 hc0 hc1
  have hfilterlen := encoded_filter_length_le (formulaRecords F)
  rw [encoded_reverse_length] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, ?_, ?_⟩
  · rw [← encodedFormula_records] at hn hfilterlen
    nlinarith
  · exact (pushFalse_eval 2 d).seq (hscan.seq ((pushFalse_eval 0 b).seq hreverse))
  · refine ⟨?_, he1, he2⟩
    intro i hi
    exact (heframe i hi).trans (hcvalid i hi)
  · simpa [filtered_formulaRecords, ← encodedFormula_records] using he0

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.filter_eval_oai := @OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.filter_eval_oai
