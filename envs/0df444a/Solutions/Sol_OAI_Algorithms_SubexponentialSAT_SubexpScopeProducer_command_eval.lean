-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:27:26.400739+00:00
-- url     : https://prove2.me/submissions/7eda57c7-4bbe-4850-94b8-1abfd3a7184a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S111

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterConversions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual binary-to-unary conversion

The finite controller consumes a little-endian binary counter on stack 0.
Each positive iteration pushes one true bit onto stack 1. Stack 2 is counter
scratch. The cleanup empties the counter and resets every Boolean register.
The numeric value controls execution through stack instructions only.
-/

namespace SubexponentialSAT.CounterConversions

open BitProgram StructuredProgram StructuredCalls CounterPrograms CounterForPrograms

theorem encodeNat_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    ∃ n, StructuredCalls.Eval encodeNatCmd n (state regs bits [])
      (state zeroRegs [] (Encoding.encodeNat (value bits))) ∧ n ≤ coreBound bits + 2 := by
  let d := state regs bits []
  obtain ⟨n, he, hn⟩ := unary_correct (pushed false d) (by simp [pushed, d, state])
  refine ⟨2 + n, ?_, ?_⟩
  · have h := (push_eval false d).seq he
    simpa [encodeNatCmd, pushed, d, state, Encoding.encodeNat] using h
  · have hn' : n ≤ coreBound bits := by simpa [pushed, d, state] using hn
    omega

theorem encodeNat_runs (regs : Fin 3 → Bool) (bits : List Bool) :
    BitProgram.RunsIn encodeNatProgram (runtimeBound bits)
      ((state regs bits []).withPC (some encodeNatProgram.entry))
      ((state zeroRegs [] (Encoding.encodeNat (value bits))).withPC none) := by
  obtain ⟨n, he, hn⟩ := encodeNat_eval regs bits
  exact ⟨n + 1, by have := coreBound_le bits; omega,
    StructuredCalls.compiled_halt_trace he 0 1⟩

end SubexponentialSAT.CounterConversions

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem copySuffix_eval (d : Data) (htmp : d.stacks 7 = []) :
    Eval copySuffix (7 * (d.stacks 0).length + 5) d (copied d) := by
  apply Eval.call
  simpa [copySuffixProgram, copied, StructuredProgram.State.withPC] using
    ListRegisterProgram.copy_run (r := 10) (s := 8) 0 3 7 0 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp

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

theorem selectMissing_eval (d : Data) : Eval selectMissing 1 d (selectedState d) := by
  apply Eval.base
  simpa [selectedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
    StructuredProgram.Eval.atom (StructuredProgram.Atom.bnot (r := 10) (s := 8) 9 4) d

theorem callback_eval (bits : List Bool) (rest : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id rest)
    (hquery : d.stacks 1 = bits.reverse) (hclean : Clean d) :
    ∃ n ≤ callbackBound bits rest, ∃ e : Data, Eval callback n d e ∧ Clean e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if bits ∈ rest then d.stacks 2
        else true :: (Encoding.frame bits ++ d.stacks 2)) ∧
      e.regs 7 = false ∧ e.regs 8 = true ∧ e.regs 9 = false := by
  rcases hclean with ⟨h3, h4, h5, h6, h7⟩
  obtain ⟨m, hm, e, he, hanswer, hresidual, houtput, hquery', hcopy, htmp,
      hsource', hacc, hscratch, htag, hpresent, hfound⟩ :=
    ExecCNFSubset.memberCall_eval bits rest (copied d)
      (by simp [copied, StackRoutines.copyStacks, hsource, h3])
      (by simpa [copied, StackRoutines.copyStacks] using hquery)
      (by simpa [copied, StackRoutines.copyStacks] using h4)
      (by simpa [copied, StackRoutines.copyStacks] using h5)
      (by simpa [copied, StackRoutines.copyStacks] using h6)
  let c₁ := ExecCNFSubset.cleared 3 (selectedState e)
  let c₂ := ExecCNFSubset.cleared 4 c₁
  have cq : c₂.stacks 1 = bits.reverse := by
    simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks] using hquery'
  have cs : c₂.regs 9 = !(decide (bits ∈ rest)) := by
    simp [c₂, c₁, selectedState, readRegs, hanswer]
  obtain ⟨f, hf, fs, fp, fo, f3, f4, f5, f6, f7, ft, fpr, ff⟩ :=
    emitCall_eval (!(decide (bits ∈ rest))) bits c₂ cq cs
  let steps := (7 * (d.stacks 0).length + 5) +
    (m + (1 + ((2 * (e.stacks 3).length + 3) +
      ((2 * (c₁.stacks 4).length + 3) +
        (SubexpNormalizeProgram.emitIfSelectedSteps (!(decide (bits ∈ rest))) bits + 1)))))
  have hlen4 : (c₁.stacks 4).length = 1 := by
    simp [c₁, selectedState, StackRoutines.clearStacks, houtput]
  have hemit := SubexpNormalizeProgram.emitIfSelected_steps_le (!(decide (bits ∈ rest))) bits
  refine ⟨steps, ?_, f, ?_, ?_, ?_, fp, ?_, ft, fpr, ff⟩
  · dsimp [steps, callbackBound]
    rw [hsource, hlen4]
    nlinarith
  · exact Eval.seq (copySuffix_eval d h7) (Eval.seq he (Eval.seq (selectMissing_eval e)
      (Eval.seq (ExecCNFSubset.clear_eval 3 (selectedState e))
        (Eval.seq (ExecCNFSubset.clear_eval 4 c₁) hf))))
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [c₂, c₁, ExecCNFSubset.cleared, StackRoutines.clearStacks] using f3
    · simpa [c₂, ExecCNFSubset.cleared, StackRoutines.clearStacks] using f4
    · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks, hcopy] using f5
    · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks, htmp] using f6
    · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks,
        hscratch, copied, StackRoutines.copyStacks, h7] using f7
  · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks,
      hsource', copied, StackRoutines.copyStacks] using fs
  · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks,
      hacc, copied, StackRoutines.copyStacks] using fo

theorem callback_state_eval (bits : List Bool) (rest : List (List Bool))
    (base : Data) (valid : Clean base) :
    ∃ (n : ℕ) (next : Data), n ≤ callbackBound bits rest ∧ Clean next ∧
      next.stacks 2 = (if bits ∈ rest then base.stacks 2
        else true :: (Encoding.frame bits ++ base.stacks 2)) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false (Encoding.encodeList id rest) bits.reverse)
        (RecordPrograms.state ports next false true false (Encoding.encodeList id rest) []) := by
  let d := RecordPrograms.state ports base false true false (Encoding.encodeList id rest) bits.reverse
  obtain ⟨n, hn, next, he, hclean, hs, hp, ho, ht, hpr, hf⟩ :=
    callback_eval bits rest d (by simp [d, RecordPrograms.state ])
      (by simp [d, RecordPrograms.state ])
      ((clean_state _ _ _ _ _ _).mpr valid)
  have hs' : next.stacks 0 = Encoding.encodeList id rest := by
    simpa [d, RecordPrograms.state, ports] using hs
  have hend : RecordPrograms.state ports next false true false (Encoding.encodeList id rest) [] = next :=
    RecordPrograms.state_eq_self ports next false true false _ [] ht hpr hf hs' hp
  refine ⟨n, next, hn, hclean, ?_, ?_⟩
  · simpa [d] using ho
  · rw [hend]
    exact he

theorem loop_run (records acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) :
    ∃ (n : ℕ) (next : Data), n ≤ 1 + budget records ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id ((ExecCNF.dedupLiterals records).reverse ++ acc) ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base records [])
        (RecordPrograms.state ports next false true false [] []) := by
  induction records generalizing base acc with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_, ?_⟩
      · simpa [ExecCNF.dedupLiterals] using hacc
      · apply Eval.while_false
        change false = false
        rfl
  | cons bits rest ih =>
      obtain ⟨n, middle, hn, hmiddle, hout, hc⟩ := callback_state_eval bits rest base valid
      let acc' := if bits ∈ rest then acc else bits :: acc
      have hacc' : middle.stacks 2 = Encoding.encodeList id acc' := by
        by_cases hm : bits ∈ rest
        · simpa [acc', hm, hacc] using hout
        · simpa [acc', hm, hacc, Encoding.encodeList] using hout
      obtain ⟨m, next, hm, hnext, hresult, hrest⟩ := ih acc' middle hmiddle hacc'
      have hreader : Eval (RecordPrograms.reader ports) (6 * bits.length + 4)
          (RecordPrograms.afterTag ports base (bits :: rest) [])
          (RecordPrograms.state ports base false true false (Encoding.encodeList id rest) bits.reverse) := by
        simpa [RecordPrograms.afterTag] using
          RecordPrograms.reader_eval ports base bits (Encoding.encodeList id rest) [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false (Encoding.encodeList id rest) [])
          (RecordPrograms.afterTag ports middle rest []) := by
        apply Eval.ite_false (by change false = false; rfl)
        simpa using RecordPrograms.pop_list_eval ports middle rest [] false true
      have hbody := Eval.seq hreader (Eval.seq hc hbranch)
      have hrun := Eval.while_true (body := RecordPrograms.body ports callback)
        (by change true = true; rfl) hbody hrest
      refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext, ?_, hrun⟩
      · simp only [budget]
        omega
      · by_cases hmem : bits ∈ rest
        · have hc' := (ExecCNF.contains_true bits rest).mpr hmem
          simpa [ExecCNF.dedupLiterals, hc', acc', hmem] using hresult
        · have hc' : ExecCNF.contains bits rest ≠ true := by
            intro h
            exact hmem ((ExecCNF.contains_true bits rest).mp h)
          simpa [ExecCNF.dedupLiterals, hc', acc', hmem, List.reverse_cons,
            List.append_assoc] using hresult

theorem scan_eval (records acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 3 + budget records ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id ((ExecCNF.dedupLiterals records).reverse ++ acc) ∧
      Eval scan n (RecordPrograms.state ports base v pr f (Encoding.encodeList id records) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hout, hloop⟩ := loop_run records acc base valid hacc
  refine ⟨1 + (1 + n), next, by omega, hnext, hout, ?_⟩
  apply Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
  apply Eval.seq _ hloop
  simpa using RecordPrograms.pop_list_eval ports base records [] v pr

theorem budget_le (records : List (List Bool)) :
    budget records ≤ 100 * (Encoding.encodeList id records).length ^ 2 := by
  induction records with
  | nil => simp [budget]
  | cons bits rest ih =>
      simp only [budget, callbackBound, Encoding.length_encodeList_cons, id_eq]
      nlinarith [Nat.zero_le (bits.length * bits.length),
        Nat.zero_le (bits.length * (Encoding.encodeList id rest).length)]

theorem encoded_dedup_length_le (records : List (List Bool)) :
    (Encoding.encodeList id (ExecCNF.dedupLiterals records)).length ≤
      (Encoding.encodeList id records).length := by
  induction records with
  | nil => rfl
  | cons bits rest ih =>
      unfold ExecCNF.dedupLiterals
      split
      · simp only [Encoding.length_encodeList_cons, id_eq]
        omega
      · simpa only [Encoding.length_encodeList_cons, id_eq] using
          Nat.add_le_add_left ih (2 * bits.length + 2)

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
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = d.stacks 5 ∧ e.stacks 6 = d.stacks 6 ∧ e.stacks 7 = d.stacks 7 := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ reverseStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) (d.regs 9)
      (Encoding.encodeList id records) (d.stacks 7) (Encoding.encodeList id acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg ]
    · funext i
      fin_cases i <;> simp [ reverseStack,
        hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 7) (d.regs 7) (d.regs 8) (d.regs 9)
  simp only [List.append_nil] at ht
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitReg reverseStack d emitReg_injective reverseStack_injective ht
  rw [embed_restricted emitReg reverseStack emitReg_injective reverseStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 7)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitReg reverseStack d b
  have hstack (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 1

theorem pushFalse_eval (stack : Fin 8) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 10) (s := 8) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 10) (s := 8) stack 0) middle
  exact Eval.seq h₁ h₂

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

theorem dedup_eval (records : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id records) (hready : Ready d) :
    ∃ n ≤ 100 * (Encoding.encodeList id records).length ^ 2 +
        10 * (Encoding.encodeList id records).length + 7,
      ∃ e : Data, Eval dedup n d e ∧ Ready e ∧
        e.stacks 0 = Encoding.encodeList id (ExecCNF.dedupLiterals records) := by
  rcases hready with ⟨hclean, hpayload, houtput⟩
  let a := pushed 2 d
  have ha : Clean a := by simpa [a, pushed, Clean] using hclean
  have hao : a.stacks 2 = Encoding.encodeList id [] := by simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, next, hn, hnext, hout, hs⟩ := scan_eval records [] a ha hao
    (a.regs 7) (a.regs 8) (a.regs 9)
  have hstart : RecordPrograms.state ports a (a.regs 7) (a.regs 8) (a.regs 9)
      (Encoding.encodeList id records) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, pushed] using hsource
    · simpa [a, pushed] using hpayload
  rw [hstart] at hs
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 0 b
  have hc : Clean c := by simpa [c, pushed, b, Clean, RecordPrograms.state, ports] using hnext
  have hc2 : c.stacks 2 = Encoding.encodeList id (ExecCNF.dedupLiterals records).reverse := by
    simpa [c, pushed, b] using hout
  have hc0 : c.stacks 0 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, Encoding.encodeList]
  have hc1 : c.stacks 1 = [] := by simp [c, pushed, b, RecordPrograms.state ]
  obtain ⟨m, hm, e, he, he0, he1, he2, he3, he4, he5, he6, he7⟩ :=
    reverseCall_eval (ExecCNF.dedupLiterals records).reverse [] c hc2 hc0 hc1
  have hcost := budget_le records
  have hlength := encoded_dedup_length_le records
  rw [encoded_reverse_length] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, ?_, ?_⟩
  · omega
  · exact Eval.seq (pushFalse_eval 2 d) (Eval.seq hs (Eval.seq (pushFalse_eval 0 b) he))
  · refine ⟨?_, he1, he2⟩
    rcases hc with ⟨hc3, hc4, hc5, hc6, hc7⟩
    exact ⟨he3.trans hc3, he4.trans hc4, he5.trans hc5, he6.trans hc6, he7.trans hc7⟩
  · simpa using he0

theorem dedup_runsIn (records : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id records) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = Encoding.encodeList id (ExecCNF.dedupLiterals records) ∧
      RunsIn dedupProgram (120 * ((Encoding.encodeList id records).length + 1) ^ 2)
        (d.withPC (some dedupProgram.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := dedup_eval records d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 0 0⟩
  nlinarith

theorem dedup_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    ExecCNF.dedupLiterals (xs.map f) = (ExecCNF.dedupLiterals xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hm : ExecCNF.contains (f x) (xs.map f) = true ↔
          ExecCNF.contains x xs = true := by
        rw [ExecCNF.contains_true, ExecCNF.contains_true, List.mem_map]
        constructor
        · rintro ⟨y, hy, h⟩
          exact hf h ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      by_cases h : ExecCNF.contains x xs = true
      · have h' := hm.mpr h
        simp [ExecCNF.dedupLiterals, h, h', ih]
      · have h' : ExecCNF.contains (f x) (xs.map f) ≠ true := fun hx => h (hm.mp hx)
        simp [ExecCNF.dedupLiterals, h, h', ih]

theorem encode_nat_records (xs : List ℕ) :
    Encoding.encodeList id (xs.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

/-- On actual unary literal fields, the result is precisely the executable
CNF normalizer's stable, last-occurrence literal deduplication. -/
theorem literal_runsIn (clause : List ℕ) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList Encoding.encodeNat clause) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 0 = Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals clause) ∧
      RunsIn dedupProgram
        (120 * ((Encoding.encodeList Encoding.encodeNat clause).length + 1) ^ 2)
        (d.withPC (some dedupProgram.entry)) (e.withPC none) := by
  have hs : d.stacks 0 = Encoding.encodeList id (clause.map Encoding.encodeNat) := by
    simpa only [encode_nat_records] using hsource
  obtain ⟨e, he, hout, hr⟩ := dedup_runsIn (clause.map Encoding.encodeNat) d hs hready
  rw [dedup_map Encoding.encodeNat Encoding.encodeNat_injective, encode_nat_records] at hout
  exact ⟨e, he, hout, by simpa only [encode_nat_records] using hr⟩

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An actual clause-row program

The input clause uses `Encoding.encodeList Encoding.encodeNat`. The stored
assignment is an explicit word of the declared length, one bit per variable.
The program parses each literal, decodes its unary index and polarity, performs
a preserving indexed read, and accumulates the disjunction. No semantic test is
an instruction. All auxiliary ports and all input requirements are explicit.
-/

namespace SubexponentialSAT.SubexpClauseRowProgram

open BitProgram StructuredCalls

namespace LiteralDecoder

private theorem pair_cycle (v pr acc : Bool)
    (a o i w src payload : List Bool) :
    Trace program 9 (cfg (some 2) v pr false acc a o i w src (true :: true :: payload))
      (cfg (some 2) true true false acc a o (true :: i) w src payload) := by
  refine .cons (b := cfg (some 3) true true false acc a o i w src (true :: payload)) ?_
    (.cons (b := cfg (some 4) true true false acc a o i w src (true :: payload)) ?_
      (.cons (b := cfg (some 5) true true true acc a o i w src (true :: payload)) ?_
        (.cons (b := cfg (some 2) true true true acc a o i w src (true :: payload)) ?_
          (.cons (b := cfg (some 3) true true true acc a o i w src payload) ?_
            (.cons (b := cfg (some 4) true true true acc a o i w src payload) ?_
              (.cons (b := cfg (some 5) true true false acc a o i w src payload) ?_
                (.cons (b := cfg (some 6) true true false acc a o i w src payload) ?_
                  (.cons ?_ (.refl _)))))))))
  all_goals simp [step, cfg, data, execInstr, readRegs, StructuredProgram.State.withPC]

private theorem finish_even (v pr acc : Bool) (a o i w src : List Bool) :
    Trace program 3 (cfg (some 2) v pr false acc a o i w src [])
      (cfg none false false false acc a o i w src []) := by
  refine .cons (b := cfg (some 3) false false false acc a o i w src []) ?_
    (.cons (b := cfg (some 7) false false false acc a o i w src []) ?_
      (.cons ?_ (.refl _)))
  all_goals simp [step, cfg, data, execInstr, readRegs, StructuredProgram.State.withPC]

private theorem finish_odd (v pr acc : Bool) (a o i w src : List Bool) :
    Trace program 7 (cfg (some 2) v pr false acc a o i w src [true])
      (cfg none false false true acc a o i w src []) := by
  refine .cons (b := cfg (some 3) true true false acc a o i w src []) ?_
    (.cons (b := cfg (some 4) true true false acc a o i w src []) ?_
      (.cons (b := cfg (some 5) true true true acc a o i w src []) ?_
        (.cons (b := cfg (some 2) true true true acc a o i w src []) ?_
          (.cons (b := cfg (some 3) false false true acc a o i w src []) ?_
            (.cons (b := cfg (some 7) false false true acc a o i w src []) ?_
              (.cons ?_ (.refl _)))))))
  all_goals simp [step, cfg, data, execInstr, readRegs, StructuredProgram.State.withPC]

private theorem loop_trace (index : ℕ) (sign v pr acc : Bool)
    (a o i w src : List Bool) :
    Trace program (9 * index + 4 * (if sign then 1 else 0) + 3)
      (cfg (some 2) v pr false acc a o i w src
        (List.replicate (2 * index + if sign then 1 else 0) true))
      (cfg none false false sign acc a o (List.replicate index true ++ i) w src []) := by
  induction index generalizing v pr i with
  | zero => cases sign <;> simpa using (by first | exact finish_even v pr acc a o i w src
                                                       | exact finish_odd v pr acc a o i w src)
  | succ index ih =>
      have h := (pair_cycle v pr acc a o i w src
        (List.replicate (2 * index + if sign then 1 else 0) true)).trans
        (ih true true (true :: i))
      have hcount : 2 * (index + 1) + (if sign then 1 else 0) =
          (2 * index + if sign then 1 else 0) + 2 := by omega
      have hlist : List.replicate index true ++ true :: i =
          List.replicate (index + 1) true ++ i := by
        rw [List.replicate_add]; simp [List.append_assoc]
      convert h using 1 <;> simp [hcount, List.replicate_succ, hlist] ; omega

/-- Exact trace from the reversed canonical natural payload to a unary index
and Boolean polarity. All assignment, clause, and accumulator data are preserved. -/
theorem trace (index : ℕ) (sign v pr oldSign acc : Bool)
    (a o i w src : List Bool) :
    Trace program (9 * index + 4 * (if sign then 1 else 0) + 5)
      (cfg (some program.entry) v pr oldSign acc a o i w src
        (Encoding.encodeNat (2 * index + if sign then 1 else 0)).reverse)
      (cfg none false false sign acc a o (List.replicate index true ++ i) w src []) := by
  have hl := loop_trace index sign false true acc a o i w src
  have h := Computation.Trace.cons
    (a := cfg (some program.entry) v pr oldSign acc a o i w src
      (Encoding.encodeNat (2 * index + if sign then 1 else 0)).reverse)
    (b := cfg (some 1) false true oldSign acc a o i w src
      (List.replicate (2 * index + if sign then 1 else 0) true))
    (by simp [step, cfg, data, execInstr, readRegs, Encoding.encodeNat,
      List.reverse_append, StructuredProgram.State.withPC])
    (Computation.Trace.cons (by simp [step, cfg, data, execInstr,
      StructuredProgram.State.withPC]) hl)
  convert h using 1
  all_goals try with_reducible_and_instances rfl

end LiteralDecoder


end SubexponentialSAT.SubexpClauseRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiteralChunkProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual literal-index to chunk-index conversion

The input is one reversed canonical unary literal field and a binary chunk
width. The fixed program decodes the variable index, counts it into binary,
divides by the chunk width, and constructs the reversed canonical chunk field.
-/

namespace SubexponentialSAT.SubexpLiteralChunkProgram

open BitProgram StructuredCalls StackRoutines

private theorem tapes_eq (ell unary binary remainder quotient payload encoded : List Bool) :
    tapes ell unary binary remainder quotient payload encoded = fun i =>
      if i = 0 then remainder else if i = 2 then unary else if i = 4 then binary
      else if i = 7 then quotient else if i = 9 then payload else if i = 10 then encoded
      else if i = 18 then ell else [] := by
  first | done | (first | done | (funext i; fin_cases i <;> rfl))

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem embed_restricted {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (d : State R S) :
    embedState register stack d ⟨d.regs ∘ register, d.stacks ∘ stack⟩ = d := by
  apply embedState_eq_of_ports _ _ _ _ _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

private theorem embed_stacks {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 19)
    (hs : Function.Injective stack) (frame : Data) (source : State r s)
    (target : Fin 19 → List Bool)
    (hp : ∀ i, target (stack i) = source.stacks i)
    (hf : ∀ i, (¬ ∃ j, stack j = i) → target i = frame.stacks i) :
    embedState register stack frame source =
      (⟨(embedState register stack frame source).regs, target⟩ : Data) := by
  apply state_ext
  · rfl
  ·
    funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack register stack frame source hs j).trans (hp j).symm
    · exact (embedState_stack_frame register stack frame source i hi).trans (hf i hi).symm

theorem decodeRegisters_injective : Function.Injective decodeRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem decodeStacks_injective : Function.Injective decodeStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 19 => x.val) h)

theorem decode_eval (regs : Fin 8 → Bool) (ell : List Bool) (v : ℕ) (sign : Bool) :
    ∃ rf, Eval decode (9 * v + 4 * (if sign then 1 else 0) + 5)
      (data regs ell [] [] [] []
        (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse [])
      (data rf ell (List.replicate v true) [] [] [] [] []) := by
  let d := data regs ell [] [] [] []
    (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse []
  let a := SubexpClauseRowProgram.data (regs 0) (regs 1) (regs 2) (regs 3)
    [] [] [] [] [] (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse
  let b := SubexpClauseRowProgram.data false false sign (regs 3)
    [] [] (List.replicate v true) [] [] []
  have ha : a = ⟨d.regs ∘ decodeRegisters, d.stacks ∘ decodeStacks⟩ := by
    apply state_ext
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have ht := SubexpClauseRowProgram.LiteralDecoder.trace v sign (regs 0) (regs 1)
    (regs 2) (regs 3) [] [] [] [] []
  simp only [List.append_nil] at ht
  have h := eval_call_lifted SubexpClauseRowProgram.LiteralDecoder.program
    decodeRegisters decodeStacks d decodeRegisters_injective decodeStacks_injective ht
  change Eval decode _ (embedState _ _ d a) (embedState _ _ d b) at h
  rw [ha, embed_restricted _ _ decodeRegisters_injective decodeStacks_injective] at h
  have hb := embed_stacks decodeRegisters decodeStacks decodeStacks_injective d b
    (tapes ell (List.replicate v true) [] [] [] [] [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨2, by simpa [decodeStacks] using h.symm⟩
      have h9 : i ≠ 9 := fun h => hi ⟨9, by simpa [decodeStacks] using h.symm⟩
      simp only [d, data, tapes_eq, h2, h9, ite_false])
  rw [hb] at h
  exact ⟨_, h⟩

theorem lengthRegisters_injective : Function.Injective lengthRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem lengthStacks_injective : Function.Injective lengthStacks := by decide

theorem count_eval (regs : Fin 8 → Bool) (ell unary : List Bool) :
    ∃ t ≤ unary.length * (8 * unary.length + 10) + 4,
      ∃ rf binary, Eval count t (data regs ell unary [] [] [] [] [])
        (data rf ell [] binary [] [] [] []) ∧
        BinaryArithmetic.toNat binary = unary.length ∧ binary.length ≤ unary.length := by
  let d := data (Function.update regs 2 false) ell unary [] [] [] [] []
  have hr : Eval (.base (.atom (.set 2 false))) 1
      (data regs ell unary [] [] [] [] []) d := .base (.atom _ _)
  obtain ⟨binary, hv, hl, t, ht, htrace⟩ :=
    CounterPrograms.length_correct_from (regs 0) (regs 1) unary
  let a : State 3 3 := ⟨CounterPrograms.counterRegs (regs 0) (regs 1) false,
    CounterPrograms.lengthStacks unary [] []⟩
  let b : State 3 3 := ⟨fun _ => false, fun j => if j = 1 then binary else []⟩
  have ha : a = ⟨d.regs ∘ lengthRegisters, d.stacks ∘ lengthStacks⟩ := by
    apply state_ext
    · funext i; fin_cases i <;> simp [a, d, data, lengthRegisters, CounterPrograms.counterRegs]
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  change Trace CounterPrograms.lengthProgram t
    (a.withPC (some CounterPrograms.lengthProgram.entry)) (b.withPC none) at htrace
  have h := eval_call_lifted CounterPrograms.lengthProgram lengthRegisters lengthStacks d
    lengthRegisters_injective lengthStacks_injective htrace
  rw [ha, embed_restricted _ _ lengthRegisters_injective lengthStacks_injective] at h
  have hb := embed_stacks lengthRegisters lengthStacks lengthStacks_injective d b
    (tapes ell [] binary [] [] [] [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨0, by simpa [lengthStacks] using h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨1, by simpa [lengthStacks] using h.symm⟩
      simp only [d, data, tapes_eq, h2, h4, ite_false])
  rw [hb] at h
  exact ⟨1 + t, by omega, _, binary, hr.seq h,
    (CounterPrograms.value_eq_toNat binary).symm.trans hv, hl⟩

theorem divide_eval (regs : Fin 8 → Bool) (ell binary : List Bool) :
    ∃ t ≤ 100 * (ell.length + binary.length + 1) ^ 2, ∃ rf,
      Eval divide t (data regs ell [] binary [] [] [] [])
        (data rf ell [] [] (ModularQuotientArithmetic.divide ell binary).2
          (ModularQuotientArithmetic.divide ell binary).1 [] []) := by
  obtain ⟨t, ht, rf, h⟩ := ModularQuotientLift.programAt_eval divisionPorts ell binary regs
    (tapes ell [] binary [] [] [] []) rfl rfl rfl rfl rfl rfl rfl rfl
  have he : ModularQuotientLift.quotientStacksAt divisionPorts
      (ModularQuotientArithmetic.divide ell binary).2
      (ModularQuotientArithmetic.divide ell binary).1 (tapes ell [] binary [] [] [] []) =
      tapes ell [] [] (ModularQuotientArithmetic.divide ell binary).2
        (ModularQuotientArithmetic.divide ell binary).1 [] [] := by
    funext i; fin_cases i <;> simp [ModularQuotientLift.quotientStacksAt, divisionPorts, tapes]
  rw [he] at h
  exact ⟨t, ht, rf, h⟩

theorem conversionRegisters_injective : Function.Injective conversionRegisters :=
  lengthRegisters_injective
theorem conversionStacks_injective : Function.Injective conversionStacks := by decide

theorem encode_eval (regs : Fin 8 → Bool) (ell remainder quotient : List Bool) :
    ∃ t ≤ CounterConversions.runtimeBound quotient, ∃ rf,
      Eval encode t (data regs ell [] [] remainder quotient [] [])
        (data rf ell [] [] remainder [] []
          (Encoding.encodeNat (BinaryArithmetic.toNat quotient))) := by
  let d := data regs ell [] [] remainder quotient [] []
  let a := CounterConversions.state (regs ∘ conversionRegisters) quotient []
  let b := CounterConversions.state CounterConversions.zeroRegs []
    (Encoding.encodeNat (CounterPrograms.value quotient))
  have ha : a = ⟨d.regs ∘ conversionRegisters, d.stacks ∘ conversionStacks⟩ := by
    apply state_ext
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨t, ht, htrace⟩ := CounterConversions.encodeNat_runs (regs ∘ conversionRegisters) quotient
  have h := eval_call_lifted CounterConversions.encodeNatProgram conversionRegisters conversionStacks d
    conversionRegisters_injective conversionStacks_injective htrace
  change Eval encode t (embedState _ _ d a) (embedState _ _ d b) at h
  rw [ha, embed_restricted _ _ conversionRegisters_injective conversionStacks_injective] at h
  have hb := embed_stacks conversionRegisters conversionStacks conversionStacks_injective d b
    (tapes ell [] [] remainder [] [] (Encoding.encodeNat (CounterPrograms.value quotient)))
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i hi
      have h7 : i ≠ 7 := fun h => hi ⟨0, by simpa [conversionStacks] using h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨1, by simpa [conversionStacks] using h.symm⟩
      simp only [d, data, tapes_eq, h7, h10, ite_false])
  rw [hb] at h
  rw [CounterPrograms.value_eq_toNat] at h
  exact ⟨t, ht, _, h⟩


theorem clearRemainder_eval (regs : Fin 8 → Bool) (ell remainder encoded : List Bool) :
    Eval clearRemainder (2 * remainder.length + 3)
      (data regs ell [] [] remainder [] [] encoded)
      (data (readRegs regs 0 1 none) ell [] [] [] [] [] encoded) := by
  have h := ListRegisterProgram.clear_run (0 : Fin 19) (0 : Fin 8) 1 regs
    (tapes ell [] [] remainder [] [] encoded)
  have he : clearStacks (0 : Fin 19) (tapes ell [] [] remainder [] [] encoded) =
      tapes ell [] [] [] [] [] encoded := by
    funext i; fin_cases i <;> simp [clearStacks, tapes]
  rw [he] at h
  exact .call _ h

theorem reverseField_eval (regs : Fin 8 → Bool) (ell encoded : List Bool) :
    Eval reverseField (3 * encoded.length + 3)
      (data regs ell [] [] [] [] [] encoded)
      (data (readRegs regs 0 1 none) ell [] [] [] [] encoded.reverse []) := by
  have h := ListRegisterProgram.transfer_run (10 : Fin 19) 9 (0 : Fin 8) 1
    (by decide) (by decide) regs (tapes ell [] [] [] [] [] encoded)
  have he : transferStacks (10 : Fin 19) 9 (tapes ell [] [] [] [] [] encoded) =
      tapes ell [] [] [] [] encoded.reverse [] := by
    funext i; fin_cases i <;> simp [transferStacks, tapes]
  rw [he] at h
  exact .call _ h

private theorem straight_eval (as : List (StructuredProgram.Atom 8 19)) (d : Data) :
    StructuredProgram.Eval (straight as) as.length d (straightResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa only [straight, straightResult, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom a d) (ih (a.eval d))

theorem reset_eval (regs : Fin 8 → Bool) (ell payload : List Bool) :
    Eval reset 8 (data regs ell [] [] [] [] payload [])
      (data (fun _ => false) ell [] [] [] [] payload []) := by
  have h := straight_eval resetOps (data regs ell [] [] [] [] payload [])
  have he : straightResult resetOps (data regs ell [] [] [] [] payload []) =
      data (fun _ => false) ell [] [] [] [] payload [] := by
    apply state_ext
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · rfl
  rw [he] at h
  exact .base (by simpa only [resetOps, List.length_cons, List.length_nil] using h)

theorem command_eval (regs : Fin 8 → Bool) (ell : List Bool) (v : ℕ) (sign : Bool)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ budget ell.length v,
      Eval command t
        (data regs ell [] [] [] []
          (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse [])
        (data (fun _ => false) ell [] [] [] []
          (Encoding.encodeNat (v / BinaryArithmetic.toNat ell)).reverse []) := by
  obtain ⟨rd, hd⟩ := decode_eval regs ell v sign
  obtain ⟨nc, hnc, rc, binary, hc, hvalue, hlength⟩ :=
    count_eval rd ell (List.replicate v true)
  simp only [List.length_replicate] at hnc hvalue hlength
  obtain ⟨nd, hnd, rq, hq⟩ := divide_eval rc ell binary
  obtain ⟨ne, hne, re, he⟩ := encode_eval rq ell
    (ModularQuotientArithmetic.divide ell binary).2 (ModularQuotientArithmetic.divide ell binary).1
  have hquot : BinaryArithmetic.toNat (ModularQuotientArithmetic.divide ell binary).1 =
      v / BinaryArithmetic.toNat ell := by
    rw [ModularQuotientArithmetic.divide_quotient_correct ell binary hell, hvalue]
  rw [hquot] at he
  have hremLength := ModularQuotientArithmetic.divide_remainder_length ell binary
  have hquotLength := ModularQuotientArithmetic.divide_quotient_length ell binary
  have hclear := clearRemainder_eval re ell (ModularQuotientArithmetic.divide ell binary).2
    (Encoding.encodeNat (v / BinaryArithmetic.toNat ell))
  have hrev := reverseField_eval (readRegs re 0 1 none) ell
    (Encoding.encodeNat (v / BinaryArithmetic.toNat ell))
  have hreset := reset_eval (readRegs (readRegs re 0 1 none) 0 1 none) ell
    (Encoding.encodeNat (v / BinaryArithmetic.toNat ell)).reverse
  have h := hd.seq (hc.seq (hq.seq (he.seq (hclear.seq (hrev.seq hreset)))))
  refine ⟨_, ?_, h⟩
  have hdiv := Nat.div_le_self v (BinaryArithmetic.toNat ell)
  have hdivCost : nd ≤ 100 * (ell.length + v + 1) ^ 2 := hnd.trans
    (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 2))
  have hconvCost : ne ≤ 32 * (v + 1) * (v + 1) := by
    unfold CounterConversions.runtimeBound at hne
    rw [CounterPrograms.value_eq_toNat, hquot, hquotLength] at hne
    exact hne.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left 32 (Nat.add_le_add_right hdiv 1))
      (Nat.add_le_add_right hlength 1))
  have hfieldLength : (Encoding.encodeNat (v / BinaryArithmetic.toNat ell)).length =
      v / BinaryArithmetic.toNat ell + 1 := by simp [Encoding.encodeNat]
  unfold budget
  rw [hremLength, hfieldLength]
  split <;> omega

/-- The parser-facing contract accepts the canonical code directly. -/
theorem command_eval_code (regs : Fin 8 → Bool) (ell : List Bool) (code : ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ budget ell.length (code / 2),
      Eval command t
        (data regs ell [] [] [] [] (Encoding.encodeNat code).reverse [])
        (data (fun _ => false) ell [] [] [] []
          (Encoding.encodeNat ((code / 2) / BinaryArithmetic.toNat ell)).reverse []) := by
  have hdecomp : 2 * (code / 2) + (if decide (code % 2 = 1) then 1 else 0) = code := by
    have hm := Nat.mod_lt code (by omega : 0 < 2)
    have hd := Nat.mod_add_div code 2
    by_cases h : code % 2 = 1 <;> simp [h] <;> omega
  simpa only [hdecomp] using command_eval regs ell (code / 2) (decide (code % 2 = 1)) hell

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpChunkRecordMap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual map from literal records to chunk records

The input is the canonical encoded list of literal codes and a preserved binary
chunk width. Each parsed record passes through the actual index decoder,
counter, division program, and record writer. The accumulator is reversed, as
required by the separately checked record-reversal and stable-deduplication
passes. No semantic map is installed as a machine instruction.
-/

namespace SubexponentialSAT.SubexpChunkRecordMap

open BitProgram StructuredCalls

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

theorem parser_state (v pr found v' pr' found' : Bool)
    (ell source output payload source' payload' : List Bool) :
    RecordPrograms.state ports (data v pr found ell source output payload)
        v' pr' found' source' payload' = data v' pr' found' ell source' output payload' := by
  apply state_ext
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem convertRegisters_injective : Function.Injective convertRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
theorem convertStacks_injective : Function.Injective convertStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 22 => x.val) h)

private theorem embed_convert (v pr found : Bool)
    (ell source output oldPayload payload : List Bool) :
    embedState convertRegisters convertStacks
      (data v pr found ell source output oldPayload)
      (SubexpLiteralChunkProgram.data (fun _ => false) ell [] [] [] [] payload []) =
      data v pr found ell source output payload := by
  apply embedState_eq_of_ports _ _ _ _ _ convertRegisters_injective convertStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    simp only [data, tapes, h9, ite_false]

theorem convert_eval (ell source output : List Bool) (code : ℕ) (v pr found : Bool)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ SubexpLiteralChunkProgram.budget ell.length (code / 2) + 1,
      Eval convert t
        (data v pr found ell source output (Encoding.encodeNat code).reverse)
        (data v pr found ell source output
          (Encoding.encodeNat ((code / 2) / BinaryArithmetic.toNat ell)).reverse) := by
  obtain ⟨t, ht, he⟩ := SubexpLiteralChunkProgram.command_eval_code
    (fun _ => false) ell code hell
  have htrace := compiled_halt_trace he (9 : Fin 19) 9
  have h := eval_call_lifted SubexpLiteralChunkProgram.program convertRegisters convertStacks
    (data v pr found ell source output (Encoding.encodeNat code).reverse)
    convertRegisters_injective convertStacks_injective htrace
  simp only [embed_convert] at h
  exact ⟨t + 1, Nat.add_le_add_right ht 1, h⟩

theorem emitRegisters_injective : Function.Injective emitRegisters := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide

private theorem embed_emit (v pr found oldV oldPr oldFound : Bool)
    (ell source output payload oldOutput oldPayload : List Bool) :
    embedState emitRegisters emitStacks
      (data oldV oldPr oldFound ell source oldOutput oldPayload)
      (SubexpNormalizeProgram.filterState v pr found source [] output payload) =
      data v pr found ell source output payload := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective emitStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2, h.symm⟩
    simp only [data, regs, h8, h9, h10, ite_false]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ 9 := fun h => hi ⟨3, h.symm⟩
    have h20 : i ≠ 20 := fun h => hi ⟨2, h.symm⟩
    simp only [data, tapes, h9, h20, ite_false]

theorem emit_eval (ell source output bits : List Bool) (v pr : Bool) :
    Eval emit (5 * bits.length + 12)
      (data v pr true ell source output bits.reverse)
      (data false true false ell source (true :: (Encoding.frame bits ++ output)) []) := by
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitRegisters emitStacks (data v pr true ell source output bits.reverse)
    emitRegisters_injective emitStacks_injective
    (SubexpNormalizeProgram.emitIfSelected_trace true bits source [] output v pr)
  simpa only [embed_emit, SubexpNormalizeProgram.emitIfSelectedSteps, ite_true, if_true,
    Nat.add_assoc] using h

theorem select_eval (v pr found : Bool) (ell source output payload : List Bool) :
    Eval select 1 (data v pr found ell source output payload)
      (data v pr true ell source output payload) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 11) (s := 22) 10 true)
    (data v pr found ell source output payload)
  have he : (StructuredProgram.Atom.set (r := 11) (s := 22) 10 true).eval
      (data v pr found ell source output payload) = data v pr true ell source output payload := by
    apply state_ext
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · rfl
  rw [he] at h
  exact .base h

theorem callback_eval (ell source output : List Bool) (code : ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ SubexpLiteralChunkProgram.budget ell.length (code / 2) +
        5 * (Encoding.encodeNat (chunk ell code)).length + 14,
      Eval callback t
        (data false true false ell source output (Encoding.encodeNat code).reverse)
        (data false true false ell source
          (true :: (Encoding.frame (Encoding.encodeNat (chunk ell code)) ++ output)) []) := by
  obtain ⟨t, ht, hc⟩ := convert_eval ell source output code false true false hell
  have hs := select_eval false true false ell source output
    (Encoding.encodeNat (chunk ell code)).reverse
  have he := emit_eval ell source output (Encoding.encodeNat (chunk ell code)) false true
  exact ⟨t + (1 + (5 * (Encoding.encodeNat (chunk ell code)).length + 12)),
    by omega, hc.seq (hs.seq he)⟩

theorem callback_contract (ell : List Bool) (hell : 0 < BinaryArithmetic.toNat ell) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost ell) (Invariant ell) (effect ell) Canonical := by
  intro bits tail base hbits hbase
  rcases hbits with ⟨code, rfl⟩
  rcases hbase with ⟨output, rfl⟩
  obtain ⟨t, ht, he⟩ := callback_eval ell tail output code hell
  let out := true :: (Encoding.frame (Encoding.encodeNat (chunk ell code)) ++ output)
  refine ⟨t, data false false false ell [] out [], ?_, ⟨out, rfl⟩, ?_, ?_⟩
  · simpa only [callbackCost, Encoding.length_encodeNat, Nat.add_sub_cancel,
      mappedBits_encodeNat] using ht
  · change out = true :: (Encoding.frame (mappedBits ell (Encoding.encodeNat code)) ++ output)
    rw [mappedBits_encodeNat]
  · simpa only [parser_state] using he

theorem visits_output (ell : List Bool) {records : List (List Bool)} {base next : Data}
    (h : RecordPrograms.Visits (fun _ => false) (effect ell) records base next)
    (acc : List (List Bool)) (hacc : base.stacks 20 = Encoding.encodeList id acc) :
    next.stacks 20 = Encoding.encodeList id ((records.map (mappedBits ell)).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht he => simp at ht
  | @miss bits rest base middle next ht he history ih =>
      have hm : middle.stacks 20 = Encoding.encodeList id (mappedBits ell bits :: acc) := by
        simpa only [effect, hacc, Encoding.encodeList, id_eq] using he
      have hnext := ih (mappedBits ell bits :: acc) hm
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hnext

theorem scan_eval (ell : List Bool) (codes acc : List ℕ) (suffix : List Bool)
    (hell : 0 < BinaryArithmetic.toNat ell) (v pr found : Bool) :
    ∃ t ≤ 3 + RecordPrograms.budget (callbackCost ell) (codes.map Encoding.encodeNat),
      Eval scan t
        (data v pr found ell (Encoding.encodeList Encoding.encodeNat codes ++ suffix)
          (Encoding.encodeList Encoding.encodeNat acc) [])
        (data false true false ell suffix
          (Encoding.encodeList Encoding.encodeNat ((codes.map (chunk ell)).reverse ++ acc)) []) := by
  let base := data false false false ell [] (Encoding.encodeList Encoding.encodeNat acc) []
  obtain ⟨t, next, ht, hnext, hh, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost ell) (Invariant ell) (effect ell) Canonical
    (callback_contract ell hell) (codes.map Encoding.encodeNat) suffix base
    (by intro bits hb; rcases List.mem_map.mp hb with ⟨code, _, rfl⟩; exact ⟨code, rfl⟩)
    ⟨Encoding.encodeList Encoding.encodeNat acc, rfl⟩ v pr found
  have hout := visits_output ell hh (acc.map Encoding.encodeNat)
    (by exact (ExecLiteralDedupProgram.encode_nat_records acc).symm)
  rcases hnext with ⟨out, rfl⟩
  have hout' : out = Encoding.encodeList Encoding.encodeNat
      ((codes.map (chunk ell)).reverse ++ acc) := by
    change out = _ at hout
    have hmaps : (codes.map Encoding.encodeNat).map (mappedBits ell) =
        (codes.map (chunk ell)).map Encoding.encodeNat := by
      simp only [List.map_map, Function.comp_def, mappedBits_encodeNat]
    rw [hmaps, ← List.map_reverse, ← List.map_append,
      ExecLiteralDedupProgram.encode_nat_records] at hout
    exact hout
  have hany : (codes.map Encoding.encodeNat).any (fun _ => false) = false := by simp
  rw [hout'] at he
  refine ⟨t, ht, ?_⟩
  simpa only [scan, base, parser_state, ExecLiteralDedupProgram.encode_nat_records,
    hany, SubexpNormalizeProgram.unread_false] using he

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

theorem initialize_eval (ell source : List Bool) :
    Eval initializeOutput 1 (data false false false ell source [] [])
      (data false false false ell source [false] []) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 11) (s := 22) 20 0)
    (data false false false ell source [] [])
  have he : (StructuredProgram.Atom.push (r := 11) (s := 22) 20 0).eval
      (data false false false ell source [] []) =
        data false false false ell source [false] [] := by
    apply state_ext
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [he] at h
  exact .base h

theorem seedSource_eval (ell output : List Bool) :
    Eval seedSource 1 (data false true false ell [] output [])
      (data false true false ell [false] output []) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 11) (s := 22) 19 0)
    (data false true false ell [] output [])
  have he : (StructuredProgram.Atom.push (r := 11) (s := 22) 19 0).eval
      (data false true false ell [] output []) =
        data false true false ell [false] output [] := by
    apply state_ext
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [he] at h
  exact .base h

theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

private theorem embed_reverse (v pr found oldV oldPr oldFound : Bool)
    (ell source output payload oldSource oldOutput : List Bool) :
    embedState emitRegisters reverseStacks
      (data oldV oldPr oldFound ell oldSource oldOutput [])
      (SubexpNormalizeProgram.filterState v pr found output [] source payload) =
        data v pr found ell source output payload := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective reverseStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2, h.symm⟩
    simp only [data, regs, h8, h9, h10, ite_false]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ 9 := fun h => hi ⟨3, h.symm⟩
    have h19 : i ≠ 19 := fun h => hi ⟨2, h.symm⟩
    have h20 : i ≠ 20 := fun h => hi ⟨0, h.symm⟩
    simp only [data, tapes, h9, h19, h20, ite_false]

theorem reverse_eval (ell : List Bool) (codes : List ℕ) :
    ∃ t ≤ 10 * (Encoding.encodeList Encoding.encodeNat codes).length,
      Eval reverse t
        (data false true false ell [false]
          (Encoding.encodeList Encoding.encodeNat codes.reverse) [])
        (data false true false ell (Encoding.encodeList Encoding.encodeNat codes) [] []) := by
  obtain ⟨t, ht, he⟩ := SubexpNormalizeProgram.reverseRecords_runsIn
    (codes.reverse.map Encoding.encodeNat) [] [] [] false true false
  have h := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitRegisters reverseStacks
    (data false true false ell [false]
      (Encoding.encodeList Encoding.encodeNat codes.reverse) [])
    emitRegisters_injective reverseStacks_injective he
  have hreverse : (codes.reverse.map Encoding.encodeNat).reverse = codes.map Encoding.encodeNat := by
    simp only [List.map_reverse, List.reverse_reverse]
  simp only [List.append_nil, hreverse,
    ExecLiteralDedupProgram.encode_nat_records, Encoding.encodeList, embed_reverse] at h
  refine ⟨t, ?_, h⟩
  rw [List.map_reverse, ExecLiteralDedupProgram.encoded_reverse_length,
    ExecLiteralDedupProgram.encode_nat_records] at ht
  exact ht

theorem dedupRegisters_injective : Function.Injective dedupRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
theorem dedupStacks_injective : Function.Injective dedupStacks := by decide

private theorem embed_restricted {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (d : State R S) :
    embedState register stack d ⟨d.regs ∘ register, d.stacks ∘ stack⟩ = d := by
  apply embedState_eq_of_ports _ _ _ _ _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

theorem dedup_eval (ell : List Bool) (codes : List ℕ) :
    ∃ t ≤ 120 * ((Encoding.encodeList Encoding.encodeNat codes).length + 1) ^ 2,
      ∃ rf, Eval dedup t
        (data false true false ell (Encoding.encodeList Encoding.encodeNat codes) [] [])
        (⟨rf, tapes ell
          (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] []⟩ : Data) := by
  let d := data false true false ell (Encoding.encodeList Encoding.encodeNat codes) [] []
  let localState : State 10 8 := ⟨d.regs ∘ dedupRegisters, d.stacks ∘ dedupStacks⟩
  have hready : ExecLiteralDedupProgram.Ready localState := by
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  obtain ⟨e, heReady, hout, t, ht, he⟩ := ExecLiteralDedupProgram.literal_runsIn
    codes localState rfl hready
  have h := eval_call_lifted ExecLiteralDedupProgram.dedupProgram dedupRegisters dedupStacks
    d dedupRegisters_injective dedupStacks_injective he
  change Eval dedup t (embedState _ _ d localState) (embedState _ _ d e) at h
  rw [embed_restricted _ _ dedupRegisters_injective dedupStacks_injective] at h
  let result := embedState dedupRegisters dedupStacks d e
  have hs : result.stacks = tapes ell
      (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] [] := by
    have hp (i : Fin 8) :
        (tapes ell (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] [])
          (dedupStacks i) = e.stacks i := by
      rcases heReady with ⟨⟨h3, h4, h5, h6, h7⟩, h1, h2⟩
      fin_cases i
      · exact hout.symm
      · exact h1.symm
      · exact h2.symm
      · exact h3.symm
      · exact h4.symm
      · exact h5.symm
      · exact h6.symm
      · exact h7.symm
    funext i
    by_cases hi : ∃ j, dedupStacks j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack _ _ _ _ dedupStacks_injective j).trans (hp j).symm
    · have h19 : i ≠ 19 := fun hh => hi ⟨0, hh.symm⟩
      rw [show result.stacks i = d.stacks i from
        embedState_stack_frame _ _ _ _ _ hi]
      simp only [d, data, tapes, h19, ite_false]
  have hr : result = (⟨result.regs, tapes ell
      (Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals codes)) [] []⟩ : Data) :=
    state_ext rfl hs
  exact ⟨t, ht, result.regs, by simpa only [← hr] using h⟩

theorem command_eval_oai (ell : List Bool) (codes : List ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ budget ell codes, ∃ rf,
      Eval command t (data false false false ell (Encoding.encodeList Encoding.encodeNat codes) [] [])
        (⟨rf, tapes ell (Encoding.encodeList Encoding.encodeNat (scope ell codes)) [] []⟩ : Data) := by
  have hi := initialize_eval ell (Encoding.encodeList Encoding.encodeNat codes)
  obtain ⟨ns, hns, hs⟩ := scan_eval ell codes [] [] hell false false false
  simp only [List.append_nil, Encoding.encodeList] at hs
  have hp := seedSource_eval ell (Encoding.encodeList Encoding.encodeNat (codes.map (chunk ell)).reverse)
  obtain ⟨nr, hnr, hr⟩ := reverse_eval ell (codes.map (chunk ell))
  obtain ⟨nd, hnd, rf, hd⟩ := dedup_eval ell (codes.map (chunk ell))
  refine ⟨1 + (ns + (1 + (nr + nd))), ?_, rf, hi.seq (hs.seq (hp.seq (hr.seq hd)))⟩
  unfold budget
  omega

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval_oai
