-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.prefixCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:38:53.938254+00:00
-- url     : https://prove2.me/submissions/c1d14748-0305-4d72-9e1d-444e0b17da9a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S111
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpTautologyFilterProgram_filter_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCleanLiteralsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clausewise literal cleanup

Each framed clause is decoded, passed to the fixed literal-deduplication
program, and framed again. An outer record reversal restores clause order.
The finite control is independent of the input formula and its clause sizes.
-/

namespace SubexponentialSAT.ExecCleanLiteralsProgram

open BitProgram StructuredCalls

theorem bankReg_injective : Function.Injective bankReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 13 => x.val) h

theorem bankStack_injective : Function.Injective bankStack := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 11 => x.val) h
  simpa [bankStack] using hv

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk) (frame : State R S) :
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

theorem literalCall_eval (clause : List ℕ) (d : Data)
    (hsource : d.stacks 3 = clauseCode clause)
    (hwork : ∀ i : Fin 8, i ≠ 0 → d.stacks (bankStack i) = []) :
    ∃ n ≤ 120 * ((clauseCode clause).length + 1) ^ 2, ∃ e : Data,
      Eval literalCall n d e ∧ e.stacks 3 = clauseCode (ExecCNF.dedupLiterals clause) ∧
      (∀ i : Fin 8, i ≠ 0 → e.stacks (bankStack i) = []) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = d.stacks 1 ∧ e.stacks 2 = d.stacks 2 ∧
      e.regs 10 = d.regs 10 ∧ e.regs 11 = d.regs 11 ∧ e.regs 12 = d.regs 12 := by
  let a : State 10 8 := ⟨d.regs ∘ bankReg, d.stacks ∘ bankStack⟩
  have ha : ExecLiteralDedupProgram.Ready a := by
    exact ⟨⟨hwork 3 (by decide), hwork 4 (by decide), hwork 5 (by decide),
      hwork 6 (by decide), hwork 7 (by decide)⟩, hwork 1 (by decide), hwork 2 (by decide)⟩
  obtain ⟨next, hnext, hout, n, hn, ht⟩ :=
    ExecLiteralDedupProgram.literal_runsIn clause a hsource ha
  have he := eval_call_lifted ExecLiteralDedupProgram.dedupProgram
    bankReg bankStack d bankReg_injective bankStack_injective ht
  rw [embed_restricted bankReg bankStack bankReg_injective bankStack_injective d] at he
  let e := embedState bankReg bankStack d next
  have hs (i : Fin 8) : e.stacks (bankStack i) = next.stacks i :=
    embedState_stack _ _ _ _ bankStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [clauseCode] using (hs 0).trans hout
  · intro i hi
    rw [hs]
    rcases hnext with ⟨⟨h3, h4, h5, h6, h7⟩, h1, h2⟩
    fin_cases i <;> simp_all
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

theorem transfer_eval (src dst : Fin 11) (hsd : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) := by
  apply Eval.call
  simpa [transferred, StructuredProgram.State.withPC] using
    ListRegisterProgram.transfer_run (r := 13) (s := 11) src dst 0 1 hsd (by decide) d.regs d.stacks

theorem emitReg_injective : Function.Injective emitReg := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 13 => x.val) h
  simpa [emitReg] using hv

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

theorem emitCall_eval (bits : List Bool) (d : Data)
    (hquery : d.stacks 1 = bits.reverse) (hselected : d.regs 12 = true) :
    ∃ e : Data, Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps true bits + 1) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame bits ++ d.stacks 2) ∧
      (∀ i : Fin 8, e.stacks (bankStack i) = d.stacks (bankStack i)) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ emitStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) true
      (d.stacks 0) (d.stacks 10) (d.stacks 2) bits.reverse := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg, hselected]
    · funext i
      fin_cases i <;> simp [ emitStack, hquery]
  have ht := SubexpNormalizeProgram.emitIfSelected_trace true bits
    (d.stacks 0) (d.stacks 10) (d.stacks 2) (d.regs 10) (d.regs 11)
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitReg emitStack d emitReg_injective emitStack_injective ht
  rw [embed_restricted emitReg emitStack emitReg_injective emitStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 10) (true :: (Encoding.frame bits ++ d.stacks 2)) []
  let e := embedState emitReg emitStack d b
  have hs (i : Fin 4) : e.stacks (emitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ emitStack_injective i
  have hr (i : Fin 3) : e.regs (emitReg i) = b.regs i :=
    embedState_register _ _ _ _ emitReg_injective i
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hs 0
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hs 3
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hs 2
  · intro i
    by_cases hi : i = 7
    · subst i
      simpa [emitStack, bankStack, b, SubexpNormalizeProgram.filterState] using hs 1
    · apply embedState_stack_frame
      intro h
      rcases h with ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hi' : i.val ≠ 7 := fun h => hi (Fin.ext h)
      fin_cases j <;> simp [emitStack, bankStack] at hv <;> omega
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hr 0
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hr 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hr 2

theorem select_eval (d : Data) : Eval select 1 d (selected d) := by
  apply Eval.base
  simpa [selected, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
    StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 11) 12 true) d

theorem clauseCode_dedup_length_le (clause : List ℕ) :
    (clauseCode (ExecCNF.dedupLiterals clause)).length ≤ (clauseCode clause).length := by
  have h := ExecLiteralDedupProgram.encoded_dedup_length_le (clause.map Encoding.encodeNat)
  rw [ExecLiteralDedupProgram.dedup_map Encoding.encodeNat Encoding.encodeNat_injective,
    ExecLiteralDedupProgram.encode_nat_records, ExecLiteralDedupProgram.encode_nat_records] at h
  exact h

theorem callback_eval (clause : List ℕ) (d : Data)
    (hquery : d.stacks 1 = (clauseCode clause).reverse) (hclean : Clean d) :
    ∃ n ≤ 160 * ((clauseCode clause).length + 1) ^ 2, ∃ e : Data,
      Eval callback n d e ∧ Clean e ∧ e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame (clauseCode (ExecCNF.dedupLiterals clause)) ++ d.stacks 2) ∧
      e.regs 10 = false ∧ e.regs 11 = true ∧ e.regs 12 = false := by
  let a := transferred 1 3 d
  have hd3 : d.stacks 3 = [] := by simpa using hclean 0
  have ha3 : a.stacks 3 = clauseCode clause := by
    simp [a, transferred, StackRoutines.transferStacks, hquery, hd3]
  have haw : ∀ i : Fin 8, i ≠ 0 → a.stacks (bankStack i) = [] := by
    intro i hi
    simp [a, transferred, StackRoutines.transferStacks, hi, hclean i]
  obtain ⟨m, hm, e, he, he3, hew, he0, he1, he2, he10, he11, he12⟩ :=
    literalCall_eval clause a ha3 haw
  let b := transferred 3 1 e
  have hb : Clean b := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [b, transferred, StackRoutines.transferStacks]
    · simp [b, transferred, StackRoutines.transferStacks, hi, hew i hi]
  have hb1 : b.stacks 1 = (clauseCode (ExecCNF.dedupLiterals clause)).reverse := by
    simp [b, transferred, StackRoutines.transferStacks, he3, he1, a]
  let c := selected b
  obtain ⟨f, hf, hf0, hf1, hf2, hfw, hf10, hf11, hf12⟩ :=
    emitCall_eval (clauseCode (ExecCNF.dedupLiterals clause)) c hb1 (by simp [c, selected])
  let steps := (3 * (d.stacks 1).length + 3) +
    (m + ((3 * (e.stacks 3).length + 3) +
      (1 + (SubexpNormalizeProgram.emitIfSelectedSteps true
        (clauseCode (ExecCNF.dedupLiterals clause)) + 1))))
  have hlen := clauseCode_dedup_length_le clause
  refine ⟨steps, ?_, f, ?_, ?_, ?_, hf1, ?_, hf10, hf11, hf12⟩
  · dsimp [steps]
    rw [hquery, List.length_reverse, he3]
    simp only [SubexpNormalizeProgram.emitIfSelectedSteps, ite_true, if_true]
    have hquad : 11 * (clauseCode clause).length + 19 ≤
        40 * ((clauseCode clause).length + 1) ^ 2 := by
      nlinarith only [Nat.zero_le (clauseCode clause).length]
    omega
  · exact Eval.seq (transfer_eval 1 3 (by decide) d) (Eval.seq he
      (Eval.seq (transfer_eval 3 1 (by decide) e) (Eval.seq (select_eval b) hf)))
  · intro i
    exact (hfw i).trans (hb i)
  · simpa [c, selected, b, transferred, StackRoutines.transferStacks, he0, a] using hf0
  · simpa [c, selected, b, transferred, StackRoutines.transferStacks, he2, a] using hf2

theorem callback_state_eval (clause : List ℕ) (tail : List Bool) (base : Data) (valid : Clean base) :
    ∃ (n : ℕ) (next : Data), n ≤ 160 * ((clauseCode clause).length + 1) ^ 2 ∧ Clean next ∧
      next.stacks 2 = true :: (Encoding.frame (clauseCode (ExecCNF.dedupLiterals clause)) ++ base.stacks 2) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false tail (clauseCode clause).reverse)
        (RecordPrograms.state ports next false true false tail []) := by
  let d := RecordPrograms.state ports base false true false tail (clauseCode clause).reverse
  obtain ⟨n, hn, next, he, hclean, hs, hp, ho, ht, hpr, hf⟩ :=
    callback_eval clause d (by simp [d, RecordPrograms.state, ports])
      ((clean_state _ _ _ _ _ _).mpr valid)
  have hs' : next.stacks 0 = tail := by simpa [d, RecordPrograms.state, ports] using hs
  have hend : RecordPrograms.state ports next false true false tail [] = next :=
    RecordPrograms.state_eq_self ports next false true false _ [] ht hpr hf hs' hp
  refine ⟨n, next, hn, hclean, ?_, ?_⟩
  · simpa [d] using ho
  · rw [hend]
    exact he

theorem formulaCode_eq_records (formula : List (List ℕ)) :
    formulaCode formula = Encoding.encodeList id (formula.map clauseCode) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      exact congrArg (fun tail => true :: (Encoding.frame (clauseCode clause) ++ tail)) ih

theorem loop_run (formula : List (List ℕ)) (acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) :
    ∃ (n : ℕ) (next : Data), n ≤ 1 + budget formula ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id (((ExecCNF.cleanLiterals formula).map clauseCode).reverse ++ acc) ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base (formula.map clauseCode) [])
        (RecordPrograms.state ports next false true false [] []) := by
  induction formula generalizing base acc with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_, ?_⟩
      · simpa [ExecCNF.cleanLiterals] using hacc
      · apply Eval.while_false
        simp [RecordPrograms.afterTag]
  | cons clause rest ih =>
      obtain ⟨n, middle, hn, hmiddle, hout, hc⟩ :=
        callback_state_eval clause (Encoding.encodeList id (rest.map clauseCode)) base valid
      let acc' := clauseCode (ExecCNF.dedupLiterals clause) :: acc
      have hacc' : middle.stacks 2 = Encoding.encodeList id acc' := by
        simpa [acc', hacc, Encoding.encodeList] using hout
      obtain ⟨m, next, hm, hnext, hresult, hrest⟩ := ih acc' middle hmiddle hacc'
      have hreader : Eval (RecordPrograms.reader ports) (6 * (clauseCode clause).length + 4)
          (RecordPrograms.afterTag ports base ((clause :: rest).map clauseCode) [])
          (RecordPrograms.state ports base false true false
            (Encoding.encodeList id (rest.map clauseCode)) (clauseCode clause).reverse) := by
        simpa [RecordPrograms.afterTag] using RecordPrograms.reader_eval ports base
          (clauseCode clause) (Encoding.encodeList id (rest.map clauseCode)) [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false (Encoding.encodeList id (rest.map clauseCode)) [])
          (RecordPrograms.afterTag ports middle (rest.map clauseCode) []) := by
        apply Eval.ite_false (by simp)
        simpa using RecordPrograms.pop_list_eval ports middle (rest.map clauseCode) [] false true
      have hbody := Eval.seq hreader (Eval.seq hc hbranch)
      have hrun := Eval.while_true (body := RecordPrograms.body ports callback)
        (by simp [RecordPrograms.afterTag]) hbody hrest
      refine ⟨(6 * (clauseCode clause).length + 4 + (n + 2)) + m + 1,
        next, ?_, hnext, ?_, hrun⟩
      · simp only [budget]
        omega
      · simpa [ExecCNF.cleanLiterals, acc', List.reverse_cons, List.append_assoc] using hresult

theorem scan_eval (formula : List (List ℕ)) (acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 3 + budget formula ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id (((ExecCNF.cleanLiterals formula).map clauseCode).reverse ++ acc) ∧
      Eval scan n (RecordPrograms.state ports base v pr f (formulaCode formula) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hout, hloop⟩ := loop_run formula acc base valid hacc
  refine ⟨1 + (1 + n), next, by omega, hnext, hout, ?_⟩
  rw [formulaCode_eq_records]
  apply Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
  apply Eval.seq _ hloop
  simpa using RecordPrograms.pop_list_eval ports base (formula.map clauseCode) [] v pr

theorem budget_le (formula : List (List ℕ)) : budget formula ≤ 500 * (formulaCode formula).length ^ 2 := by
  induction formula with
  | nil => simp [budget, formulaCode]
  | cons clause rest ih =>
      change budget rest ≤ 500 * (Encoding.encodeList clauseCode rest).length ^ 2 at ih
      simp only [budget, formulaCode, Encoding.length_encodeList_cons]
      nlinarith [Nat.zero_le ((clauseCode clause).length * (clauseCode clause).length),
        Nat.zero_le ((clauseCode clause).length * (Encoding.encodeList clauseCode rest).length)]

theorem cleaned_length_le (formula : List (List ℕ)) :
    (formulaCode (ExecCNF.cleanLiterals formula)).length ≤ (formulaCode formula).length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have h := clauseCode_dedup_length_le clause
      change (Encoding.encodeList clauseCode (ExecCNF.cleanLiterals rest)).length ≤
        (Encoding.encodeList clauseCode rest).length at ih
      simp only [formulaCode, ExecCNF.cleanLiterals, List.map_cons, Encoding.length_encodeList_cons]
      change (Encoding.encodeList clauseCode (rest.map ExecCNF.dedupLiterals)).length ≤
        (Encoding.encodeList clauseCode rest).length at ih
      omega

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
      (∀ i : Fin 8, e.stacks (bankStack i) = d.stacks (bankStack i)) := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ reverseStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 10) (d.regs 11) (d.regs 12)
      (Encoding.encodeList id records) (d.stacks 10) (Encoding.encodeList id acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg ]
    · funext i
      fin_cases i <;> simp [ reverseStack,
        hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 10) (d.regs 10) (d.regs 11) (d.regs 12)
  simp only [List.append_nil] at ht
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitReg reverseStack d emitReg_injective reverseStack_injective ht
  rw [embed_restricted emitReg reverseStack emitReg_injective reverseStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 10)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitReg reverseStack d b
  have hs (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_⟩
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hs 2
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hs 3
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hs 0
  · intro i
    by_cases hi : i = 7
    · subst i
      simpa [reverseStack, bankStack, b, SubexpNormalizeProgram.filterState] using hs 1
    · apply embedState_stack_frame
      intro h
      rcases h with ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hi' : i.val ≠ 7 := fun h => hi (Fin.ext h)
      fin_cases j <;> simp [reverseStack, bankStack] at hv <;> omega

theorem pushFalse_eval (stack : Fin 11) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 13) (s := 11) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 13) (s := 11) stack 0) middle
  exact Eval.seq h₁ h₂

theorem ready_iff (d : Data) : Ready d ↔ ∀ i : Fin 11, i ≠ 0 → d.stacks i = [] := by
  constructor
  · rintro ⟨hc, h1, h2⟩ i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h1
    · exact h2
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact hc 3
    · exact hc 4
    · exact hc 5
    · exact hc 6
    · exact hc 7
  · intro h
    exact ⟨fun i => h (bankStack i) (bankStack_ne_zero i), h 1 (by decide), h 2 (by decide)⟩

theorem clean_eval (formula : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode formula) (hready : Ready d) :
    ∃ n ≤ 500 * (formulaCode formula).length ^ 2 + 10 * (formulaCode formula).length + 7,
      ∃ e : Data, Eval clean n d e ∧ Ready e ∧
        e.stacks 0 = formulaCode (ExecCNF.cleanLiterals formula) := by
  rcases hready with ⟨hclean, hpayload, houtput⟩
  let a := pushed 2 d
  have ha : Clean a := by
    simpa [a, pushed, Clean] using hclean
  have hao : a.stacks 2 = Encoding.encodeList id [] := by
    simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, next, hn, hnext, hout, hs⟩ := scan_eval formula [] a ha hao
    (a.regs 10) (a.regs 11) (a.regs 12)
  have hstart : RecordPrograms.state ports a (a.regs 10) (a.regs 11) (a.regs 12)
      (formulaCode formula) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, pushed, ports] using hsource
    · simpa [a, pushed, ports] using hpayload
  rw [hstart] at hs
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 0 b
  have hc : Clean c := by
    simpa [c, pushed, b, Clean, RecordPrograms.state, ports] using hnext
  have hc2 : c.stacks 2 =
      Encoding.encodeList id ((ExecCNF.cleanLiterals formula).map clauseCode).reverse := by
    simpa [c, pushed, b] using hout
  have hc0 : c.stacks 0 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, ports, Encoding.encodeList]
  have hc1 : c.stacks 1 = [] := by
    simp [c, pushed, b, RecordPrograms.state, ports]
  obtain ⟨m, hm, e, he, he0, he1, he2, hew⟩ :=
    reverseCall_eval ((ExecCNF.cleanLiterals formula).map clauseCode).reverse [] c hc2 hc0 hc1
  have hcost := budget_le formula
  have hlength := cleaned_length_le formula
  rw [ExecLiteralDedupProgram.encoded_reverse_length, ← formulaCode_eq_records] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, ?_, ?_⟩
  · omega
  · exact Eval.seq (pushFalse_eval 2 d) (Eval.seq hs (Eval.seq (pushFalse_eval 0 b) he))
  · exact ⟨fun i => (hew i).trans (hc i), he1, he2⟩
  · simpa only [List.reverse_reverse, List.append_nil, ← formulaCode_eq_records] using he0

end SubexponentialSAT.ExecCleanLiteralsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem ready_iff (d : Data) : Ready d ↔ ∀ i : Fin 11, i ≠ 0 → d.stacks i = [] := by
  constructor
  · rintro ⟨hc, h1, h2⟩ i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact h1
    · exact h2
    · exact hc 3 (by decide)
    · exact hc 4 (by decide)
    · exact hc 5 (by decide)
    · exact hc 6 (by decide)
    · exact hc 7 (by decide)
    · exact hc 8 (by decide)
    · exact hc 9 (by decide)
    · exact hc 10 (by decide)
  · intro h
    refine ⟨?_, h 1 (by decide), h 2 (by decide)⟩
    intro i hi
    apply h i
    intro he
    subst i
    contradiction

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Actual literal cleanup followed by tautology removal

This is a fixed program on the original declared variable universe. Its two
stages use the same input/output port and restore empty work stacks. The exact
list order and the length bound are retained for subsequent clause absorption.
-/

namespace SubexponentialSAT.SubexpNormalizationPrefixProgram

open BitProgram StructuredCalls

theorem command_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 999 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval command n d e ∧ Ready e ∧ e.stacks 0 = formulaCode (preprocess F) := by
  obtain ⟨n, hn, middle, hclean, hmiddle, hout⟩ :=
    ExecCleanLiteralsProgram.clean_eval F d hsource hready
  have hnext : SubexpTautologyFilterProgram.Ready middle :=
    (SubexpTautologyFilterProgram.ready_iff middle).mpr
      ((ExecCleanLiteralsProgram.ready_iff middle).mp hmiddle)
  obtain ⟨m, hm, e, hfilter, he, heout⟩ :=
    SubexpTautologyFilterProgram.filter_eval (ExecCNF.cleanLiterals F) middle hout hnext
  have hlen := ExecCleanLiteralsProgram.cleaned_length_le F
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 2
  have hm' : m ≤ 399 * ((formulaCode F).length + 1) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left 399 hsq)
  refine ⟨n + m, ?_, e, hclean.seq hfilter, ?_, heout⟩
  · nlinarith
  · exact (ExecCleanLiteralsProgram.ready_iff e).mpr
      ((SubexpTautologyFilterProgram.ready_iff e).mp he)

theorem program_runsIn (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = formulaCode (preprocess F) ∧
      RunsIn program (1000 * ((formulaCode F).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := command_eval F d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 0 0⟩
  have hpos : 0 < ((formulaCode F).length + 1) ^ 2 := pow_pos (by omega) _
  omega

end SubexponentialSAT.SubexpNormalizationPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

theorem prefixRegister_injective : Function.Injective prefixRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 15 => i.val) h)

theorem prefixStack_injective : Function.Injective prefixStack := by
  intro i j h
  apply Fin.ext
  have he := congrArg (fun i : Fin 16 => i.val) h
  simp only [prefixStack] at he
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

theorem prefixCall_eval_oai (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 1000 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval prefixCall n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (SubexpNormalizationPrefixProgram.preprocess F) := by
  let a : SubexpNormalizationPrefixProgram.Data :=
    ⟨d.regs ∘ prefixRegister, d.stacks ∘ prefixStack⟩
  have ha0 : a.stacks 0 = formulaCode F := hsource
  have ha : SubexpNormalizationPrefixProgram.Ready a := by
    apply (ExecCleanLiteralsProgram.ready_iff a).mpr
    intro i hi
    exact hready (prefixStack i) (fun he => hi (prefixStack_injective he))
  obtain ⟨b, hbready, hbout, n, hn, hbtrace⟩ :=
    SubexpNormalizationPrefixProgram.program_runsIn F a ha0 ha
  let e := embedState prefixRegister prefixStack d b
  have he := eval_call_lifted SubexpNormalizationPrefixProgram.program prefixRegister prefixStack d
    prefixRegister_injective prefixStack_injective hbtrace
  rw [embed_restricted _ _ prefixRegister_injective prefixStack_injective] at he
  refine ⟨n, hn, e, he, ?_, ?_⟩
  · intro i hi
    by_cases hp : ∃ j, prefixStack j = i
    · obtain ⟨j, rfl⟩ := hp
      have hj : j ≠ 0 := by
        intro h
        subst j
        exact hi rfl
      exact (embedState_stack prefixRegister prefixStack d b prefixStack_injective j).trans
        ((ExecCleanLiteralsProgram.ready_iff b).mp hbready j hj)
    · exact (embedState_stack_frame prefixRegister prefixStack d b i hp).trans (hready i hi)
  · exact (embedState_stack prefixRegister prefixStack d b prefixStack_injective 0).trans hbout

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.prefixCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.prefixCall_eval_oai
