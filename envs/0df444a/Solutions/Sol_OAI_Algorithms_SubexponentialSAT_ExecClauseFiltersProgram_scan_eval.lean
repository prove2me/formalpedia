-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:13:48.66177+00:00
-- url     : https://prove2.me/submissions/0a9803e6-ef72-48c2-b46f-7750d905a9b1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem copyTarget_eval (d : Data) (htmp : d.stacks 7 = []) :
    Eval copyTarget (7 * (d.stacks 2).length + 5) d (copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 10) (s := 8)
    2 3 7 0 1 (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp
  have hh : step copyTargetProgram
      (StackRoutines.copyResult 7 2 3 0 1 d.regs d.stacks) =
      some ((copied d).withPC none) := by
    simp [step, StackRoutines.copyResult, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [copyTargetProgram, copied, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

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

theorem mark_eval (d : Data) :
    Eval (RecordPrograms.atom (.bnot 9 4)) 1 d (mark d) := by
  have h : (StructuredProgram.Atom.bnot (r := 10) (s := 8) 9 4).eval d = mark d := by
    rfl
  rw [← h]
  exact .base (.atom _ _)

theorem callback_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (hquery : d.stacks 1 = query.reverse) (valid : invariant records d) :
    ∃ n ≤ perRecordCost records query, ∃ e : Data,
      Eval callback n d e ∧ invariant records e ∧
      e.regs 9 = !decide (query ∈ records) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 := by
  rcases valid with ⟨htarget, hsource, hout, hcopy, htemp, hcopyTemp⟩
  have hsrc : (copied d).stacks 3 = Encoding.encodeList id records := by
    simp [ StackRoutines.copyStacks, htarget, hsource]
  have hq : (copied d).stacks 1 = query.reverse := by
    simpa [copied, StackRoutines.copyStacks] using hquery
  have ho : (copied d).stacks 4 = [] := by
    simpa [copied, StackRoutines.copyStacks] using hout
  have hc : (copied d).stacks 5 = [] := by
    simpa [copied, StackRoutines.copyStacks] using hcopy
  have ht : (copied d).stacks 6 = [] := by
    simpa [copied, StackRoutines.copyStacks] using htemp
  obtain ⟨n, hn, e, he, ha, hs, hp, hq, hc, ht, hzero, htwo, hseven, hr7, hr8, hr9⟩ :=
    memberCall_eval query records (copied d) hsrc hq ho hc ht
  let result := cleared 1 (cleared 4 (cleared 3 (mark e)))
  let steps := (7 * (d.stacks 2).length + 5) +
    (n + (1 + ((2 * (e.stacks 3).length + 3) +
      ((2 * (e.stacks 4).length + 3) + (2 * (e.stacks 1).length + 3)))))
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [steps, perRecordCost]
    rw [htarget, hp, hq]
    simp only [List.length_cons, List.length_nil, List.length_reverse]
    nlinarith
  · apply Eval.seq (copyTarget_eval d hcopyTemp)
    apply Eval.seq he
    apply Eval.seq (mark_eval e)
    apply Eval.seq (clear_eval 3 (mark e))
    apply Eval.seq (clear_eval 4 (cleared 3 (mark e)))
    simpa [result, cleared, StackRoutines.clearStacks, mark] using
      clear_eval 1 (cleared 4 (cleared 3 (mark e)))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [result, cleared, StackRoutines.clearStacks, mark, copied,
        StackRoutines.copyStacks, htarget] using htwo
    · simp [result, StackRoutines.clearStacks ]
    · simp [result, StackRoutines.clearStacks ]
    · simpa [result, cleared, StackRoutines.clearStacks, mark] using hc
    · simpa [result, cleared, StackRoutines.clearStacks, mark] using ht
    · simpa [result, cleared, StackRoutines.clearStacks, mark, copied,
        StackRoutines.copyStacks, hcopyTemp] using hseven
  · simp [result, readRegs, ha]
  · simpa [result, cleared, StackRoutines.clearStacks, mark, copied,
      StackRoutines.copyStacks] using hzero
  · simp [result, StackRoutines.clearStacks]
  · simpa [result, cleared, readRegs, mark, copied] using hr7
  · simpa [result, cleared, readRegs, mark, copied] using hr8

theorem callback_contract (records : List (List Bool)) :
    RecordPrograms.CallbackContract ports callback (fun bits => !decide (bits ∈ records))
      (perRecordCost records) (invariant records) := by
  intro bits tail base hbase
  let d := RecordPrograms.state ports base false true false tail bits.reverse
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state, ports]
  have hd1 : d.stacks 1 = bits.reverse := by simp [d, RecordPrograms.state, ports]
  have hd7 : d.regs 7 = false := by simp [d, RecordPrograms.state, ports]
  have hd8 : d.regs 8 = true := by simp [d, RecordPrograms.state, ports]
  have hv : invariant records d := by
    simpa [invariant, d, RecordPrograms.state, ports] using hbase
  obtain ⟨n, hn, e, he, hv, ha, hs, hp, h7, h8⟩ := callback_eval bits records d hd1 hv
  have eState : RecordPrograms.state ports e false true (!decide (bits ∈ records)) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ (h7.trans hd7) (h8.trans hd8)
      ha (hs.trans hd0) hp
  refine ⟨n, e, hn, hv, ?_⟩
  rw [eState]
  exact he

theorem contains_eq_decide (bits : List Bool) (records : List (List Bool)) :
    ExecCNF.contains bits records = decide (bits ∈ records) := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem not_any_missing (source target : List (List Bool)) :
    (!(source.any (fun bits => !decide (bits ∈ target)))) = ExecCNF.subset source target := by
  induction source with
  | nil => rfl
  | cons bits rest ih =>
    simp only [List.any_cons, Bool.not_or, Bool.not_not, ExecCNF.subset,
      contains_eq_decide, ih]

theorem finish_eval (base : Data) (missing : Bool) (source : List Bool) :
    Eval finish 2 (RecordPrograms.state ports base false true missing source [])
      (RecordPrograms.state ports base false true (!missing) source [!missing]) := by
  have h1 : (StructuredProgram.Atom.bnot (r := 10) (s := 8) 9 9).eval
      (RecordPrograms.state ports base false true missing source []) =
      RecordPrograms.state ports base false true (!missing) source [] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state, ports]
  have h2 : (StructuredProgram.Atom.push (r := 10) (s := 8) 1 9).eval
      (RecordPrograms.state ports base false true (!missing) source []) =
      RecordPrograms.state ports base false true (!missing) source [!missing] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state, ports]
  have he1 : Eval (RecordPrograms.atom (.bnot 9 9)) 1
      (RecordPrograms.state ports base false true missing source [])
      (RecordPrograms.state ports base false true (!missing) source []) := by
    rw [← h1]
    exact .base (.atom _ _)
  have he2 : Eval (RecordPrograms.atom (.push 1 9)) 1
      (RecordPrograms.state ports base false true (!missing) source [])
      (RecordPrograms.state ports base false true (!missing) source [!missing]) := by
    rw [← h2]
    exact .base (.atom _ _)
  exact Eval.seq he1 he2

theorem subset_eval (source target : List (List Bool)) (suffix : List Bool)
    (base : Data) (valid : invariant target base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data),
      n ≤ 5 + RecordPrograms.budget (perRecordCost target) source ∧
      invariant target next ∧
      Eval subset n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList id source ++ suffix) [])
        (RecordPrograms.state ports next false true (ExecCNF.subset source target)
          (RecordPrograms.unread (fun bits => !decide (bits ∈ target)) source suffix)
          [ExecCNF.subset source target]) := by
  obtain ⟨n, next, hn, hnext, he⟩ := RecordPrograms.iterate_run ports callback
    (fun bits => !decide (bits ∈ target)) (perRecordCost target) (invariant target)
    (callback_contract target) source suffix base valid v pr f
  have hf := finish_eval next (source.any (fun bits => !decide (bits ∈ target)))
    (RecordPrograms.unread (fun bits => !decide (bits ∈ target)) source suffix)
  rw [not_any_missing] at hf
  exact ⟨n + 2, next, by omega, hnext, Eval.seq he hf⟩

/-- The bound accounts for every parsed bit, target copy, membership scan,
cleanup instruction, and loop test in the fixed subset program. -/
theorem budget_le (source target : List (List Bool)) :
    3 + RecordPrograms.budget (perRecordCost target) source ≤
      64 * ((Encoding.encodeList id target).length + 1) *
        (Encoding.encodeList id source).length := by
  induction source with
  | nil => simp only [RecordPrograms.budget, Encoding.encodeList, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.add_zero, Nat.mul_one]; omega
  | cons bits rest ih =>
    have hstep : 6 * bits.length + perRecordCost target bits + 7 ≤
        64 * ((Encoding.encodeList id target).length + 1) * (2 * bits.length + 2) := by
      dsimp [perRecordCost]
      nlinarith
    simp only [RecordPrograms.budget, Encoding.length_encodeList_cons, id_eq]
    calc
      3 + (6 * bits.length + perRecordCost target bits + 7 +
          RecordPrograms.budget (perRecordCost target) rest)
          = (6 * bits.length + perRecordCost target bits + 7) +
              (3 + RecordPrograms.budget (perRecordCost target) rest) := by omega
      _ ≤ 64 * ((Encoding.encodeList id target).length + 1) * (2 * bits.length + 2) +
          64 * ((Encoding.encodeList id target).length + 1) *
            (Encoding.encodeList id rest).length := Nat.add_le_add hstep ih
      _ = _ := by ring

theorem subset_runsIn (source target : List (List Bool)) (suffix : List Bool)
    (base : Data) (valid : invariant target base) (v pr f : Bool) :
    ∃ next : Data, invariant target next ∧
      RunsIn subsetProgram
        (64 * ((Encoding.encodeList id target).length + 1) *
          (Encoding.encodeList id source).length + 3)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList id source ++ suffix) []).withPC (some subsetProgram.entry))
        ((RecordPrograms.state ports next false true (ExecCNF.subset source target)
          (RecordPrograms.unread (fun bits => !decide (bits ∈ target)) source suffix)
          [ExecCNF.subset source target]).withPC none) := by
  obtain ⟨n, next, hn, hnext, he⟩ := subset_eval source target suffix base valid v pr f
  refine ⟨next, hnext, n + 1, ?_, compiled_halt_trace he 0 1⟩
  have hb := budget_le source target
  omega

theorem subset_call (source target : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id source) (hout : d.stacks 1 = [])
    (valid : invariant target d) :
    ∃ n ≤ 64 * ((Encoding.encodeList id target).length + 1) *
        (Encoding.encodeList id source).length + 3, ∃ e : Data,
      Eval (.call subsetProgram) n d e ∧ invariant target e ∧
      e.regs 9 = ExecCNF.subset source target ∧
      e.stacks 1 = [ExecCNF.subset source target] ∧
      (e.stacks 0).length ≤ (Encoding.encodeList id source).length := by
  obtain ⟨next, hnxt, n, hn, ht⟩ := subset_runsIn source target [] d valid
    (d.regs 7) (d.regs 8) (d.regs 9)
  have hs : RecordPrograms.state ports d (d.regs 7) (d.regs 8) (d.regs 9)
      (Encoding.encodeList id source ++ []) [] = d := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [ports] using hsource
    · exact hout
  rw [hs] at ht
  refine ⟨n, hn, _, Eval.call subsetProgram ht, ?_, ?_, ?_, ?_⟩
  · simpa [invariant, RecordPrograms.state, ports] using hnxt
  · simp [RecordPrograms.state, ports]
  · simp [RecordPrograms.state, ports]
  · simpa [RecordPrograms.state, ports] using
      unread_length_le (fun bits => !decide (bits ∈ target)) source

end SubexponentialSAT.ExecCNFSubset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

theorem regPort_injective : Function.Injective regPort := Fin.castAdd_injective 10 2
theorem stackPort_injective : Function.Injective stackPort := Fin.castAdd_injective 8 2

private theorem embed_restrict (d : Data) :
    embedState regPort stackPort d (restrict d) = d := by
  cases d with
  | mk regs stk =>
    unfold embedState restrict
    congr 1
    · funext i
      by_cases h : ∃ j, regPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact regPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stackPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact stackPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

/-- The subset routine has an actual trace. Its lifted call preserves the two
original clauses and the caller's two saved Boolean flags. -/
theorem subset_eval (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 0 = Encoding.encodeList id source) (ho : d.stacks 1 = [])
    (hv : ExecCNFSubset.invariant target (restrict d)) :
    ∃ n ≤ 64 * ((Encoding.encodeList id target).length + 1) *
        (Encoding.encodeList id source).length + 3, ∃ e : Data,
      Eval (.call subsetProgram) n d e ∧
      ExecCNFSubset.invariant target (restrict e) ∧
      e.regs 9 = ExecCNF.subset source target ∧
      e.stacks 1 = [ExecCNF.subset source target] ∧
      (e.stacks 0).length ≤ (Encoding.encodeList id source).length ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) ∧
      e.regs 10 = d.regs 10 ∧ e.regs 11 = d.regs 11 := by
  obtain ⟨n, hn, b, he, hb, hr, hout, hlen⟩ :=
    ExecCNFSubset.subset_call source target (restrict d) hs ho hv
  have ht : Trace ExecCNFSubset.subsetProgram n
      ((restrict d).withPC (some ExecCNFSubset.subsetProgram.entry)) (b.withPC none) := by
    cases he with
    | call _ h => exact h
  have heval := eval_call_lifted ExecCNFSubset.subsetProgram regPort stackPort d
    regPort_injective stackPort_injective ht
  rw [embed_restrict] at heval
  let e := embedState regPort stackPort d b
  have hstack (i : Fin 8) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stackPort_injective i
  have hreg (i : Fin 10) : e.regs (regPort i) = b.regs i :=
    embedState_register _ _ _ _ regPort_injective i
  have hre : restrict e = b := by
    cases b
    unfold restrict
    congr 1
    · funext i; exact hreg i
    · funext i; exact hstack i
  refine ⟨n, hn, e, heval, hre.symm ▸ hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hreg 9).trans hr
  · exact (hstack 1).trans hout
  · exact (congrArg List.length (hstack 0)).trans_le hlen
  · intro i
    apply embedState_stack_frame
    fin_cases i <;> decide
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

theorem copy_eval (src dst : Fin 10) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ 7) (htd : (7 : Fin 10) ≠ dst)
    (htmp : d.stacks 7 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  have h := StackRoutines.copyProgram_trace src dst 7 (0 : Fin 12) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

theorem clear_eval (port : Fin 10) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace port (0 : Fin 12) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

/-- A complete directional comparison restores all workspace, so the same
fixed routine can be invoked with the clause ports interchanged. -/
theorem compare_eval (source target : List (List Bool)) (i j : Fin 2) (d : Data)
    (hs : d.stacks (original i) = Encoding.encodeList id source)
    (ht : d.stacks (original j) = Encoding.encodeList id target) (hc : clean d) :
    ∃ n ≤ compareBound source target, ∃ e : Data,
      Eval (compare i j) n d e ∧ clean e ∧
      e.regs 9 = ExecCNF.subset source target ∧
      (∀ k : Fin 2, e.stacks (original k) = d.stacks (original k)) ∧
      e.regs 10 = d.regs 10 ∧ e.regs 11 = d.regs 11 := by
  have hi0 : original i ≠ 0 := by fin_cases i <;> decide
  have hi7 : original i ≠ 7 := by fin_cases i <;> decide
  have hj2 : original j ≠ 2 := by fin_cases j <;> decide
  have hj7 : original j ≠ 7 := by fin_cases j <;> decide
  have hj0 : original j ≠ 0 := by fin_cases j <;> decide
  let a := copied (original i) 0 d
  let b := copied (original j) 2 a
  have hc0 : d.stacks 0 = [] := hc 0
  have hc1 : d.stacks 1 = [] := hc 1
  have hc2 : d.stacks 2 = [] := hc 2
  have hc7 : d.stacks 7 = [] := hc 7
  have ha7 : a.stacks 7 = [] := by simpa [a, copied, StackRoutines.copyStacks] using hc7
  have haj : a.stacks (original j) = Encoding.encodeList id target := by
    simpa [a, copied, StackRoutines.copyStacks, hj0] using ht
  have hb0 : b.stacks 0 = Encoding.encodeList id source := by
    simp [b, a, copied, StackRoutines.copyStacks, hs, hc0]
  have hb1 : b.stacks 1 = [] := by
    simpa [b, a, copied, StackRoutines.copyStacks] using hc1
  have hbv : ExecCNFSubset.invariant target (restrict b) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [restrict, stackPort, b, a, copied, StackRoutines.copyStacks, hj0, ht, hc2]
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 3
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 4
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 5
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 6
    · simpa [restrict, stackPort, b, a, copied, StackRoutines.copyStacks] using hc 7
  obtain ⟨m, hm, e, he, hv, hr, hout, hlen, hframe, h10, h11⟩ :=
    subset_eval source target b hb0 hb1 hbv
  let result := cleared 2 (cleared 1 (cleared 0 e))
  let count := (7 * (d.stacks (original i)).length + 5) +
    ((7 * (a.stacks (original j)).length + 5) +
      (m + ((2 * (e.stacks 0).length + 3) +
        ((2 * (e.stacks 1).length + 3) + (2 * (e.stacks 2).length + 3)))))
  have he2 : e.stacks 2 = Encoding.encodeList id target := hv.1
  refine ⟨count, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [count, compareBound]
    rw [hs, haj, hout, he2]
    simp only [List.length_cons, List.length_nil]
    nlinarith
  · apply Eval.seq (copy_eval _ _ d hi0 hi7 (by decide) hc7)
    apply Eval.seq (copy_eval _ _ a hj2 hj7 (by decide) ha7)
    apply Eval.seq he
    apply Eval.seq (clear_eval 0 e)
    apply Eval.seq (clear_eval 1 (cleared 0 e))
    simpa [result, cleared, StackRoutines.clearStacks] using
      clear_eval 2 (cleared 1 (cleared 0 e))
  · intro k
    fin_cases k
    · simp [result, cleared, StackRoutines.clearStacks, stackPort]
    · simp [result, cleared, StackRoutines.clearStacks, stackPort]
    · simp [result, cleared, StackRoutines.clearStacks, stackPort]
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.2.2.1
    · simpa [result, cleared, StackRoutines.clearStacks, restrict, stackPort] using hv.2.2.2.2.2
  · simpa [result, cleared, readRegs] using hr
  · intro k
    have hk0 : original k ≠ 0 := by fin_cases k <;> decide
    have hk1 : original k ≠ 1 := by fin_cases k <;> decide
    have hk2 : original k ≠ 2 := by fin_cases k <;> decide
    simpa [result, cleared, StackRoutines.clearStacks, b, a, copied,
      StackRoutines.copyStacks, hk0, hk1, hk2] using hframe k
  · simpa [result, cleared, readRegs, b, a, copied] using h10
  · simpa [result, cleared, readRegs, b, a, copied] using h11

theorem save_eval (d : Data) : Eval save 1 d (saved d) :=
  .base (.atom _ _)

theorem combine_eval (d : Data) : Eval combine 3 d (combined d) :=
  .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

/-- The same execution also exposes the reverse-inclusion failure bit, used
to reject a proposed core that is not contained in a candidate clause. -/
theorem command_eval_all (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ n, n + 1 ≤ bound source target ∧ ∃ e : Data,
      Eval command n d e ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) ∧
      e.regs 9 = !(ExecCNF.subset target source) := by
  obtain ⟨n, hn, e, he, hclean, hforward, hframe, h10, h11⟩ :=
    compare_eval source target 0 1 d hs ht hc
  have hs' : (saved e).stacks (original 1) = Encoding.encodeList id target :=
    (hframe 1).trans ht
  have ht' : (saved e).stacks (original 0) = Encoding.encodeList id source :=
    (hframe 0).trans hs
  obtain ⟨m, hm, f, hf, hclean', hbackward, hframe', h10', h11'⟩ :=
    compare_eval target source 1 0 (saved e) hs' ht' hclean
  have hremember : f.regs 11 = ExecCNF.subset source target := by
    simpa [saved, hforward] using h11'
  refine ⟨n + (1 + (m + 3)), ?_, combined f,
    Eval.seq he (Eval.seq (save_eval e) (Eval.seq hf (combine_eval f))), ?_, ?_, ?_, ?_, ?_⟩
  · have hle : n + (1 + (m + 3)) + 1 ≤
        compareBound source target + compareBound target source + 5 := by omega
    calc
      n + (1 + (m + 3)) + 1 ≤
          compareBound source target + compareBound target source + 5 := hle
      _ ≤ bound source target := by
        dsimp [bound, compareBound]
        ring_nf
        omega
  · exact hclean'
  · simp [hremember, hbackward, ExecCNF.equivalent]
  · simp [hremember, hbackward, ExecCNF.strictSubset]
  · intro i
    exact (hframe' i).trans (hframe i)
  · simp [hbackward]

theorem program_runsIn_all (source target : List (List Bool)) (d : Data)
    (hs : d.stacks 8 = Encoding.encodeList id source)
    (ht : d.stacks 9 = Encoding.encodeList id target) (hc : clean d) :
    ∃ e : Data, RunsIn program (bound source target)
      (d.withPC (some program.entry)) (e.withPC none) ∧ clean e ∧
      e.regs 10 = ExecCNF.equivalent source target ∧
      e.regs 11 = ExecCNF.strictSubset source target ∧
      (∀ i : Fin 2, e.stacks (original i) = d.stacks (original i)) ∧
      e.regs 9 = !(ExecCNF.subset target source) := by
  obtain ⟨n, hn, e, he, hclean, heq, hstrict, hframe, hreverse⟩ :=
    command_eval_all source target d hs ht hc
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 8 0⟩, hclean, heq, hstrict, hframe, hreverse⟩

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordMappedPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual record iteration over encoded logical values

The instruction sequence is `RecordPrograms.iterate`. The contract below is
required only for payloads emitted by the supplied encoder. It does not ask a
callback for correct behavior on malformed encodings, and it does not install
the encoder, test, or cost function as a machine instruction.
-/

namespace SubexponentialSAT.RecordMappedPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {α : Type*} {r s : ℕ}

theorem loop_run (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop)
    (contract : Contract p callback enc test cost invariant)
    (values : List α) (suffix : List Bool) (base : State r s)
    (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget enc cost values ∧ invariant next ∧
      Eval (RecordPrograms.loop p callback) n (afterTag p enc base values suffix)
        (state p next false true (values.any test) (unread enc test values suffix) []) := by
  induction values generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons a rest ih =>
      let tail := Encoding.encodeList enc rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, hcallback⟩ := contract a tail base valid
      have hreader : Eval (reader p) (6 * (enc a).length + 4)
          (afterTag p enc base (a :: rest) suffix)
          (state p base false true false tail (enc a).reverse) := by
        simpa [afterTag, tail] using reader_eval p base (enc a) tail [] true true false
      have hguard : (afterTag p enc base (a :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test a with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test a) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (RecordPrograms.loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * (enc a).length + 4 + (n + 2)) + 1 + 1, middle, ?_, hmiddle, ?_⟩
          · simp only [budget]
            omega
          · simpa [RecordPrograms.loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test a) tail [])
              (afterTag p enc middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p enc middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hrest⟩ := ih middle hmiddle
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * (enc a).length + 4 + (n + 2)) + m + 1, next, ?_, hnext, ?_⟩
          · simp only [budget]
            omega
          · simpa [RecordPrograms.loop, body, unread, ht] using hrun

/-- Genuine execution of one fixed iterator over any list of encodable values.
The encoder appears only in the input/output specification and bound. -/
theorem iterate_run (p : Ports r s) (callback : Cmd r s) (enc : α → List Bool)
    (test : α → Bool) (cost : α → ℕ) (invariant : State r s → Prop)
    (contract : Contract p callback enc test cost invariant)
    (values : List α) (suffix : List Bool) (base : State r s)
    (valid : invariant base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget enc cost values ∧ invariant next ∧
      Eval (RecordPrograms.iterate p callback) n
        (state p base v pr f (Encoding.encodeList enc values ++ suffix) [])
        (state p next false true (values.any test) (unread enc test values suffix) []) := by
  obtain ⟨n, next, hn, hnext, hloop⟩ := loop_run p callback enc test cost invariant contract
    values suffix base valid
  refine ⟨1 + (1 + n), next, by omega, hnext, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p enc base values suffix v pr) hloop)

theorem unread_length_le (enc : α → List Bool) (test : α → Bool)
    (values : List α) (suffix : List Bool) :
    (unread enc test values suffix).length ≤
      (Encoding.encodeList enc values).length + suffix.length := by
  induction values with
  | nil => simp [unread, Encoding.encodeList]
  | cons a rest ih =>
      cases h : test a <;>
        simp [unread, h, Encoding.length_encodeList_cons] ; omega

/-- A linear bound in the actual encoded input length, provided the callback
bound is linear in its current encoded payload length. -/
theorem program_budget_le_input (enc : α → List Bool) (cost : α → ℕ)
    (values : List α) (a b : ℕ)
    (hcost : ∀ x ∈ values, cost x ≤ a * (enc x).length + b) :
    4 + budget enc cost values ≤
      (a + b + 17) * ((Encoding.encodeList enc values).length + 1) := by
  induction values with
  | nil => simp [budget, Encoding.encodeList]; omega
  | cons x xs ih =>
      have hx := hcost x (by simp)
      have ht := ih (fun y hy => hcost y (by simp [hy]))
      simp only [budget, Encoding.length_encodeList_cons]
      nlinarith

end SubexponentialSAT.RecordMappedPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clause-relation scans over encoded formulas

All modes use a fixed finite Boolean program. An outer record iterator parses
each encoded clause, then invokes the concrete preserving clause-relation
program. The query clause is preserved for callers that subsequently emit it.
-/
namespace SubexponentialSAT.ExecClauseRelationScan
open BitProgram StructuredCalls

theorem regPort_injective : Function.Injective regPort := Fin.castAdd_injective 12 3
theorem stackPort_injective : Function.Injective stackPort := Fin.castAdd_injective 10 2

private theorem embed_restrict (d : Data) :
    embedState regPort stackPort d (restrict d) = d := by
  cases d with
  | mk regs stk =>
    unfold embedState restrict
    congr 1
    · funext i
      by_cases h : ∃ j, regPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact regPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stackPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact stackPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

theorem relation_eval (C Q : Clause) (d : Data)
    (hc : d.stacks 8 = encodeClause C) (hq : d.stacks 9 = encodeClause Q)
    (hw : clean d) :
    ∃ n ≤ ExecClauseRelationsProgram.bound C Q, ∃ e : Data,
      Eval (.call relationProgram) n d e ∧ clean e ∧
      (∀ mode, e.regs (resultRegister mode) = test mode C Q) ∧
      e.stacks 8 = d.stacks 8 ∧ e.stacks 9 = d.stacks 9 ∧
      e.stacks 10 = d.stacks 10 ∧ e.stacks 11 = d.stacks 11 ∧
      e.regs 12 = d.regs 12 ∧ e.regs 13 = d.regs 13 ∧ e.regs 14 = d.regs 14 := by
  have hclean : ExecClauseRelationsProgram.clean (restrict d) := hw
  obtain ⟨b, ⟨n, hn, ht⟩, hb, heq, hstrict, hframe, hreverse⟩ :=
    ExecClauseRelationsProgram.program_runsIn_all C Q (restrict d) hc hq hclean
  have heval := eval_call_lifted ExecClauseRelationsProgram.program regPort stackPort d
    regPort_injective stackPort_injective ht
  rw [embed_restrict] at heval
  let e := embedState regPort stackPort d b
  have hstack (i : Fin 10) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stackPort_injective i
  have hreg (i : Fin 12) : e.regs (regPort i) = b.regs i :=
    embedState_register _ _ _ _ regPort_injective i
  refine ⟨n, hn, e, heval, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hstack (Fin.castAdd 2 i)).trans (hb i)
  · intro mode
    cases mode with
    | equivalent => exact (hreg 10).trans heq
    | strictSubset => exact (hreg 11).trans hstrict
    | missingCore => exact (hreg 9).trans hreverse
  · exact (hstack 8).trans (hframe 0)
  · exact (hstack 9).trans (hframe 1)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

theorem transfer_eval (d : Data) :
    Eval transfer (3 * (d.stacks 11).length + 3) d (transferred d) := by
  have h := StackRoutines.transferProgram_trace (r := 15) (s := 12)
    11 8 0 1 (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  apply Eval.call
  simpa [transferred, transferProgram, StackRoutines.transferResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem clearCandidate_eval (d : Data) :
    Eval clearCandidate (2 * (d.stacks 8).length + 3) d (cleared d) := by
  have h := StackRoutines.clearProgram_trace (r := 15) (s := 12) 8 0 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

theorem mark_eval (mode : Mode) (d : Data) :
    Eval (RecordPrograms.atom (.copy 14 (resultRegister mode))) 1 d (marked mode d) :=
  .base (.atom _ _)

theorem callback_eval (mode : Mode) (C Q : Clause) (d : Data)
    (hp : d.stacks 11 = (encodeClause C).reverse) (valid : invariant Q d) :
    ∃ n ≤ perClauseCost Q (encodeClause C), ∃ e : Data,
      Eval (callback mode) n d e ∧ invariant Q e ∧ e.regs 14 = test mode C Q ∧
      e.stacks 10 = d.stacks 10 ∧ e.stacks 11 = [] ∧
      e.regs 12 = d.regs 12 ∧ e.regs 13 = d.regs 13 := by
  obtain ⟨hq, hw⟩ := valid
  have h8 : d.stacks 8 = [] := hw 8
  have hc : (transferred d).stacks 8 = encodeClause C := by
    simp [transferred, StackRoutines.transferStacks, hp, h8]
  have hq' : (transferred d).stacks 9 = encodeClause Q := by
    simpa [transferred, StackRoutines.transferStacks] using hq
  have hw' : clean (transferred d) := by
    intro i
    have h := hw (Fin.castAdd 1 i)
    have hcast : Fin.castAdd 3 (Fin.castAdd 1 i) = Fin.castAdd 4 i := Fin.ext rfl
    rw [hcast] at h
    have hi8 : Fin.castAdd 4 i ≠ (8 : Fin 12) := by
      intro h
      have hv : i.val = 8 := congrArg Fin.val h
      omega
    have hi11 : Fin.castAdd 4 i ≠ (11 : Fin 12) := by
      intro h
      have hv : i.val = 11 := congrArg Fin.val h
      omega
    simpa [transferred, StackRoutines.transferStacks, hi8, hi11] using h
  obtain ⟨n, hn, e, he, hclean, hanswer, h8e, h9e, h10e, h11e, h12e, h13e, h14e⟩ :=
    relation_eval C Q (transferred d) hc hq' hw'
  let result := cleared (marked mode e)
  let count := (3 * (d.stacks 11).length + 3) +
    (n + (1 + (2 * (e.stacks 8).length + 3)))
  refine ⟨count, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [count, perClauseCost]
    rw [hp, h8e, hc]
    simp only [List.length_reverse]
    dsimp [ExecClauseRelationsProgram.bound, encodeClause] at hn ⊢
    have hfactor : (Encoding.encodeList id C).length + 1 ≤
        ((Encoding.encodeList id C).length + 1) *
          ((Encoding.encodeList id Q).length + 1) := by
      calc
        (Encoding.encodeList id C).length + 1 =
            ((Encoding.encodeList id C).length + 1) * 1 := by omega
        _ ≤ ((Encoding.encodeList id C).length + 1) *
            ((Encoding.encodeList id Q).length + 1) := by
          exact Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.mul_assoc] at hn ⊢
    omega
  · exact Eval.seq (transfer_eval d)
      (Eval.seq he (Eval.seq (mark_eval mode e) (clearCandidate_eval (marked mode e))))
  · refine ⟨?_, ?_⟩
    · simpa [result, cleared, marked, StackRoutines.clearStacks] using h9e.trans hq'
    · intro i
      by_cases hi : i.val = 8
      · have hi' : Fin.castAdd 3 i = (8 : Fin 12) := Fin.ext hi
        simp [hi', result, cleared, StackRoutines.clearStacks]
      · have hil : i.val < 8 := by omega
        have h := hclean ⟨i.val, hil⟩
        have hcast : Fin.castAdd 4 (⟨i.val, hil⟩ : Fin 8) =
            Fin.castAdd 3 i := Fin.ext rfl
        rw [hcast] at h
        have hi8 : Fin.castAdd 3 i ≠ (8 : Fin 12) := by
          intro h
          have hv : i.val = 8 := congrArg Fin.val h
          omega
        simpa [result, cleared, marked, StackRoutines.clearStacks, hi8] using h
  · simpa [result, cleared, readRegs, marked] using hanswer mode
  · simpa [result, cleared, marked, StackRoutines.clearStacks, transferred,
      StackRoutines.transferStacks] using h10e
  · simpa [result, cleared, marked, StackRoutines.clearStacks, transferred,
      StackRoutines.transferStacks] using h11e
  · simpa [result, cleared, marked, readRegs, transferred] using h12e
  · simpa [result, cleared, marked, readRegs, transferred] using h13e

theorem callback_contract (mode : Mode) (Q : Clause) :
    RecordMappedPrograms.Contract ports (callback mode) encodeClause
      (fun C => test mode C Q) (fun C => perClauseCost Q (encodeClause C)) (invariant Q) := by
  intro C tail base hbase
  let d := RecordPrograms.state ports base false true false tail (encodeClause C).reverse
  have hd10 : d.stacks 10 = tail := by simp [d, RecordPrograms.state, ports]
  have hd11 : d.stacks 11 = (encodeClause C).reverse := by
    simp [d, RecordPrograms.state, ports]
  have hd12 : d.regs 12 = false := by simp [d, RecordPrograms.state, ports]
  have hd13 : d.regs 13 = true := by simp [d, RecordPrograms.state, ports]
  have hv : invariant Q d := by
    refine ⟨?_, ?_⟩
    · simpa [d, RecordPrograms.state, ports] using hbase.1
    · intro i
      have hi10 : Fin.castAdd 3 i ≠ (10 : Fin 12) := by
        intro h
        have hv : i.val = 10 := congrArg Fin.val h
        omega
      have hi11 : Fin.castAdd 3 i ≠ (11 : Fin 12) := by
        intro h
        have hv : i.val = 11 := congrArg Fin.val h
        omega
      simpa [d, RecordPrograms.state, ports, hi10, hi11] using hbase.2 i
  obtain ⟨n, hn, e, he, hv, ha, h10, h11, h12, h13⟩ := callback_eval mode C Q d hd11 hv
  have heState : RecordPrograms.state ports e false true (test mode C Q) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ (h12.trans hd12) (h13.trans hd13)
      ha (h10.trans hd10) h11
  refine ⟨n, e, hn, hv, ?_⟩
  rw [heState]
  exact he

theorem emit_eval (base : Data) (answer : Bool) (source : List Bool) :
    Eval (RecordPrograms.atom (.push 11 14)) 1
      (RecordPrograms.state ports base false true answer source [])
      (RecordPrograms.state ports base false true answer source [answer]) := by
  have h : (StructuredProgram.Atom.push (r := 15) (s := 12) 11 14).eval
      (RecordPrograms.state ports base false true answer source []) =
      RecordPrograms.state ports base false true answer source [answer] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state, ports]
  rw [← h]
  exact .base (.atom _ _)

theorem command_eval (mode : Mode) (F : Formula) (Q : Clause) (suffix : List Bool)
    (base : Data) (valid : invariant Q base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data),
      n ≤ 4 + RecordMappedPrograms.budget encodeClause
        (fun C => perClauseCost Q (encodeClause C)) F ∧ invariant Q next ∧
      Eval (command mode) n
        (RecordPrograms.state ports base v pr f (encodeFormula F ++ suffix) [])
        (RecordPrograms.state ports next false true (F.any (fun C => test mode C Q))
          (RecordMappedPrograms.unread encodeClause (fun C => test mode C Q) F suffix)
          [F.any (fun C => test mode C Q)]) := by
  obtain ⟨n, next, hn, hnext, he⟩ := RecordMappedPrograms.iterate_run ports (callback mode)
    encodeClause (fun C => test mode C Q) (fun C => perClauseCost Q (encodeClause C))
    (invariant Q) (callback_contract mode Q) F suffix base valid v pr f
  exact ⟨n + 1, next, by omega, hnext, Eval.seq he (emit_eval _ _ _)⟩

theorem budget_le (F : Formula) (Q : Clause) :
    4 + RecordMappedPrograms.budget encodeClause
        (fun C => perClauseCost Q (encodeClause C)) F ≤
      400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) := by
  have hb := RecordMappedPrograms.program_budget_le_input encodeClause
    (fun C => perClauseCost Q (encodeClause C)) F
    (180 * ((encodeClause Q).length + 1)) (180 * ((encodeClause Q).length + 1)) (by
      intro C _
      dsimp [perClauseCost]
      nlinarith)
  dsimp [encodeFormula] at ⊢
  nlinarith

theorem program_call (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (hs : d.stacks 10 = encodeFormula F) (hp : d.stacks 11 = [])
    (hv : invariant Q d) :
    ∃ n ≤ bound F Q, ∃ e : Data,
      Eval (.call (program mode)) n d e ∧ invariant Q e ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] ∧
      (e.stacks 10).length ≤ (encodeFormula F).length := by
  obtain ⟨n, next, hn, hnext, he⟩ := command_eval mode F Q [] d hv
    (d.regs 12) (d.regs 13) (d.regs 14)
  have hstart : RecordPrograms.state ports d (d.regs 12) (d.regs 13) (d.regs 14)
      (encodeFormula F ++ []) [] = d := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · rw [show ports.source = (10 : Fin 12) from rfl]
      simpa only [List.append_nil] using hs
    · exact hp
  rw [hstart] at he
  have ht := compiled_halt_trace he 10 11
  refine ⟨n + 1, ?_, _, Eval.call (program mode) ht, ?_, ?_, ?_, ?_⟩
  · have hb := budget_le F Q
    dsimp [bound]
    omega
  · refine ⟨?_, ?_⟩
    · simpa [RecordPrograms.state, ports] using hnext.1
    · intro i
      have hi10 : Fin.castAdd 3 i ≠ (10 : Fin 12) := by
        intro h
        have hv : i.val = 10 := congrArg Fin.val h
        omega
      have hi11 : Fin.castAdd 3 i ≠ (11 : Fin 12) := by
        intro h
        have hv : i.val = 11 := congrArg Fin.val h
        omega
      simpa [RecordPrograms.state, ports, hi10, hi11] using hnext.2 i
  · simp [RecordPrograms.state, ports]
  · simp [RecordPrograms.state, ports]
  · simpa [RecordPrograms.state, ports, encodeFormula] using
      RecordMappedPrograms.unread_length_le encodeClause (fun C => test mode C Q) F []

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A preserving wrapper for repeated clause-vs-formula scans. A real copy of
the full formula is scanned, and its residual copy is explicitly cleared. -/
namespace SubexponentialSAT.ExecClauseRelationScan.Preserving
open BitProgram StructuredCalls

theorem stackPort_injective : Function.Injective stackPort := Fin.castAdd_injective 12 1

private theorem embed_restrict (d : Data) :
    embedState id stackPort d (restrict d) = d := by
  cases d with
  | mk regs stk =>
    unfold embedState restrict
    congr 1
    · funext i
      exact Function.injective_id.extend_apply _ _ i
    · funext i
      by_cases h : ∃ j, stackPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact stackPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

theorem scan_eval (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (hs : d.stacks 10 = encodeFormula F) (hp : d.stacks 11 = [])
    (hv : ExecClauseRelationScan.invariant Q (restrict d)) :
    ∃ n ≤ ExecClauseRelationScan.bound F Q, ∃ e : Data,
      Eval (.call (scanner mode)) n d e ∧
      ExecClauseRelationScan.invariant Q (restrict e) ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] ∧
      (e.stacks 10).length ≤ (encodeFormula F).length ∧
      e.stacks 12 = d.stacks 12 := by
  obtain ⟨n, hn, b, he, hb, hr, hout, hlen⟩ :=
    ExecClauseRelationScan.program_call mode F Q (restrict d) hs hp hv
  have ht : Trace (ExecClauseRelationScan.program mode) n
      ((restrict d).withPC (some (ExecClauseRelationScan.program mode).entry))
      (b.withPC none) := by
    cases he with
    | call _ h => exact h
  have heval := eval_call_lifted (ExecClauseRelationScan.program mode) id stackPort d
    Function.injective_id stackPort_injective ht
  rw [embed_restrict] at heval
  let e := embedState id stackPort d b
  have hstack (i : Fin 12) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stackPort_injective i
  have hreg (i : Fin 15) : e.regs i = b.regs i :=
    embedState_register _ _ _ _ Function.injective_id i
  have hre : restrict e = b := by
    cases b
    unfold restrict
    congr 1
    · funext i; exact hreg i
    · funext i; exact hstack i
  exact ⟨n, hn, e, heval, hre.symm ▸ hb, (hreg 14).trans hr,
    (hstack 11).trans hout, (congrArg List.length (hstack 10)).trans_le hlen,
    embedState_stack_frame _ _ _ _ _ (by decide)⟩

theorem copyFormula_eval (d : Data) (htmp : d.stacks 8 = []) :
    Eval copyFormula (7 * (d.stacks 12).length + 5) d (copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 15) (s := 13)
    12 10 8 0 1 (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

theorem clearSource_eval (d : Data) :
    Eval clearSource (2 * (d.stacks 10).length + 3) d (cleared d) := by
  have h := StackRoutines.clearProgram_trace (r := 15) (s := 13) 10 0 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

/-- Both the original formula and query survive the scan. Only the output
singleton must be consumed before invoking another preserving scan. -/
theorem command_eval (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (valid : invariant F Q d) (hout : d.stacks 11 = []) :
    ∃ n, n + 1 ≤ bound F Q ∧ ∃ e : Data,
      Eval (command mode) n d e ∧ invariant F Q e ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] := by
  obtain ⟨hformula, hbase, hsource⟩ := valid
  have htmp : d.stacks 8 = [] := hbase.2 8
  have hs : (copied d).stacks 10 = encodeFormula F := by
    simp [copied, StackRoutines.copyStacks, hformula, hsource]
  have hp : (copied d).stacks 11 = [] := by
    simpa [copied, StackRoutines.copyStacks] using hout
  have hv : ExecClauseRelationScan.invariant Q (restrict (copied d)) := by
    refine ⟨?_, ?_⟩
    · simpa [restrict, stackPort, copied, StackRoutines.copyStacks] using hbase.1
    · intro i
      have hi10 : stackPort (Fin.castAdd 3 i) ≠ (10 : Fin 13) := by
        intro h
        have hv : i.val = 10 := congrArg Fin.val h
        omega
      simpa [restrict, copied, StackRoutines.copyStacks, hi10] using hbase.2 i
  obtain ⟨n, hn, e, he, hv, hr, hp, hlen, hf⟩ := scan_eval mode F Q (copied d) hs hp hv
  let result := cleared e
  let count := (7 * (d.stacks 12).length + 5) + (n + (2 * (e.stacks 10).length + 3))
  refine ⟨count, ?_, result, Eval.seq (copyFormula_eval d htmp) (Eval.seq he (clearSource_eval e)),
    ?_, ?_, ?_⟩
  · dsimp [count, bound]
    rw [hformula]
    dsimp [ExecClauseRelationScan.bound] at hn
    have hmargin :
        400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) +
            9 * (encodeFormula F).length + 10 ≤
          512 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) := by
      nlinarith only [Nat.zero_le (encodeClause Q).length,
        Nat.zero_le (encodeFormula F).length]
    calc
      7 * (encodeFormula F).length + 5 + (n + (2 * (e.stacks 10).length + 3)) + 1 ≤
          400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) +
            9 * (encodeFormula F).length + 10 := by omega
      _ ≤ 512 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) := hmargin
  · refine ⟨?_, ?_, ?_⟩
    · simpa [result, cleared, copied, StackRoutines.clearStacks,
        StackRoutines.copyStacks, hformula] using hf
    · refine ⟨?_, ?_⟩
      · simpa [restrict, stackPort, result, cleared, StackRoutines.clearStacks] using hv.1
      · intro i
        have hi10 : stackPort (Fin.castAdd 3 i) ≠ (10 : Fin 13) := by
          intro h
          have hv : i.val = 10 := congrArg Fin.val h
          omega
        simpa [restrict, result, cleared, StackRoutines.clearStacks, hi10] using hv.2 i
    · simp [result, cleared, StackRoutines.clearStacks]
  · simpa [result, cleared, readRegs] using hr
  · simpa [result, cleared, StackRoutines.clearStacks] using hp

theorem program_runsIn (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (valid : invariant F Q d) (hout : d.stacks 11 = []) :
    ∃ e : Data, RunsIn (program mode) (bound F Q)
      (d.withPC (some (program mode).entry)) (e.withPC none) ∧ invariant F Q e ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] := by
  obtain ⟨n, hn, e, he, hv, hr, hp⟩ := command_eval mode F Q d valid hout
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 12 11⟩, hv, hr, hp⟩

end SubexponentialSAT.ExecClauseRelationScan.Preserving

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFiltersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact-order clause filters on encoded formulas

The relation scanner occupies stacks 0--12. The outer record pass uses stack
13 for unread records, stack 14 for the reversed output record list, and stack
15 for the reversed current payload. Two stack transfers put a clause into the
scanner and return it to the existing frame emitter.
-/


namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)

theorem scanStack_injective : Function.Injective scanStack := Fin.castAdd_injective 13 3

private theorem embed_smallState (frameRegs regs : Regs)
    (query0 answer0 master0 query answer master source output payload : List Bool) :
    embedState id scanStack (state frameRegs query0 answer0 master0 source output payload)
      (smallState regs query answer master) = state regs query answer master source output payload := by
  apply embedState_eq_of_ports id scanStack _ _ _ Function.injective_id scanStack_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hlo : 13 ≤ i.val := by
      by_contra h
      have hil : i.val < 13 := by omega
      exact hi ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    fin_cases i <;> simp_all [state]

theorem scan_eval_oai (mode : Mode) (F : Formula) (Q : Clause) (regs : Regs)
    (source output : List Bool) :
    ∃ (n : ℕ) (rf : Regs), n ≤ ExecClauseRelationScan.Preserving.bound F Q ∧
      rf 14 = F.any (fun C => test mode C Q) ∧
      Eval (scan mode) n
        (state regs (encodeClause Q) [] (encodeFormula F) source output [])
        (state rf (encodeClause Q) [F.any (fun C => test mode C Q)]
          (encodeFormula F) source output []) := by
  let start := smallState regs (encodeClause Q) [] (encodeFormula F)
  have hv : ExecClauseRelationScan.Preserving.invariant F Q start := by
    refine ⟨rfl, ⟨rfl, ?_⟩, rfl⟩
    intro i
    fin_cases i <;> rfl
  obtain ⟨e, ⟨n, hn, htrace⟩, he, hr, ho⟩ :=
    ExecClauseRelationScan.Preserving.program_runsIn mode F Q start hv rfl
  have heq : e = smallState e.regs (encodeClause Q)
      [F.any (fun C => test mode C Q)] (encodeFormula F) := by
    have hs : e.stacks = (smallState e.regs (encodeClause Q)
        [F.any (fun C => test mode C Q)] (encodeFormula F)).stacks := by
      funext i
      fin_cases i
      · exact he.2.1.2 0
      · exact he.2.1.2 1
      · exact he.2.1.2 2
      · exact he.2.1.2 3
      · exact he.2.1.2 4
      · exact he.2.1.2 5
      · exact he.2.1.2 6
      · exact he.2.1.2 7
      · exact he.2.1.2 8
      · exact he.2.1.1
      · exact he.2.2
      · exact ho
      · exact he.1
    cases e
    cases hs
    rfl
  have hcall := eval_call_lifted (ExecClauseRelationScan.Preserving.program mode)
    id scanStack (state regs (encodeClause Q) [] (encodeFormula F) source output [])
    Function.injective_id scanStack_injective htrace
  rw [heq] at hcall
  change Eval (scan mode) n
    (embedState id scanStack _ (smallState regs (encodeClause Q) [] (encodeFormula F))) _ at hcall
  rw [embed_smallState, embed_smallState] at hcall
  exact ⟨n, e.regs, hn, hr, hcall⟩

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval_oai := @OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval_oai
