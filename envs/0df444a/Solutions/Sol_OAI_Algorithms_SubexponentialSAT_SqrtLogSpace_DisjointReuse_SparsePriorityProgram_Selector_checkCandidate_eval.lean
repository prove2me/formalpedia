-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:24:28.348555+00:00
-- url     : https://prove2.me/submissions/1350c5d9-f5ea-4140-9853-834ab9e03c49

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

theorem nat_pop (b v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem nat_present (v : Bool) (input output : List Bool) :
    step natProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem nat_true (input output : List Bool) :
    step natProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem nat_push (input output : List Bool) :
    step natProgram (cfg (some 3) true true input output) =
      some (cfg (some 0) true true input (true :: output)) := by
  simp [step, cfg, execInstr]

theorem nat_false (input output : List Bool) :
    step natProgram (cfg (some 2) false true input output) =
      some (cfg (some 4) false true input output) := by
  simp [step, cfg, execInstr]

theorem nat_halt (v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 4) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem nat_cycle (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (true :: input) output)
      (cfg (some 0) true true input (true :: output)) :=
  .cons (nat_pop true v p input output)
    (.cons (nat_present true input output)
      (.cons (nat_true input output) (.cons (nat_push input output) (.refl _))))

theorem nat_finish (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (nat_pop false v p input output)
    (.cons (nat_present false input output)
      (.cons (nat_false input output) (.cons (nat_halt false true input output) (.refl _))))

/-- The count is data on stack 1, rather than an input-dependent control state. -/
theorem nat_trace (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using nat_finish v p rest output
  | succ n ih =>
      have h := (nat_cycle v p (Encoding.encodeNat n ++ rest) output).trans
        (ih (true :: output) true true)
      have ht : 4 + (4 * n + 4) = 4 * (n + 1) + 4 := by omega
      have hin : Encoding.encodeNat (n + 1) ++ rest =
          true :: (Encoding.encodeNat n ++ rest) := by
        simp [Encoding.encodeNat, List.replicate_succ]
      simpa only [ht, hin, List.replicate_succ', List.append_assoc,
        List.singleton_append] using h

/-! ## In-place removal of one escape frame -/

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FrontendProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual initialization of the canonical SAT input

The nineteen-label program splits the variable-count header and counts its
unary marks into a binary stack word. The untouched encoded CNF body remains
on stack 0. All growing values live on Boolean stacks, not in finite control.
-/

namespace SubexponentialSAT.FrontendProgram

open SubexponentialSAT.BitProgram

theorem extend_parser_regs (b p : Bool) :
    Function.extend (Fin.castSucc : Fin 2 → Fin 3) (ParserProgram.pair b p)
      (CounterPrograms.counterRegs false false false) = CounterPrograms.counterRegs b p false := by
  funext i
  fin_cases i
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 0
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castSucc = (2 : Fin 3) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_parser_stacks (body unary : List Bool) :
    Function.extend (Fin.castAdd 2 : Fin 2 → Fin 4) (ParserProgram.pair body unary)
      (storage [] [] [] []) = storage body unary [] [] := by
  funext i
  fin_cases i
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 0
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (2 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (3 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 3 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_counter_stacks (body unary binary scratch : List Bool) :
    Function.extend (Fin.succ : Fin 3 → Fin 4)
      (CounterPrograms.lengthStacks unary binary scratch) (storage body [] [] []) =
      storage body unary binary scratch := by
  funext i
  fin_cases i
  · have hn : ¬ ∃ j : Fin 3, j.succ = (0 : Fin 4) := by simp
    exact Function.extend_apply' _ _ _ hn
  · exact (Fin.succ_injective 3).extend_apply _ _ 0
  · exact (Fin.succ_injective 3).extend_apply _ _ 1
  · exact (Fin.succ_injective 3).extend_apply _ _ 2

@[simp] theorem embed_parser (pc : Option (Fin 5)) (b p : Bool) (body unary : List Bool) :
    ProgramLinking.embedCfg Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5)
      emptyFrame (ParserProgram.cfg pc b p body unary) =
      cfg (ProgramLinking.relocatePc (Fin.castAdd 14) (some 5) pc) b p body unary [] [] := by
  simp [ProgramLinking.embedCfg, emptyFrame, cfg, ParserProgram.cfg,
    extend_parser_regs, extend_parser_stacks]

@[simp] theorem embed_counter (pc : Option (Fin 14)) (b p : Bool)
    (body unary binary scratch : List Bool) :
    ProgramLinking.embedCfg id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
      (⟨pc, CounterPrograms.counterRegs b p false,
        CounterPrograms.lengthStacks unary binary scratch⟩ : Cfg 3 3 14) =
      cfg (ProgramLinking.relocatePc (Fin.natAdd 5) none pc) b p body unary binary scratch := by
  simp [ProgramLinking.embedCfg, bodyFrame, cfg, extend_counter_stacks]

theorem counter_terminal_eq (output : List Bool) :
    terminal CounterPrograms.lengthProgram output =
      (⟨none, CounterPrograms.counterRegs false false false,
        CounterPrograms.lengthStacks [] output []⟩ : Cfg 3 3 14) := by
  simp [terminal ]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [CounterPrograms.lengthStacks]

theorem initialize_initial (input : List Bool) :
    initial initializeProgram input = cfg (some 0) false false input [] [] [] := by
  simp [initial, cfg]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [storage]

theorem header_trace (n : ℕ) (body : List Bool) :
    Trace initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) := by
  have h := ProgramLinking.relocate_trace ParserProgram.natProgram initializeProgram
    Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5) emptyFrame
    (Fin.castSucc_injective 2) (Fin.castAdd_injective 2 2)
    (ProgramLinking.linkInto_leftCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ)
    (ParserProgram.nat_trace n body [] false false)
  simpa [embed_parser, ProgramLinking.relocatePc, initialize_initial] using h

theorem initializeBound_eq (n : ℕ) : initializeBound n = 8 * n ^ 2 + 14 * n + 7 := by
  unfold initializeBound
  ring

/-- Actual raw-input initialization. The formula body is preserved on stack 0,
the binary count is on stack 2, and both work stacks are empty. -/
theorem initialize_raw (n : ℕ) (body : List Bool) :
    ∃ binary : List Bool, CounterPrograms.value binary = n ∧ binary.length ≤ n ∧
      RunsIn initializeProgram (initializeBound n)
        (initial initializeProgram (Encoding.encodeNat n ++ body))
        (cfg none false false body [] binary []) := by
  obtain ⟨binary, hv, hlen, hc⟩ :=
    CounterPrograms.length_correct_from false true (List.replicate n true)
  simp only [List.length_replicate] at hv hlen hc
  have hrel := ProgramLinking.relocate_runsIn CounterPrograms.lengthProgram initializeProgram
    id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
    Function.injective_id (Fin.succ_injective 3)
    (ProgramLinking.linkInto_rightCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ) hc
  have hcounter : RunsIn initializeProgram (n * (8 * n + 10) + 3)
      (cfg (some 5) false true body (List.replicate n true) [] [])
      (cfg none false false body [] binary []) := by
    simpa [CounterPrograms.lengthCfg, counter_terminal_eq, embed_counter,
      ProgramLinking.relocatePc] using hrel
  have hheader : RunsIn initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) :=
    ⟨_, le_rfl, header_trace n body⟩
  exact ⟨binary, hv, hlen, hheader.trans hcounter⟩

end SubexponentialSAT.FrontendProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryCompareProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Minimal actual binary comparison, extracted from SubexpGuardProgram.
Only the concrete Boolean borrow operation and fixed comparison machine are retained.
The source map and hashes are recorded in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace Compare

/-- The final borrow is the strict comparison, even for unequal word lengths. -/
theorem carry_iff (xs ys : List Bool) (c : Bool) :
    carry c xs ys = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys + bitVal c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [carry, bitVal]
    | cons b ys ih =>
      rw [carry, ih]
      cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [carry, ih]
      cases a <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
    | cons b ys =>
      rw [carry, ih]
      cases a <;> cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat] <;> omega

private theorem update_left (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 0 zs = operandStacks zs ys := by
  funext i
  fin_cases i <;> simp [operandStacks]

private theorem update_right (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 1 zs = operandStacks xs zs := by
  funext i
  fin_cases i <;> simp [operandStacks]

theorem roundRegs_borrow (regs : Fin 8 → Bool) (a b : Option Bool) :
    roundRegs regs a b 0 = borrowBit (a.getD false) (b.getD false) (regs 0) := by
  simp only [roundRegs, Function.update_self]
  cases ha : a.getD false <;> cases hb : b.getD false <;> cases hc : regs 0 <;>
    simp [borrowBit]

private theorem round_nil_cons (regs : Fin 8 → Bool) (b : Bool) (ys : List Bool) :
    Trace program 10 (cfg (some 1) regs [] (b :: ys))
      (cfg (some 1) (roundRegs regs none (some b)) [] ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_nil (regs : Fin 8 → Bool) (a : Bool) (xs : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) [])
      (cfg (some 1) (roundRegs regs (some a) none) xs []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_cons (regs : Fin 8 → Bool) (a b : Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) (b :: ys))
      (cfg (some 1) (roundRegs regs (some a) (some b)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

/-- A concrete nonterminal round, including its branch instruction. -/
theorem round_trace (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hne : xs ≠ [] ∨ ys ≠ []) :
    Trace program 10 (cfg (some 1) regs xs ys)
      (cfg (some 1) (roundRegs regs xs.head? ys.head?) xs.tail ys.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at hne
    | cons b ys => exact round_nil_cons regs b ys
  | cons a xs =>
    cases ys with
    | nil => exact round_cons_nil regs a xs
    | cons b ys => exact round_cons_cons regs a b xs ys

theorem exit_trace (regs : Fin 8 → Bool) :
    Trace program 5 (cfg (some 1) regs [] []) (cfg none (exitRegs regs) [] []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, exitRegs, readRegs, update_left, update_right,
    Function.update_apply]

/-- Exact instruction count for the data-dependent loop. -/
theorem loop_trace (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 5)
        (cfg (some 1) regs xs ys) (cfg none rf [] []) ∧
      rf 0 = carry (regs 0) xs ys := by
  induction xs generalizing ys regs with
  | nil =>
    induction ys generalizing regs with
    | nil =>
      exact ⟨exitRegs regs, by simpa using exit_trace regs, by simp [carry]⟩
    | cons b ys ih =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs none (some b))
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs [] (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
  | cons a xs ih =>
    cases ys with
    | nil =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) none) []
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) [] (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
    | cons b ys =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) (some b)) ys
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb

/-- Complete comparator contract. Leading zero bits and unequal widths are allowed. -/
theorem run (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 6)
        (cfg (some program.entry) regs xs ys) (cfg none rf [] []) ∧
      (rf 0 = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rf, hr, hb⟩ := loop_trace (Function.update regs 0 false) xs ys
  refine ⟨rf, ?_, ?_⟩
  · have he : Trace program 1 (cfg (some program.entry) regs xs ys)
        (cfg (some 1) (Function.update regs 0 false) xs ys) := by
      exact .cons (by rfl) (.refl _)
    convert he.trans hr using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · rw [hb]
    simpa only [Function.update_self, bitVal_false, Nat.add_zero] using carry_iff xs ys false

end Compare

open StructuredProgram

private theorem extend_restrict {α β γ : Type} (f : α → β) (hf : Function.Injective f)
    (g : β → γ) : Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    exact hf.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hb

private theorem embed_restrict {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    StructuredCalls.embedState register stack a (restrictState register stack a) = a := by
  unfold StructuredCalls.embedState restrictState
  change State.mk (Function.extend register (a.regs ∘ register) a.regs)
    (Function.extend stack (a.stacks ∘ stack) a.stacks) = a
  rw [extend_restrict register hr, extend_restrict stack hs]

private theorem pair_eta (f : Fin 2 → List Bool) : Compare.operandStacks (f 0) (f 1) = f := by
  first | done | (funext i; fin_cases i <;> rfl)

/-- A measured comparison call on fixed injective ports, with every other
caller register and stack preserved. -/
theorem compare_call {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    ∃ b : State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram Compare.program register stack))
        (10 * max (a.stacks (stack 0)).length (a.stacks (stack 1)).length + 6) a b ∧
      (b.regs (register 0) = true ↔
        BinaryArithmetic.toNat (a.stacks (stack 0)) <
          BinaryArithmetic.toNat (a.stacks (stack 1))) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ j, b.stacks (stack j) = []) := by
  obtain ⟨rf, hrun, hcmp⟩ := Compare.run (fun i => a.regs (register i))
    (a.stacks (stack 0)) (a.stacks (stack 1))
  have hstack := pair_eta (fun i => a.stacks (stack i))
  have hempty : Compare.operandStacks [] [] = (fun _ : Fin 2 => []) := by
    simpa using pair_eta (fun _ : Fin 2 => [])
  simp only [Compare.cfg, hstack, hempty] at hrun
  let localOut : State 8 2 := ⟨rf, fun _ => []⟩
  let b := StructuredCalls.embedState register stack a localOut
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.eval_call_lifted Compare.program register stack a hr hs
      (a := restrictState register stack a) (b := localOut) hrun
    rw [embed_restrict register stack hr hs a] at h
    exact h
  · simpa only [b, StructuredCalls.embedState_register register stack a localOut hr,
      localOut] using hcmp
  · exact fun i hi => StructuredCalls.embedState_register_frame register stack a localOut i hi
  · exact fun i hi => StructuredCalls.embedState_stack_frame register stack a localOut i hi
  · exact fun j => StructuredCalls.embedState_stack register stack a localOut hs j


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSunflowerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs used by sunflower candidate checking

Runtime clause counts and widths remain encoded stack data. The first
primitive counts framed records; it is an actual finite instruction table,
with a trace theorem, rather than a semantic list-length instruction.
-/
namespace SubexponentialSAT.SubexpSunflowerProgram

open BitProgram

namespace CountRecords

theorem start (value present : Bool) (input output : List Bool) :
    Trace program 2 (cfg (some 0) value present input output)
      (cfg (some 2) false present input (false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem trace (records : List (List Bool)) (suffix output : List Bool)
    (value present : Bool) :
    Trace program (steps records)
      (cfg (some program.entry) value present (Encoding.encodeList id records ++ suffix) output)
      (cfg none false false suffix (Encoding.encodeNat records.length ++ output)) := by
  have h := (start value present (Encoding.encodeList id records ++ suffix) output).trans
    (loop_trace records suffix (false :: output) false present)
  simpa [steps, Encoding.encodeNat, Nat.add_comm, List.append_assoc] using h

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BitProgram StructuredCalls BinaryArithmetic

namespace Tuple

theorem copy_eval (src dst : Fin 9) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ 8) (htd : (8 : Fin 9) ≠ dst)
    (htmp : d.stacks 8 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  have ht := StackRoutines.copyProgram_trace src dst 8 (0 : Fin 13) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StackRoutines.copyProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem clear_eval (port : Fin 9) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have ht := StackRoutines.clearProgram_trace port (0 : Fin 13) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StackRoutines.clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem workReg_injective : Function.Injective workReg := Fin.castAdd_injective 8 5

theorem pairPort_injective (left right : Fin 9) (h : left ≠ right) :
    Function.Injective (pairPort left right) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pairPort]

theorem compare_eval (left right : Fin 9) (h : left ≠ right) (d : Data) :
    ∃ e : Data,
      Eval (compare left right)
        (10 * max (d.stacks left).length (d.stacks right).length + 6) d e ∧
      e.regs 0 = decide (toNat (d.stacks left) < toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) ∧
      (∀ i : Fin 9, i ≠ left → i ≠ right → e.stacks i = d.stacks i) ∧
      e.stacks left = [] ∧ e.stacks right = [] := by
  obtain ⟨e, he, ha, hr, hs, hz⟩ := BinaryCompareProgram.compare_call workReg
    (pairPort left right) workReg_injective (pairPort_injective left right h) d
  refine ⟨e, he, ?_, ?_, ?_, hz 0, hz 1⟩
  · apply Bool.eq_iff_iff.mpr
    simpa [workReg, pairPort] using ha
  · intro i hi
    apply hr
    rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    change j.val = i.val at hjv
    have := j.isLt
    omega
  · intro i hl hr'
    apply hs
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [pairPort] at hj <;> subst i <;> contradiction

end Tuple

namespace Count

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Tuple
  (Data copied copy copy_eval cleared clear clear_eval)

theorem countReg_injective : Function.Injective countReg := Fin.castAdd_injective 2 11
theorem countStack_injective : Function.Injective countStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [countStack]

theorem count_eval (records : List (List Bool)) (d : Data)
    (hinput : d.stacks 5 = Encoding.encodeList id records) (houtput : d.stacks 7 = []) :
    Eval (.call countProgram) (SubexpSunflowerProgram.CountRecords.steps records)
      d (counted records d) := by
  let b : State 2 2 := ⟨ParserProgram.pair false false,
    ParserProgram.pair [] (Encoding.encodeNat records.length)⟩
  have hstart : (projectState countReg countStack d).withPC
      (some SubexpSunflowerProgram.CountRecords.program.entry) =
      SubexpSunflowerProgram.CountRecords.cfg
        (some SubexpSunflowerProgram.CountRecords.program.entry) (d.regs 0) (d.regs 1)
        (Encoding.encodeList id records) [] := by
    simp only [projectState, StructuredProgram.State.withPC,
      SubexpSunflowerProgram.CountRecords.cfg, Cfg.mk.injEq, true_and]
    constructor <;> funext i <;> fin_cases i <;>
      simp [countReg, countStack, ParserProgram.pair, hinput, houtput]
  have ht : Trace SubexpSunflowerProgram.CountRecords.program
      (SubexpSunflowerProgram.CountRecords.steps records)
      ((projectState countReg countStack d).withPC
        (some SubexpSunflowerProgram.CountRecords.program.entry)) (b.withPC none) := by
    rw [hstart]
    simpa [b, SubexpSunflowerProgram.CountRecords.cfg, StructuredProgram.State.withPC] using
      SubexpSunflowerProgram.CountRecords.trace records [] [] (d.regs 0) (d.regs 1)
  have hb : embedState countReg countStack d b = counted records d := by
    apply embedState_eq_of_ports _ _ _ _ _ countReg_injective countStack_injective
    · intro i; fin_cases i <;> simp [counted, countReg, readRegs, b]
    · intro i hi
      have hi0 : i ≠ 0 := by intro h; apply hi; exact ⟨0, h.symm⟩
      have hi1 : i ≠ 1 := by intro h; apply hi; exact ⟨1, h.symm⟩
      simp [counted, readRegs, hi0, hi1]
    · intro i; fin_cases i <;> simp [counted, countStack, b]
    · intro i hi
      have hi5 : i ≠ 5 := by intro h; apply hi; exact ⟨0, h.symm⟩
      have hi7 : i ≠ 7 := by intro h; apply hi; exact ⟨1, h.symm⟩
      simp [counted, hi5, hi7]
  simpa only [hb, countProgram] using eval_call_from_state
    SubexpSunflowerProgram.CountRecords.program countReg countStack d
    countReg_injective countStack_injective ht

theorem reset_eval (d : Data) : Eval reset 3 d (resetState d) :=
  .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

theorem binaryReg_injective : Function.Injective binaryReg := Fin.castAdd_injective 3 10
theorem binaryStack_injective : Function.Injective binaryStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [binaryStack]

/-- Convert an input-sized unary record count to binary. The cost comes from
the actual header parser and dynamic binary length counter. -/
theorem toBinary_eval (n : ℕ) (d : Data) (h7 : d.stacks 7 = Encoding.encodeNat n)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ FrontendProgram.initializeBound n + 3, ∃ bits : List Bool, ∃ e : Data,
      Eval toBinary t d e ∧ toNat bits = n ∧ bits.length ≤ n ∧
      e.stacks = Function.update (Function.update d.stacks 7 []) 6 bits ∧
      (∀ i : Fin 13, 3 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨bits, hvalue, hlength, t, ht, htrace⟩ := FrontendProgram.initialize_raw n []
  let a := resetState d
  let b : State 3 4 := StructuredProgram.State.ofCfg
    (FrontendProgram.cfg none false false [] [] bits [])
  have hstart : (projectState binaryReg binaryStack a).withPC
      (some FrontendProgram.initializeProgram.entry) =
      initial FrontendProgram.initializeProgram (Encoding.encodeNat n ++ []) := by
    rw [FrontendProgram.initialize_initial]
    simp only [projectState, StructuredProgram.State.withPC, FrontendProgram.cfg,
      Cfg.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · funext i
      fin_cases i <;> simp [a, resetState, binaryReg, CounterPrograms.counterRegs]
    · funext i
      fin_cases i <;> simp [a, resetState, binaryStack, FrontendProgram.storage,
        h7, h5, h6, h8]
  have hl : Trace FrontendProgram.initializeProgram t
      ((projectState binaryReg binaryStack a).withPC
        (some FrontendProgram.initializeProgram.entry)) (b.withPC none) := by
    rw [hstart]
    exact htrace
  have he := eval_call_from_state FrontendProgram.initializeProgram binaryReg binaryStack a
    binaryReg_injective binaryStack_injective hl
  let e := embedState binaryReg binaryStack a b
  have hs (i : Fin 4) : e.stacks (binaryStack i) = b.stacks i :=
    embedState_stack _ _ _ _ binaryStack_injective i
  refine ⟨3 + t, by omega, bits, e, Eval.seq (reset_eval d) he, ?_, hlength, ?_, ?_⟩
  · simpa only [CounterPrograms.value_eq_toNat] using hvalue
  · funext i
    fin_cases i
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg, h5] using hs 1
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg] using hs 2
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg] using hs 0
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg, h8] using hs 3
  · intro i hi
    have hfr : e.regs i = a.regs i := by
      apply embedState_register_frame
      rintro ⟨j, hj⟩
      have hjv := congrArg Fin.val hj
      change j.val = i.val at hjv
      have := j.isLt
      omega
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hi2 : i ≠ 2 := by intro h; subst i; simp at hi
    simpa [a, resetState, hi0, hi1, hi2] using hfr

theorem less_eval (left right : Fin 9) (d : Data)
    (hl : left ≠ 5 ∧ left ≠ 7 ∧ left ≠ 8)
    (hr : right ≠ 5 ∧ right ≠ 7 ∧ right ≠ 8)
    (h5 : d.stacks 5 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 20 * ((d.stacks left).length + (d.stacks right).length + 1), ∃ e : Data,
      Eval (less left right) n d e ∧ e.stacks = d.stacks ∧
      e.regs 0 = decide (toNat (d.stacks left) < toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := copied left 5 d
  let b := copied right 7 a
  have ha8 : a.stacks 8 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h8
  have har : a.stacks right = d.stacks right := by simp [a, copied, StackRoutines.copyStacks, hr.1]
  have hb5 : b.stacks 5 = d.stacks left := by simp [b, a, copied, StackRoutines.copyStacks, h5]
  have hb7 : b.stacks 7 = d.stacks right := by
    simp [b, a, copied, StackRoutines.copyStacks, hr.1, h7]
  obtain ⟨e, he, hresult, hregs, hstacks, he5, he7⟩ :=
    Tuple.compare_eval 5 7 (by decide) b
  refine ⟨(7 * (d.stacks left).length + 5) + ((7 * (a.stacks right).length + 5) +
    (10 * max (b.stacks 5).length (b.stacks 7).length + 6)), ?_, e, ?_, ?_, ?_, ?_⟩
  · rw [har, hb5, hb7]
    have hmax := max_le
      (Nat.le_add_right (d.stacks left).length (d.stacks right).length)
      (Nat.le_add_left (d.stacks right).length (d.stacks left).length)
    omega
  · exact Eval.seq (copy_eval left 5 d hl.1 hl.2.2 (by decide) h8)
      (Eval.seq (copy_eval right 7 a hr.2.1 hr.2.2 (by decide) ha8) he)
  · funext i
    by_cases hi5 : i = 5
    · subst i; exact he5.trans h5.symm
    by_cases hi7 : i = 7
    · subst i; exact he7.trans h7.symm
    simpa [b, a, copied, StackRoutines.copyStacks, hi5, hi7] using hstacks i hi5 hi7
  · simpa [hb5, hb7] using hresult
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    simpa [b, a, copied, readRegs, hi0, hi1] using hregs i hi

/-- Numeric equality tolerates leading zero padding in the supplied bound.
Both comparisons consume only real copies of the preserved operands. -/
theorem numericEq_eval (expected : Fin 2) (d : Data)
    (h5 : d.stacks 5 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 50 * ((d.stacks 6).length + (d.stacks (expectedPort expected)).length + 1),
      ∃ e : Data, Eval (numericEq expected) n d e ∧ e.stacks = d.stacks ∧
        e.regs 4 = decide (toNat (d.stacks 6) = toNat (d.stacks (expectedPort expected))) ∧
        (∀ i : Fin 13, 8 ≤ i.val → i ≠ 12 → e.regs i = d.regs i) := by
  have hp : expectedPort expected ≠ 5 ∧ expectedPort expected ≠ 7 ∧ expectedPort expected ≠ 8 := by
    fin_cases expected <;> decide
  obtain ⟨n, hn, a, ha, hast, ha0, hareg⟩ := less_eval 6 (expectedPort expected) d
    (by decide) hp h5 h7 h8
  let b := (StructuredProgram.Atom.copy (r := 13) (s := 9) 12 0).eval a
  have hbst : b.stacks = d.stacks := hast
  have hb12 : b.regs 12 = decide (toNat (d.stacks 6) < toNat (d.stacks (expectedPort expected))) := by
    simpa [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using ha0
  obtain ⟨m, hm, c, hc, hcst, hc0, hcreg⟩ := less_eval (expectedPort expected) 6 b hp
    (by decide) (by simpa only [hbst] using h5)
    (by simpa only [hbst] using h7) (by simpa only [hbst] using h8)
  let e := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 4 4).eval
    ((StructuredProgram.Atom.bor (r := 13) (s := 9) 4 12 0).eval c)
  have hc12 : c.regs 12 = decide (toNat (d.stacks 6) < toNat (d.stacks (expectedPort expected))) :=
    (hcreg 12 (by decide)).trans hb12
  have hbool (a b : ℕ) : (!(decide (a < b) || decide (b < a))) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp
    omega
  refine ⟨n + (1 + (m + (1 + 1))), ?_, e, ?_, hcst.trans hbst, ?_, ?_⟩
  · rw [hbst] at hm
    omega
  · exact Eval.seq ha (Eval.seq (.base (.atom _ _))
      (Eval.seq hc (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))))
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      hc12, hc0, hbst, hbool]
  · intro i hi hne
    have hi4 : i ≠ 4 := by
      intro h
      subst i
      change 8 ≤ 4 at hi
      omega
    have hci := hcreg i hi
    have hai := hareg i hi
    simpa [e, b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      hi4, hne, hai] using hci

/-- Count the actual records, convert the count, compare it with a supplied
binary word, and clear every temporary. Only the scanned input is consumed. -/
theorem countTest_eval (expected : Fin 2) (records : List (List Bool)) (d : Data)
    (hin : d.stacks 5 = Encoding.encodeList id records)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 200 * ((Encoding.encodeList id records).length +
      (d.stacks (expectedPort expected)).length + 1) ^ 2, ∃ e : Data,
      Eval (countTest expected) n d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
      e.regs 4 = decide (records.length = toNat (d.stacks (expectedPort expected))) ∧
      (∀ i : Fin 13, 8 ≤ i.val → i ≠ 12 → e.regs i = d.regs i) := by
  let a := counted records d
  have ha7 : a.stacks 7 = Encoding.encodeNat records.length := by simp [a, counted]
  have ha5 : a.stacks 5 = [] := by simp [a, counted]
  have ha6 : a.stacks 6 = [] := by simpa [a, counted] using h6
  have ha8 : a.stacks 8 = [] := by simpa [a, counted] using h8
  obtain ⟨n, hn, bits, b, hb, hvalue, hlength, hbst, hbreg⟩ :=
    toBinary_eval records.length a ha7 ha5 ha6 ha8
  have hb5 : b.stacks 5 = [] := by simp [hbst, a, counted]
  have hb6 : b.stacks 6 = bits := by simp [hbst]
  have hb7 : b.stacks 7 = [] := by simp [hbst]
  have hb8 : b.stacks 8 = [] := by simpa [hbst, a, counted] using h8
  have hbexpected : b.stacks (expectedPort expected) = d.stacks (expectedPort expected) := by
    fin_cases expected <;> simp [expectedPort, hbst, a, counted]
  obtain ⟨m, hm, c, hc, hcst, hc4, hcreg⟩ := numericEq_eval expected b hb5 hb7 hb8
  let e := cleared 6 c
  have hm' : m ≤ 50 * (bits.length + (d.stacks (expectedPort expected)).length + 1) := by
    simpa [hb6, hbexpected] using hm
  have hc6 : c.stacks 6 = bits := by simpa [hcst] using hb6
  refine ⟨SubexpSunflowerProgram.CountRecords.steps records +
    (n + (m + (2 * (c.stacks 6).length + 3))), ?_, e,
    Eval.seq (count_eval records d hin h7) (Eval.seq hb (Eval.seq hc (clear_eval 6 c))),
    ?_, ?_, ?_⟩
  · rw [hc6]
    have hcount := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hrecords := Encoding.length_encodeList_lower id records
    have hrecords' : records.length ≤ (Encoding.encodeList id records).length := by omega
    have hquad := Nat.mul_le_mul hrecords' hrecords'
    have hbits : bits.length ≤ (Encoding.encodeList id records).length :=
      hlength.trans hrecords'
    have hsum : bits.length + (d.stacks (expectedPort expected)).length + 1 ≤
        (Encoding.encodeList id records).length +
          (d.stacks (expectedPort expected)).length + 1 := by omega
    have hsumquad := Nat.mul_le_mul hsum hsum
    rw [FrontendProgram.initializeBound_eq] at hn
    let H := (Encoding.encodeList id records).length +
      (d.stacks (expectedPort expected)).length + 1
    have hH : 1 ≤ H := by dsimp [H]; omega
    have hEH : (Encoding.encodeList id records).length ≤ H := by dsimp [H]; omega
    have hRH : records.length ≤ H := hrecords'.trans hEH
    have hBH : bits.length ≤ H := hbits.trans hEH
    have hsq : H ≤ H ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ hH
    have hRsq : records.length ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hRH 2
    have hcount' : SubexpSunflowerProgram.CountRecords.steps records ≤ 7 * H ^ 2 := by
      have h7 := Nat.mul_le_mul_left 7 hsq
      omega
    have hn' : n ≤ 32 * H ^ 2 := by
      have h8 := Nat.mul_le_mul_left 8 hRsq
      have h14 := Nat.mul_le_mul_left 14 (hRH.trans hsq)
      have h10 : 10 ≤ 10 * H ^ 2 := by omega
      omega
    have hm'' : m ≤ 50 * H ^ 2 := by
      have hmH : m ≤ 50 * H := hm'.trans (Nat.mul_le_mul_left 50 (by
        dsimp [H]
        exact hsum))
      exact hmH.trans (Nat.mul_le_mul_left 50 hsq)
    have hclear : 2 * bits.length + 3 ≤ 5 * H ^ 2 := by
      have h5 := Nat.mul_le_mul_left 5 hsq
      omega
    change SubexpSunflowerProgram.CountRecords.steps records +
        (n + (m + (2 * bits.length + 3))) ≤ 200 * H ^ 2
    omega
  · funext i
    fin_cases i <;> simp [e, cleared, StackRoutines.clearStacks, hcst, hbst, a, counted, h6, h7]
  · simpa [e, cleared, readRegs, hb6, hbexpected, hvalue] using hc4
  · intro i hi hne
    have hi3 : 3 ≤ i.val := by omega
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hh := (hcreg i hi hne).trans (hbreg i hi3)
    simpa [e, cleared, readRegs, a, counted, hi0, hi1] using hh

end Count

namespace FrameWriter

theorem escapeBits_append (a b : List Bool) :
    escapeBits (a ++ b) = escapeBits a ++ escapeBits b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [escapeBits, ih]

theorem frame_eq_escape (bits : List Bool) :
    Encoding.frame bits = escapeBits bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      rw [Encoding.frame_cons, escapeBits, ih]
      simp only [List.cons_append]

theorem literalService_encode_cycle (b v p op : Bool) (code depth operands scratch : List Bool) :
    Trace literalService 5
      (cfg4 (some 9) v p op code depth operands (b :: scratch))
      (cfg4 (some 9) true true op code depth (true :: b :: operands) scratch) := by
  refine .cons (b := cfg4 (some 10) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4, readRegs]
  refine .cons (b := cfg4 (some 11) b true op code depth operands scratch) ?_ ?_
  · simp [step, execInstr, cfg4]
  refine .cons (b := cfg4 (some 12) b true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4]
  refine .cons (b := cfg4 (some 13) true true op code depth (b :: operands) scratch) ?_ ?_
  · simp [step, execInstr, cfg4]
  refine .cons ?_ (.refl _)
  simp [step, execInstr, cfg4]

theorem literalService_encode_loop (scratch code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * scratch.length + 2)
      (cfg4 (some 9) v p op code depth operands scratch)
      (cfg4 (some 14) false false op code depth (escapeBits scratch.reverse ++ operands) []) := by
  induction scratch generalizing operands v p with
  | nil =>
      refine .cons (b := cfg4 (some 10) false false op code depth operands []) ?_ ?_
      · simp [step, execInstr, cfg4, readRegs]
      · refine .cons ?_ (.refl _)
        simp [step, execInstr, cfg4, escapeBits]
  | cons b bs ih =>
      have h := (literalService_encode_cycle b v p op code depth operands bs).trans
        (ih (true :: b :: operands) true true)
      have hn : 5 + (5 * bs.length + 2) = 5 * (b :: bs).length + 2 := by
        simp only [List.length_cons]
        omega
      simpa only [hn, List.reverse_cons, escapeBits_append, escapeBits,
        List.append_assoc, List.cons_append, List.nil_append] using h

theorem literalService_encode_trace (bits code depth operands : List Bool) (v p op : Bool) :
    Trace literalService (5 * bits.length + 7)
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
  have init : Trace literalService 2
      (cfg4 (some 7) v p op code depth operands bits.reverse)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse) := by
    refine .cons (b := cfg4 (some 8) false p op code depth operands bits.reverse) ?_ ?_
    · simp [step, execInstr, cfg4]
    · refine .cons ?_ (.refl _)
      simp [step, execInstr, cfg4]
  have loop := literalService_encode_loop bits.reverse code depth (false :: operands) false p op
  have finish : Trace literalService 3
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) [])
      (cfg4 none true false op code depth (true :: (Encoding.frame bits ++ operands)) []) := by
    refine .cons (b := cfg4 (some 15) true false op code depth (Encoding.frame bits ++ operands) []) ?_ ?_
    · simp [step, execInstr, cfg4]
    refine .cons (b := cfg4 (some 16) true false op code depth (true :: (Encoding.frame bits ++ operands)) []) ?_ ?_
    · simp [step, execInstr, cfg4]
    refine .cons ?_ (.refl _)
    simp [step, execInstr, cfg4]
  have loop' : Trace literalService (5 * bits.length + 2)
      (cfg4 (some 9) false p op code depth (false :: operands) bits.reverse)
      (cfg4 (some 14) false false op code depth (Encoding.frame bits ++ operands) []) := by
    simpa [List.length_reverse, List.reverse_reverse, frame_eq_escape,
      List.append_assoc] using loop
  have h := (init.trans loop').trans finish
  have hn : 2 + (5 * bits.length + 2) + 3 = 5 * bits.length + 7 := by omega
  simpa only [hn] using h


end FrameWriter

namespace Filter

theorem emitRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace emitRecordProgram (5 * bits.length + 7)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitRecordProgram.entry))
      ((filterState true false selected source work
        (true :: (Encoding.frame bits ++ output)) []).withPC none) := by
  simpa only [emitRecordProgram, step, filterState, StructuredProgram.State.withPC,
    FrameWriter.cfg4] using
    FrameWriter.literalService_encode_trace bits source work output v p selected

theorem discardRecord_trace (bits source work output : List Bool) (v p selected : Bool) :
    Trace discardRecordProgram (2 * bits.length + 3)
      ((filterState v p selected source work output bits.reverse).withPC
        (some discardRecordProgram.entry))
      ((filterState false false selected source work output []).withPC none) := by
  have h := StackRoutines.clearProgram_trace (r := 3) (s := 4) 3 0 1
    (FrameWriter.triple v p selected)
    (FrameWriter.quadruple source work output bits.reverse)
  have hh := StackRoutines.halt_after_trace (StackRoutines.clearProgram (3 : Fin 4)
    (0 : Fin 3) 1) h 2 rfl rfl
  simpa [discardRecordProgram, StackRoutines.clearProgram, StackRoutines.clearResult,
    StackRoutines.clearStacks, filterState, StructuredProgram.State.withPC,
    readRegs, Nat.add_assoc] using hh

theorem resetFilterFlags_eval (v p selected : Bool)
    (source work output payload : List Bool) :
    StructuredProgram.Eval resetFilterFlags 3
      (filterState v p selected source work output payload)
      (filterState false true false source work output payload) := by
  have h0 : StructuredProgram.Eval (.atom (.set 0 false)) 1
      (filterState v p selected source work output payload)
      (filterState false p selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 0 false)
        (filterState v p selected source work output payload)
  have h1 : StructuredProgram.Eval (.atom (.set 1 true)) 1
      (filterState false p selected source work output payload)
      (filterState false true selected source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 1 true)
        (filterState false p selected source work output payload)
  have h2 : StructuredProgram.Eval (.atom (.set 2 false)) 1
      (filterState false true selected source work output payload)
      (filterState false true false source work output payload) := by
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      filterState] using StructuredProgram.Eval.atom (.set 2 false)
        (filterState false true selected source work output payload)
  exact .seq h0 (.seq h1 h2)

/-- An actual measured branch: the kept record is encoded, and an omitted
record is consumed. Both paths leave the callback ready for the next record. -/
theorem emitIfSelected_eval (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    StructuredCalls.Eval emitIfSelected (emitIfSelectedSteps selected bits)
      (filterState v p selected source work output bits.reverse)
      (filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []) := by
  cases selected with
  | false =>
      have hc := StructuredCalls.Eval.call discardRecordProgram
        (discardRecord_trace bits source work output v p false)
      have hi := StructuredCalls.Eval.ite_false (yes := .call emitRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval false false false source work output []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs
  | true =>
      have hc := StructuredCalls.Eval.call emitRecordProgram
        (emitRecord_trace bits source work output v p true)
      have hi := StructuredCalls.Eval.ite_true (no := .call discardRecordProgram)
        (test := (2 : Fin 3)) (by rfl) hc
      have hs := hi.seq (StructuredCalls.Eval.base
        (resetFilterFlags_eval true false true source work
          (true :: (Encoding.frame bits ++ output)) []))
      simpa [emitIfSelected, emitIfSelectedSteps, Nat.add_assoc] using hs

theorem emitIfSelected_trace (selected : Bool)
    (bits source work output : List Bool) (v p : Bool) :
    Trace emitIfSelectedProgram (emitIfSelectedSteps selected bits + 1)
      ((filterState v p selected source work output bits.reverse).withPC
        (some emitIfSelectedProgram.entry))
      ((filterState false true false source work
        (if selected then true :: (Encoding.frame bits ++ output) else output) []).withPC none) :=
  StructuredCalls.compiled_halt_trace
    (emitIfSelected_eval selected bits source work output v p) 3 2

theorem emitIfSelected_steps_le (selected : Bool) (bits : List Bool) :
    emitIfSelectedSteps selected bits + 1 ≤ 5 * bits.length + 12 := by
  unfold emitIfSelectedSteps
  split <;> omega

theorem filterVisits_result {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    {records : List (List Bool)} {before after : StructuredProgram.State r s}
    (h : RecordPrograms.Visits (fun _ => false) (FilterEffect output keep)
      records before after)
    (acc : List (List Bool)) (hacc : before.stacks output = Encoding.encodeList id acc) :
    after.stacks output = Encoding.encodeList id ((records.filter keep).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
      cases hkeep : keep bits with
      | false =>
          have hm : middle.stacks output = Encoding.encodeList id acc := by
            simpa [hkeep, hacc] using he.output_eq
          simpa [List.filter_cons, hkeep] using ih acc hm
      | true =>
          have hm : middle.stacks output = Encoding.encodeList id (bits :: acc) := by
            simpa [hkeep, hacc, Encoding.encodeList] using he.output_eq
          simpa [List.filter_cons, hkeep, List.reverse_cons, List.append_assoc] using
            ih (bits :: acc) hm


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Guard

theorem widthStack_injective : Function.Injective widthStack := by decide

theorem subsetReg_injective : Function.Injective subsetReg := Fin.castAdd_injective 12 1

theorem subsetStack_injective : Function.Injective subsetStack := Fin.castAdd_injective 10 1

theorem copyClause_eval (d : Data) (h0 : d.stacks 0 = []) (h5 : d.stacks 5 = []) :
    Eval copyClause (7 * (d.stacks 9).length + 5) d (copied d) := by
  have h := ListRegisterProgram.copy_run (r := 13) (s := 11) 9 5 0 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h0
  apply Eval.call
  simpa [copied, StackRoutines.copyStacks, h5] using h

theorem width_eval (C : Clause) (d : Data)
    (h5 : d.stacks 5 = Encoding.encodeList id C)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h3 : d.stacks 3 = []) :
    ∃ t ≤ 200 * ((Encoding.encodeList id C).length + (d.stacks 10).length + 1) ^ 2 + 1,
      ∃ e : Data, Eval width t d e ∧
        e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (C.length = BinaryArithmetic.toNat (d.stacks 10)) := by
  let a := projectState id widthStack d
  obtain ⟨t, ht, b, hb, hbs, hbr, _⟩ :=
    SparsePriorityPrimitives.Count.countTest_eval 0 C a h5 h6 h7 h3
  let e := embedState id widthStack d b
  have he := eval_liftCommand_from_state (SparsePriorityPrimitives.Count.countTest 0) 5 5
    id widthStack d Function.injective_id widthStack_injective hb
  refine ⟨t + 1, by simpa [a, projectState, SparsePriorityPrimitives.Count.expectedPort,
    widthStack] using Nat.add_le_add_right ht 1, e, he, ?_, ?_⟩
  · funext i
    by_cases hi : ∃ j, widthStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [embedState_stack _ _ _ _ widthStack_injective j, hbs]
      fin_cases j <;> simp [a, projectState, widthStack]
    · rw [embedState_stack_frame _ _ _ _ _ hi]
      have hi5 : i ≠ 5 := fun h => hi ⟨5, h.symm⟩
      simp [hi5]
  · exact (embedState_register id widthStack d b Function.injective_id 4).trans hbr

theorem subset_eval (H C : Clause) (d : Data)
    (hH : d.stacks 8 = Encoding.encodeList id H)
    (hC : d.stacks 9 = Encoding.encodeList id C)
    (hwork : ∀ i : Fin 8, d.stacks (Fin.castAdd 3 i) = []) :
    ∃ t ≤ ExecClauseRelationsProgram.compareBound H C + 1,
      ∃ e : Data, Eval subset t d e ∧ e.stacks = d.stacks ∧
        e.regs 9 = ExecCNF.subset H C ∧ e.regs 12 = d.regs 12 := by
  let a := projectState subsetReg subsetStack d
  have ha : ExecClauseRelationsProgram.clean a := hwork
  obtain ⟨t, ht, b, hb, hclean, hresult, hframe, _, _⟩ :=
    ExecClauseRelationsProgram.compare_eval H C 0 1 a hH hC ha
  let e := embedState subsetReg subsetStack d b
  have he := eval_liftCommand_from_state (ExecClauseRelationsProgram.compare 0 1) 8 9
    subsetReg subsetStack d subsetReg_injective subsetStack_injective hb
  refine ⟨t + 1, Nat.add_le_add_right ht 1, e, he, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : ∃ j, subsetStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [embedState_stack _ _ _ _ subsetStack_injective j]
      fin_cases j
      · exact (hclean 0).trans (hwork 0).symm
      · exact (hclean 1).trans (hwork 1).symm
      · exact (hclean 2).trans (hwork 2).symm
      · exact (hclean 3).trans (hwork 3).symm
      · exact (hclean 4).trans (hwork 4).symm
      · exact (hclean 5).trans (hwork 5).symm
      · exact (hclean 6).trans (hwork 6).symm
      · exact (hclean 7).trans (hwork 7).symm
      · exact hframe 0
      · exact hframe 1
    · exact embedState_stack_frame _ _ _ _ _ hi
  · exact (embedState_register subsetReg subsetStack d b subsetReg_injective 9).trans hresult
  · exact embedState_register_frame _ _ _ _ _ (by decide)

theorem command_eval (H C : Clause) (d : Data)
    (hH : d.stacks 8 = Encoding.encodeList id H)
    (hC : d.stacks 9 = Encoding.encodeList id C)
    (hwork : ∀ i : Fin 8, d.stacks (Fin.castAdd 3 i) = []) :
    ∃ t ≤ 400 * ((Encoding.encodeList id H).length + (Encoding.encodeList id C).length +
        (d.stacks 10).length + 1) ^ 2,
      ∃ e : Data, Eval command t d e ∧ e.stacks = d.stacks ∧
        e.regs 12 = (decide (C.length = BinaryArithmetic.toNat (d.stacks 10)) &&
          ExecCNF.subset H C) := by
  let a := copied d
  have ha5 : a.stacks 5 = Encoding.encodeList id C := by simp [a, copied, hC]
  have haw (i : Fin 8) (hi : i.val ≠ 5) : a.stacks (Fin.castAdd 3 i) = [] := by
    have hi' : Fin.castAdd 3 i ≠ (5 : Fin 11) := fun h => hi (congrArg Fin.val h)
    simpa [a, copied, hi'] using hwork i
  obtain ⟨t, ht, b, hb, hbs, hb4⟩ := width_eval C a ha5
    (haw 6 (by decide)) (haw 7 (by decide)) (haw 3 (by decide))
  have hbstate : b.stacks = d.stacks := by
    rw [hbs]
    funext i
    by_cases hi : i = 5
    · subst i; simpa using (hwork 5).symm
    · simp [a, copied, hi]
  let c := (StructuredProgram.Atom.copy (r := 13) (s := 11) 12 4).eval b
  have hcs : c.stacks = d.stacks := hbstate
  have hc12 : c.regs 12 = decide (C.length = BinaryArithmetic.toNat (d.stacks 10)) := by
    simpa [c, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, a, copied] using hb4
  obtain ⟨u, hu, z, hz, hzs, hz9, hz12⟩ := subset_eval H C c
    (by simpa only [hcs] using hH) (by simpa only [hcs] using hC)
    (by simpa only [hcs] using hwork)
  let e := (StructuredProgram.Atom.band (r := 13) (s := 11) 12 12 9).eval z
  refine ⟨(7 * (d.stacks 9).length + 5) + (t + (1 + (u + 1))), ?_, e,
    (copyClause_eval d (hwork 0) (hwork 5)).seq
      (hb.seq ((Eval.base (.atom _ _)).seq (hz.seq (Eval.base (.atom _ _))))),
    hzs.trans hcs, ?_⟩
  · rw [hC]
    have ha10 : a.stacks 10 = d.stacks 10 := by simp [a, copied]
    rw [ha10] at ht
    unfold ExecClauseRelationsProgram.compareBound at hu
    let L := (Encoding.encodeList id H).length + (Encoding.encodeList id C).length +
      (d.stacks 10).length + 1
    have hwidth : (Encoding.encodeList id C).length + (d.stacks 10).length + 1 ≤ L := by omega
    have hcore : (Encoding.encodeList id H).length + 1 ≤ L := by omega
    have hclause : (Encoding.encodeList id C).length + 1 ≤ L := by omega
    have hsq := Nat.pow_le_pow_left hwidth 2
    have hprod := Nat.mul_le_mul hcore hclause
    have hL : 1 ≤ L := by omega
    have hLSq : L ≤ L ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right L hL
    have ht' : t ≤ 200 * L ^ 2 + 1 :=
      ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 200 hsq) 1)
    have hu' : u ≤ 80 * L ^ 2 + 1 := by
      apply hu.trans
      simpa only [Nat.mul_assoc, pow_two] using
        Nat.add_le_add_right (Nat.mul_le_mul_left 80 hprod) 1
    have hclauseSq : (Encoding.encodeList id C).length ≤ L ^ 2 :=
      (by omega : (Encoding.encodeList id C).length ≤ L).trans hLSq
    change _ ≤ 400 * L ^ 2
    omega
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hz12, hc12, hz9]

end Guard

namespace Filter

theorem guard_eval (H C : Clause) (width source output : List Bool) (regs : Regs) :
    ∃ t ≤ 400 * ((clauseCode H).length + (clauseCode C).length + width.length + 1) ^ 2 + 1,
      ∃ rf : Regs, Eval guard t
        (state regs (clauseCode H) width source output [] (clauseCode C))
        (state rf (clauseCode H) width source output [] (clauseCode C)) ∧
      rf 12 = (decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C) := by
  let d := state regs (clauseCode H) width source output [] (clauseCode C)
  let a := projectState guardReg guardStack d
  obtain ⟨t, ht, b, hb, hbs, hbr⟩ := Guard.command_eval H C a rfl rfl (by intro i; fin_cases i <;> rfl)
  let e := embedState guardReg guardStack d b
  have hr : Function.Injective guardReg := Fin.castAdd_injective 13 3
  have hs : Function.Injective guardStack := Fin.castAdd_injective 11 3
  have he := eval_liftCommand_from_state Guard.command 9 9 guardReg guardStack d hr hs hb
  have hes : e.stacks = d.stacks := by
    funext i
    by_cases hi : ∃ j, guardStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [embedState_stack _ _ _ _ hs j, hbs]
      rfl
    · exact embedState_stack_frame _ _ _ _ _ hi
  have heq : e = state e.regs (clauseCode H) width source output [] (clauseCode C) :=
    congrArg₂ StructuredProgram.State.mk rfl hes
  refine ⟨t + 1, Nat.add_le_add_right ht 1, e.regs, heq ▸ he, ?_⟩
  exact (embedState_register guardReg guardStack d b hr 12).trans hbr

theorem transfer_in (regs : Regs) (core width source output bits : List Bool) :
    Eval (transfer 13 9) (3 * bits.length + 3)
      (state regs core width source output bits.reverse [])
      (state (readRegs regs 0 1 none) core width source output [] bits) := by
  have h := ListRegisterProgram.transfer_run (r := 16) (s := 14) 13 9 0 1
    (by decide) (by decide) regs (state regs core width source output bits.reverse []).stacks
  have hs : StackRoutines.transferStacks 13 9
      (state regs core width source output bits.reverse []).stacks =
      (state (readRegs regs 0 1 none) core width source output [] bits).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  apply Eval.call
  rw [hs] at h
  simpa [ListRegisterProgram.Run, state, StructuredProgram.State.withPC] using h

theorem transfer_out (regs : Regs) (core width source output bits : List Bool) :
    Eval (transfer 9 13) (3 * bits.length + 3)
      (state regs core width source output [] bits)
      (state (readRegs regs 0 1 none) core width source output bits.reverse []) := by
  have h := ListRegisterProgram.transfer_run (r := 16) (s := 14) 9 13 0 1
    (by decide) (by decide) regs (state regs core width source output [] bits).stacks
  have hs : StackRoutines.transferStacks 9 13
      (state regs core width source output [] bits).stacks =
      (state (readRegs regs 0 1 none) core width source output bits.reverse []).stacks := by
    funext i
    fin_cases i <;> simp [state, StackRoutines.transferStacks]
  apply Eval.call
  rw [hs] at h
  simpa [ListRegisterProgram.Run, state, StructuredProgram.State.withPC] using h

theorem emitReg_injective : Function.Injective emitReg := by decide

theorem emitStack_injective : Function.Injective emitStack := by decide

private theorem embed_emit (regs : Regs) (v p f : Bool)
    (core width source₀ output₀ payload₀ source output payload clause : List Bool) :
    embedState emitReg emitStack (state regs core width source₀ output₀ payload₀ [])
      (SparsePriorityPrimitives.Filter.filterState v p f source clause output payload) =
      state (flags regs v p f) core width source output payload clause := by
  apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective emitStack_injective
  · intro i; fin_cases i <;> simp [emitReg, flags, state, SparsePriorityPrimitives.Filter.filterState]
  · intro i hi
    have h13 : i ≠ 13 := fun h => hi ⟨0, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨1, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h13, h14, h15]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h11 : i ≠ 11 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h12 : i ≠ 12 := fun h => hi ⟨2, h.symm⟩
    have h13 : i ≠ 13 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emit_eval (regs : Regs) (bits core width source output : List Bool) :
    Eval emit (SparsePriorityPrimitives.Filter.emitIfSelectedSteps (regs 15) bits + 1)
      (state regs core width source output bits.reverse [])
      (state (flags regs false true false) core width source
        (if regs 15 then true :: (Encoding.frame bits ++ output) else output) [] []) := by
  have h := eval_call_lifted SparsePriorityPrimitives.Filter.emitIfSelectedProgram emitReg emitStack
    (state regs core width source output bits.reverse []) emitReg_injective emitStack_injective
    (SparsePriorityPrimitives.Filter.emitIfSelected_trace (regs 15) bits source [] output (regs 13) (regs 14))
  simpa only [embed_emit, flags_self, emit] using h

theorem callback_eval (H C : Clause) (width source output : List Bool) (regs : Regs) :
    ∃ t ≤ cost H width (clauseCode C), ∃ rf : Regs,
      rf 13 = false ∧ rf 14 = true ∧ rf 15 = false ∧
      Eval callback t
        (state regs (clauseCode H) width source output (clauseCode C).reverse [])
        (state rf (clauseCode H) width source
          (if decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C
            then true :: (Encoding.frame (clauseCode C) ++ output) else output) [] []) := by
  obtain ⟨t, ht, rg, hg, hr⟩ := guard_eval H C width source output (readRegs regs 0 1 none)
  let selected := Function.update rg 15 (rg 12)
  have hset : Eval (.base (.atom (.copy 15 12))) 1
      (state rg (clauseCode H) width source output [] (clauseCode C))
      (state selected (clauseCode H) width source output [] (clauseCode C)) := .base (.atom _ _)
  let restored := readRegs selected 0 1 none
  have hs : restored 15 = (decide (C.length = BinaryArithmetic.toNat width) &&
      ExecCNF.subset H C) := by simp [restored, selected, readRegs, hr]
  have he := emit_eval restored (clauseCode C) (clauseCode H) width source output
  rw [hs] at he
  have hfull := (transfer_in regs (clauseCode H) width source output (clauseCode C)).seq
    (hg.seq (hset.seq ((transfer_out selected (clauseCode H) width source output (clauseCode C)).seq he)))
  refine ⟨_, ?_, flags restored false true false, by simp [flags], by simp [flags],
    by simp [flags], hfull⟩
  have hem := SparsePriorityPrimitives.Filter.emitIfSelected_steps_le
    (decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C) (clauseCode C)
  dsimp [cost]
  have hsquare := Nat.le_self_pow (by decide : 2 ≠ 0)
    ((clauseCode H).length + (clauseCode C).length + width.length + 1)
  omega

theorem record_state (regs : Regs) (core width source output payload clause tail bits : List Bool)
    (v p f : Bool) :
    RecordPrograms.state ports (state regs core width source output payload clause)
      v p f tail bits = state (flags regs v p f) core width tail output bits clause := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ports, state]

theorem callback_contract (H : Clause) (width : List Bool) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false) (cost H width)
      (Ready H width) (SparsePriorityPrimitives.Filter.FilterEffect 12 (keep H width))
      (fun bits => ∃ C : Clause, bits = clauseCode C) := by
  intro bits tail base hbits hbase
  obtain ⟨C, rfl⟩ := hbits
  obtain ⟨regs, source, output, payload, rfl⟩ := hbase.shape
  obtain ⟨t, ht, rf, h13, h14, h15, he⟩ :=
    callback_eval H C width tail output (flags regs false true false)
  let out := if decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C
    then true :: (Encoding.frame (clauseCode C) ++ output) else output
  let next := state rf (clauseCode H) width [] out [] []
  have hf : flags rf false true false = rf := by
    simpa only [h13, h14, h15] using flags_self rf
  refine ⟨t, next, ht, ⟨rf, [], out, [], rfl⟩, ?_, ?_⟩
  · constructor
    simp [next, out, state]
  · simpa only [next, record_state, hf] using he

theorem formulaCode_records (F : Formula) :
    formulaCode F = Encoding.encodeList id (records F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [formulaCode, records, Encoding.encodeList] using ih

theorem filter_records (F : Formula) (H : Clause) (width : List Bool) :
    (records F).filter (keep H width) = records (result F H width) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp only [records, result] at ih
    cases h : decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C <;>
      simp [records, result, h, ih]

theorem scan_eval (F : Formula) (H : Clause) (width : List Bool)
    (acc : List (List Bool)) (regs : Regs) :
    ∃ t ≤ 3 + RecordPrograms.budget (cost H width) (records F), ∃ rf : Regs,
      Eval scan t
        (state regs (clauseCode H) width (formulaCode F) (Encoding.encodeList id acc) [] [])
        (state rf (clauseCode H) width []
          (Encoding.encodeList id ((records (result F H width)).reverse ++ acc)) [] []) := by
  let d := state regs (clauseCode H) width (formulaCode F) (Encoding.encodeList id acc) [] []
  have hvalid : ∀ bits ∈ records F, ∃ C : Clause, bits = clauseCode C := by
    intro bits hb
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨C, rfl⟩
  obtain ⟨t, next, ht, hnext, hhistory, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (cost H width) (Ready H width)
    (SparsePriorityPrimitives.Filter.FilterEffect 12 (keep H width))
    (fun bits => ∃ C : Clause, bits = clauseCode C) (callback_contract H width)
    (records F) [] d hvalid ⟨regs, _, _, [], rfl⟩ (regs 13) (regs 14) (regs 15)
  have hout := SparsePriorityPrimitives.Filter.filterVisits_result 12 (keep H width) hhistory acc
    (show d.stacks 12 = _ from rfl)
  obtain ⟨rf, source, output, payload, rfl⟩ := hnext.shape
  have hout' : output = Encoding.encodeList id ((records (result F H width)).reverse ++ acc) := by
    simpa [d, state, filter_records] using hout
  have hany : (records F).any (fun _ => false) = false := by simp
  refine ⟨t, ht, flags rf false true false, ?_⟩
  simpa only [scan, d, List.append_nil, record_state, flags_self, ← formulaCode_records,
    hany, SparsePriorityPrimitives.Filter.unread_false, hout'] using he


theorem member_length_le (records : List (List Bool)) (bits : List Bool) (h : bits ∈ records) :
    bits.length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rw [Encoding.length_encodeList_cons]
      simp only [id_eq]
      omega
    · exact (ih h).trans (by rw [Encoding.length_encodeList_cons]; omega)

theorem budget_le (records : List (List Bool)) (H : Clause) (width : List Bool) :
    3 + RecordPrograms.budget (cost H width) records ≤
      600 * ((clauseCode H).length + (Encoding.encodeList id records).length +
        width.length + 1) ^ 3 := by
  let L := (clauseCode H).length + (Encoding.encodeList id records).length + width.length + 1
  have hc : ∀ bits ∈ records, cost H width bits ≤ 0 * bits.length + 500 * L ^ 2 := by
    intro bits hb
    have hlen := member_length_le records bits hb
    simp only [Nat.zero_mul, Nat.zero_add, cost]
    exact Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by dsimp [L]; omega) 2)
  have hb := RecordPrograms.program_budget_le_input (cost H width) records 0 (500 * L ^ 2) hc
  change 4 + RecordPrograms.budget (cost H width) records ≤
    (0 + 500 * L ^ 2 + 17) * ((Encoding.encodeList id records).length + 1) at hb
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hinput : (Encoding.encodeList id records).length + 1 ≤ L := by dsimp [L]; omega
  have hm := Nat.mul_le_mul_left (500 * L ^ 2 + 17) hinput
  have hsq : 1 ≤ L ^ 2 := one_le_pow₀ hL
  change _ ≤ 600 * L ^ 3
  nlinarith

theorem scan_polynomial (F : Formula) (H : Clause) (width : List Bool)
    (acc : List (List Bool)) (regs : Regs) :
    ∃ t ≤ 600 * ((clauseCode H).length + (formulaCode F).length + width.length + 1) ^ 3,
      ∃ rf : Regs, Eval scan t
        (state regs (clauseCode H) width (formulaCode F) (Encoding.encodeList id acc) [] [])
        (state rf (clauseCode H) width []
          (Encoding.encodeList id ((records (result F H width)).reverse ++ acc)) [] []) := by
  obtain ⟨t, ht, rf, he⟩ := scan_eval F H width acc regs
  refine ⟨t, ht.trans ?_, rf, he⟩
  simpa only [← formulaCode_records] using budget_le (records F) H width


theorem startOutput_eval (regs : Regs) (core width source : List Bool) :
    Eval startOutput 2 (state regs core width source [] [] [])
      (state (Function.update regs 0 false) core width source [false] [] []) := by
  have h := (Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.set (r := 16) (s := 14) 0 false)
    (state regs core width source [] [] []))).seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push 12 0)
      ((StructuredProgram.Atom.set 0 false).eval (state regs core width source [] [] []))))
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [state, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]

theorem command_eval (F : Formula) (H : Clause) (width : List Bool) (regs : Regs) :
    ∃ t ≤ 600 * ((clauseCode H).length + (formulaCode F).length + width.length + 1) ^ 3 + 2,
      ∃ rf : Regs, Eval command t
        (state regs (clauseCode H) width (formulaCode F) [] [] [])
        (state rf (clauseCode H) width []
          (formulaCode ((result F H width).reverse)) [] []) := by
  obtain ⟨t, ht, rf, he⟩ := scan_polynomial F H width [] (Function.update regs 0 false)
  refine ⟨2 + t, by omega, rf, ?_⟩
  have hfull := (startOutput_eval regs (clauseCode H) width (formulaCode F)).seq he
  simpa [command, formulaCode_records, records, List.map_reverse] using hfull


end Filter

namespace CountThreshold

/-- Compare a scanned family's exact size with a binary threshold without expanding
that threshold to unary. The only unary count has length bounded by the input. -/
theorem command_eval (records : List (List Bool)) (d : Data)
    (hin : d.stacks 5 = Encoding.encodeList id records)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ 300 * ((Encoding.encodeList id records).length + (d.stacks 4).length + 1) ^ 2,
      ∃ e : Data, Eval command t d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 4) ≤ records.length) := by
  let a := SparsePriorityPrimitives.Count.counted records d
  have ha7 : a.stacks 7 = Encoding.encodeNat records.length := by
    simp [a, SparsePriorityPrimitives.Count.counted]
  have ha5 : a.stacks 5 = [] := by simp [a, SparsePriorityPrimitives.Count.counted]
  have ha6 : a.stacks 6 = [] := by simpa [a, SparsePriorityPrimitives.Count.counted] using h6
  have ha8 : a.stacks 8 = [] := by simpa [a, SparsePriorityPrimitives.Count.counted] using h8
  obtain ⟨t, ht, bits, b, hb, hvalue, hlength, hbs, _⟩ :=
    SparsePriorityPrimitives.Count.toBinary_eval records.length a ha7 ha5 ha6 ha8
  have hb5 : b.stacks 5 = [] := by simp [hbs, a, SparsePriorityPrimitives.Count.counted]
  have hb6 : b.stacks 6 = bits := by simp [hbs]
  have hb7 : b.stacks 7 = [] := by simp [hbs]
  have hb8 : b.stacks 8 = [] := by simpa [hbs, a, SparsePriorityPrimitives.Count.counted] using h8
  have hb4 : b.stacks 4 = d.stacks 4 := by simp [hbs, a, SparsePriorityPrimitives.Count.counted]
  obtain ⟨u, hu, c, hc, hcs, hc0, _⟩ := SparsePriorityPrimitives.Count.less_eval 6 4 b
    (by decide) (by decide) hb5 hb7 hb8
  let z := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 4 0).eval c
  let e := SparsePriorityPrimitives.Tuple.cleared 6 z
  have hc6 : c.stacks 6 = bits := by simpa [hcs] using hb6
  have hz6 : z.stacks 6 = bits := hc6
  have hu' : u ≤ 20 * (bits.length + (d.stacks 4).length + 1) := by
    simpa only [hb6, hb4] using hu
  refine ⟨SubexpSunflowerProgram.CountRecords.steps records +
    (t + (u + (1 + (2 * (z.stacks 6).length + 3)))), ?_, e,
    (SparsePriorityPrimitives.Count.count_eval records d hin h7).seq
      (hb.seq (hc.seq ((Eval.base (.atom _ _)).seq (SparsePriorityPrimitives.Tuple.clear_eval 6 z)))),
    ?_, ?_⟩
  · rw [hz6]
    have hcount := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hrecords := Encoding.length_encodeList_lower id records
    have hrecords' : records.length ≤ (Encoding.encodeList id records).length := by omega
    have hbits : bits.length ≤ (Encoding.encodeList id records).length :=
      hlength.trans hrecords'
    let H := (Encoding.encodeList id records).length + (d.stacks 4).length + 1
    have hH : 1 ≤ H := by dsimp [H]; omega
    have hEH : (Encoding.encodeList id records).length ≤ H := by dsimp [H]; omega
    have hRH : records.length ≤ H := hrecords'.trans hEH
    have hBH : bits.length ≤ H := hbits.trans hEH
    have hsq : H ≤ H ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right H hH
    have hRsq : records.length ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hRH 2
    have hcount' : SubexpSunflowerProgram.CountRecords.steps records ≤ 7 * H ^ 2 := by
      have h7 := Nat.mul_le_mul_left 7 hsq
      omega
    rw [FrontendProgram.initializeBound_eq] at ht
    have ht' : t ≤ 32 * H ^ 2 := by
      have h8 := Nat.mul_le_mul_left 8 hRsq
      have h14 := Nat.mul_le_mul_left 14 (hRH.trans hsq)
      have h10 : 10 ≤ 10 * H ^ 2 := by omega
      omega
    have hsum : bits.length + (d.stacks 4).length + 1 ≤ H := by
      dsimp [H]
      omega
    have hu'' : u ≤ 20 * H ^ 2 :=
      (hu'.trans (Nat.mul_le_mul_left 20 hsum)).trans (Nat.mul_le_mul_left 20 hsq)
    have hclear : 1 + (2 * bits.length + 3) ≤ 6 * H ^ 2 := by
      have h6 := Nat.mul_le_mul_left 6 hsq
      omega
    change SubexpSunflowerProgram.CountRecords.steps records +
      (t + (u + (1 + (2 * bits.length + 3)))) ≤ 300 * H ^ 2
    omega
  · funext i
    fin_cases i <;>
      simp [e, z, SparsePriorityPrimitives.Tuple.cleared, StackRoutines.clearStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        hcs, hbs, a, SparsePriorityPrimitives.Count.counted, h6, h7]
  · have hnot : (!decide (records.length < BinaryArithmetic.toNat (d.stacks 4))) =
        decide (BinaryArithmetic.toNat (d.stacks 4) ≤ records.length) := by
      by_cases h : records.length < BinaryArithmetic.toNat (d.stacks 4)
      · simp [h, Nat.not_le_of_lt h]
      · have hh : BinaryArithmetic.toNat (d.stacks 4) ≤ records.length := by omega
        simp [h, hh]
    simpa [e, z, SparsePriorityPrimitives.Tuple.cleared, readRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.withPC,
      StructuredProgram.State.ofCfg, execInstr, hc0, hb6, hb4, hvalue] using hnot

end CountThreshold

namespace Selector

private theorem embed_stacks_eq {r s R S : ℕ} (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (d : State R S) (b : State r s)
    (hs : Function.Injective stack) (out : Fin S → List Bool)
    (hports : ∀ j, b.stacks j = out (stack j))
    (hframe : ∀ i, (¬ ∃ j, stack j = i) → d.stacks i = out i) :
    (embedState register stack d b).stacks = out := by
  funext i
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    exact (embedState_stack register stack d b hs j).trans (hports j)
  · exact (embedState_stack_frame register stack d b i hi).trans (hframe i hi)

theorem copy_eval (source target : Fin 24) (d : Data)
    (hs : source ≠ target) (hs8 : source ≠ 8) (ht8 : (8 : Fin 24) ≠ target)
    (h8 : d.stacks 8 = []) (ht : d.stacks target = []) :
    Eval (copy source target) (7 * (d.stacks source).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks target (d.stacks source)⟩ := by
  have h := ListRegisterProgram.copy_run source target 8 (0 : Fin 24) 1
    hs hs8 ht8 (by decide) d.regs d.stacks h8
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, ht] using h

theorem thresholdStack_injective : Function.Injective thresholdStack := by decide

theorem thresholdCall_eval (F : Formula) (d : Data)
    (h5 : d.stacks 5 = Filter.formulaCode F)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ 300 * ((Filter.formulaCode F).length + (d.stacks 17).length + 1) ^ 2 + 1,
      ∃ e : Data, Eval thresholdCall t d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 17) ≤ F.length) ∧
        (∀ i : Fin 24, 13 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 11) thresholdStack d
  have hin : a.stacks 5 = Encoding.encodeList id (Filter.records F) := by
    simpa [a, projectState, thresholdStack, ← Filter.formulaCode_records] using h5
  obtain ⟨t, ht, b, he, hb, hv⟩ := CountThreshold.command_eval (Filter.records F) a hin
    (by simpa [a, projectState, thresholdStack] using h6)
    (by simpa [a, projectState, thresholdStack] using h7)
    (by simpa [a, projectState, thresholdStack] using h8)
  let e := embedState (Fin.castAdd 11) thresholdStack d b
  refine ⟨t + 1, by simpa [a, projectState, thresholdStack,
    ← Filter.formulaCode_records] using Nat.add_le_add_right ht 1,
    e, eval_liftCommand_from_state _ 5 5 (Fin.castAdd 11) thresholdStack d
      (Fin.castAdd_injective 13 11) thresholdStack_injective he, ?_, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ thresholdStack_injective
    · intro j
      rw [hb]
      fin_cases j <;> simp [a, projectState, thresholdStack]
    · intro i hi
      have hi5 : i ≠ 5 := fun h => hi ⟨5, h.symm⟩
      simp [hi5]
  · simpa [e, a, projectState, thresholdStack, Filter.records, List.length_map] using
      (embedState_register _ _ _ _ (Fin.castAdd_injective 13 11) 4).trans hv
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem filterStack_injective : Function.Injective filterStack := by decide

theorem filterCall_eval (F : Formula) (H : Clause) (width : List Bool) (d : Data)
    (h9 : d.stacks 9 = Filter.clauseCode H) (h16 : d.stacks 16 = width)
    (h10 : d.stacks 10 = Filter.formulaCode F)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
    ∃ t ≤ 600 * ((Filter.clauseCode H).length + (Filter.formulaCode F).length +
      width.length + 1) ^ 3 + 3, ∃ e : Data,
      Eval filterCall t d e ∧
      e.stacks = Function.update (Function.update d.stacks 10 []) 12
        (Filter.formulaCode ((Filter.result F H width).reverse)) ∧
      (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 8) filterStack d
  have ha : a = Filter.state a.regs (Filter.clauseCode H) width
      (Filter.formulaCode F) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [filterStack, h9, h16, h10, h11, h12]
    all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5 | exact hwork 6 | exact hwork 7 | exact hwork 8
  obtain ⟨t, ht, rf, he⟩ := Filter.command_eval F H width a.regs
  rw [← ha] at he
  let b := Filter.state rf (Filter.clauseCode H) width []
    (Filter.formulaCode ((Filter.result F H width).reverse)) [] []
  let e := embedState (Fin.castAdd 8) filterStack d b
  refine ⟨t + 1, by omega, e, eval_liftCommand_from_state _ 11 12
    (Fin.castAdd 8) filterStack d (Fin.castAdd_injective 16 8) filterStack_injective he, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ filterStack_injective
    · intro j
      fin_cases j <;> simp [b, Filter.state, filterStack, h9, h16, h11]
      all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5 | exact hwork 6 | exact hwork 7 | exact hwork 8
    · intro i hi
      have hi10 : i ≠ 10 := fun h => hi ⟨11, h.symm⟩
      have hi12 : i ≠ 12 := fun h => hi ⟨12, h.symm⟩
      simp [hi10, hi12]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem checkCandidate_eval_oai (F : Formula) (H : Clause) (width : List Bool) (d : Data)
    (h9 : d.stacks 9 = Filter.clauseCode H) (h16 : d.stacks 16 = width)
    (h18 : d.stacks 18 = Filter.formulaCode F)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = []) (h12 : d.stacks 12 = []) :
    ∃ t ≤ checkCandidateBound F H width (d.stacks 17), ∃ e : Data,
      Eval checkCandidate t d e ∧
      e.stacks = Function.update d.stacks 12 (Filter.formulaCode (selectedFamily F H width)) ∧
      e.regs 4 = decide (BinaryArithmetic.toNat (d.stacks 17) ≤ (Filter.result F H width).length) ∧
      (∀ i : Fin 24, 16 ≤ i.val → e.regs i = d.regs i) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks 10 (d.stacks 18)⟩
  have ha := copy_eval 18 10 d (by decide) (by decide) (by decide) (hwork 8) h10
  have ha9 : a.stacks 9 = Filter.clauseCode H := by simp [a, h9]
  have ha16 : a.stacks 16 = width := by simp [a, h16]
  have ha10 : a.stacks 10 = Filter.formulaCode F := by simp [a, h18]
  have haw (i : Fin 9) : a.stacks (Fin.castAdd 15 i) = [] := by
    have hi : Fin.castAdd 15 i ≠ (10 : Fin 24) := by
      intro h
      have hh := congrArg Fin.val h
      have := i.isLt
      change i.val = 10 at hh
      omega
    simpa [a, hi] using hwork i
  obtain ⟨t, ht, b, hb, hbs, hbr⟩ := filterCall_eval F H width a ha9 ha16 ha10 haw
    (by simpa [a] using h11) (by simpa [a] using h12)
  have hbstate : b.stacks = Function.update d.stacks 12
      (Filter.formulaCode (selectedFamily F H width)) := by
    rw [hbs]
    funext i
    by_cases hi10 : i = 10
    · subst i; simp [h10]
    · simp [a, Function.update_apply, hi10, selectedFamily]
  have hb12 : b.stacks 12 = Filter.formulaCode (selectedFamily F H width) := by simp [hbstate]
  have hb8 : b.stacks 8 = [] := by simpa [hbstate] using hwork 8
  have hb5 : b.stacks 5 = [] := by simpa [hbstate] using hwork 5
  let c : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 5 (b.stacks 12)⟩
  have hc := copy_eval 12 5 b (by decide) (by decide) (by decide) hb8 hb5
  have hc5 : c.stacks 5 = Filter.formulaCode (selectedFamily F H width) := by simp [c, hb12]
  have hc6 : c.stacks 6 = [] := by simpa [c, hbstate] using hwork 6
  have hc7 : c.stacks 7 = [] := by simpa [c, hbstate] using hwork 7
  have hc8 : c.stacks 8 = [] := by simpa [c, hbstate] using hwork 8
  have hc17 : c.stacks 17 = d.stacks 17 := by simp [c, hbstate]
  obtain ⟨u, hu, e, he, hes, hev, her⟩ :=
    thresholdCall_eval (selectedFamily F H width) c hc5 hc6 hc7 hc8
  refine ⟨7 * (d.stacks 18).length + 5 + (t + (7 * (b.stacks 12).length + 5 + u)),
    ?_, e, ha.seq (hb.seq (hc.seq he)), ?_, ?_, ?_⟩
  · rw [hc17] at hu
    simp only [h18, hb12]
    unfold checkCandidateBound
    omega
  · rw [hes]
    funext i
    by_cases hi5 : i = 5
    · subst i; simpa using hwork 5
    · simp [c, hbstate, hi5]
  · simpa only [hc17, selectedFamily, List.length_reverse] using hev
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hbi := hbr i hi
    have hei := her i (by omega)
    simpa [a, c, readRegs, hi0, hi1, hbi] using hei

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval_oai
