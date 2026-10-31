-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:45:32.73177+00:00
-- url     : https://prove2.me/submissions/8ee644dd-8ad3-4e0e-8855-bb23d75fcb54

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

theorem copy_call_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk htmp

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem route_eval (p : Route) (hp : routeValid p) (a : Data)
    (ht : a.stacks 767 = []) : Eval (route p) (routeCost p a) a (routed p a) := by
  obtain ⟨hsd,hst,hdt⟩ := hp
  have hc := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
  have hsrc : clearStacks p.2 a.stacks p.1 = a.stacks p.1 :=
    clearStacks_frame _ _ _ hsd
  have htmp : clearStacks p.2 a.stacks 767 = [] := by
    rw [clearStacks_frame _ _ _ (Ne.symm hdt),ht]
  have hf := BankRoutines.copy_call_eval p.1 p.2 (767 : Fin 896) (0 : Fin 40) 1
    hsd hst (Ne.symm hdt) (by decide) (readRegs a.regs 0 1 none)
    (clearStacks p.2 a.stacks) htmp
  have he : copyStacks p.1 p.2 (clearStacks p.2 a.stacks) =
      Function.update a.stacks p.2 (a.stacks p.1) := by
    funext i
    by_cases hi : i = p.2
    · subst i; simp [copyStacks,clearStacks,hsd]
    · simp [copyStacks,clearStacks,hi]
  have hcost : 2*(a.stacks p.2).length+3+(7*(a.stacks p.1).length+5) = routeCost p a := by
    unfold routeCost
    omega
  simpa only [route,routed,hsrc,he,readRegs_reset,hcost] using hc.seq hf

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls SubexpIncidencePlanPrimitives

theorem tested_active (regs : Fin 10 → Bool) (n : ℕ) :
    testedRegs regs n 9 = decide (n ≠ 0) := by
  cases n <;> simp [testedRegs, readRegs, List.replicate_succ]

theorem peek_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    Eval peek 1 (data base regs j n out) (data base (testedRegs regs n) j n out) := by
  exact .base (.atom _ _)

theorem pop_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    Eval pop 1 (data base regs j (n+1) out)
      (data base (readRegs regs 7 9 (some true)) j n out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (6 : Fin 10) 7 9)
    (data base regs j (n+1) out))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · simp [ StructuredProgram.Atom.instr, execInstr, List.replicate_succ]
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, List.replicate_succ]

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramIndex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime, self-delimiting natural-index alphabet. The range control is the
existing unary loop, with one delimiter inserted in each emitted payload. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Index
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpIncidencePlanPrimitives
open SubexponentialSAT.SubexpUnaryRangeProgram (data unary testedRegs tested_active)

theorem indexPrefix_eq_records (js : List ℕ) :
    indexPrefix js ++ [false] = ProgramEncoding.encodeRecords (js.map Encoding.encodeNat) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simpa [indexPrefix, ProgramEncoding.encodeRecords, Encoding.encodeList,
      List.append_assoc] using congrArg (fun x => true :: Encoding.frame (Encoding.encodeNat j) ++ x) ih

theorem emitCurrent_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Eval emitCurrent (12*j+27) (data base regs j n out)
      (data base rf (j+1) n (true :: Encoding.frame (Encoding.encodeNat j) ++ out)) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = regs i) := by
  let a := data base regs j n out
  let b := copied 5 1 a
  let c := Subexp.TupleProgram.pushedState 1 0 false b
  let d := SubexpUnaryRangeProgram.selected c
  let e := emitted true (Encoding.encodeNat j) d
  let f := incremented 5 e
  have h1 := copy_eval 5 1 3 a (by decide) (by decide) (by decide) (by rfl)
  have h2 := Subexp.TupleProgram.pushConst_eval 1 0 false b
  have h3 : Eval SubexpUnaryRangeProgram.setSelected 1 c d := .base (.atom _ _)
  have h4 := emit_eval true (Encoding.encodeNat j) d
    (by simp [d, SubexpUnaryRangeProgram.selected, c,
      b, copied, StackRoutines.copyStacks, a, Encoding.encodeNat])
    (by simp [d, SubexpUnaryRangeProgram.selected])
  have h5 := increment_eval 5 e
  have hf : f = data base f.regs (j+1) n
      (true :: Encoding.frame (Encoding.encodeNat j) ++ out) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i
    fin_cases i <;> simp [ e, emitted, d, SubexpUnaryRangeProgram.selected,
      c, b, copied, StackRoutines.copyStacks, a,
      List.replicate_succ]
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  change Eval emitCurrent _ a f at h
  rw [hf] at h
  refine ⟨f.regs, ?_, ?_⟩
  · convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp [a, SubexpNormalizeProgram.emitIfSelectedSteps]
    omega
  · intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    have h4 : i ≠ 4 := by intro h; subst i; change 7 ≤ 4 at hi; omega
    simp [f, incremented, e, emitted, d, SubexpUnaryRangeProgram.selected,
      c, b, copied, readRegs, a, h0, h1, h4]

theorem loop_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool)
    (hg : regs 9 = decide (n ≠ 0)) :
    ∃ rf, Eval loop (steps j n) (data base regs j n out)
      (data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)) ∧ rf 9 = false := by
  induction n generalizing regs j out with
  | zero =>
      refine ⟨regs, ?_, by simpa using hg⟩
      simpa [steps, indexPrefix] using
        (Eval.while_false
          (body := .seq SubexpUnaryRangeProgram.pop (.seq emitCurrent SubexpUnaryRangeProgram.peek))
          (a := data base regs j 0 out) (show regs 9 = false by simpa using hg))
  | succ n ih =>
      obtain ⟨re, he, hr⟩ := emitCurrent_eval base (readRegs regs 7 9 (some true)) j n out
      have hp := SubexpUnaryRangeProgram.pop_eval base regs j n out
      have ht := SubexpUnaryRangeProgram.peek_eval base re (j+1) n
        (true :: Encoding.frame (Encoding.encodeNat j) ++ out)
      obtain ⟨rf, hf, hrf⟩ := ih (testedRegs re n) (j+1)
        (true :: Encoding.frame (Encoding.encodeNat j) ++ out) (tested_active re n)
      have h := Eval.while_true (show (data base regs j (n+1) out).regs 9 = true by simpa using hg)
        (hp.seq (he.seq ht)) hf
      refine ⟨rf, ?_, hrf⟩
      convert h using 1
      · simp only [steps]; omega
      · simp [indexPrefix, List.range'_succ, List.reverse_cons, List.flatMap_append,
          List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem command_eval (base : Data) (regs : Fin 10 → Bool) (j n : ℕ) (out : List Bool) :
    ∃ rf, Eval command (1 + steps j n) (data base regs j n out)
      (data base rf (j+n) 0 (indexPrefix (List.range' j n).reverse ++ out)) ∧ rf 9 = false := by
  obtain ⟨rf, h, hr⟩ := loop_eval base (testedRegs regs n) j n out (tested_active regs n)
  exact ⟨rf, (SubexpUnaryRangeProgram.peek_eval base regs j n out).seq h, hr⟩

theorem steps_le (j n : ℕ) : 1 + steps j n ≤ n * (12*(j+n)+30) + 2 := by
  induction n generalizing j with
  | zero => simp [steps]
  | succ n ih =>
      have h := ih (j+1)
      simp only [steps]
      nlinarith

theorem alphabet_eval (base : Data) (regs : Fin 10 → Bool) (s : ℕ) :
    ∃ rf, Eval command (1 + steps 0 s) (data base regs 0 s [false])
      (data base rf s 0 (ProgramEncoding.encodeRecords (alphabet s))) ∧ rf 9 = false := by
  obtain ⟨rf, h, hr⟩ := command_eval base regs 0 s [false]
  refine ⟨rf, ?_, hr⟩
  simpa [alphabet, indexPrefix_eq_records, ← List.range_eq_range'] using h

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterNativeReferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked-reference stream is generated by a fixed program from the binary
clause count. Both binary-to-unary expansion and the quadratic framed stream
emission are part of the measured run. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative.References
open SubexponentialSAT BitProgram StructuredCalls

theorem command_eval (regs : Fin 10 → Bool) (bits : List Bool) :
    ∃ t rf, t ≤ budget bits ∧ Eval command t (input regs bits)
      (output rf (CounterPrograms.value bits)) := by
  let a := input regs bits
  let d := projectState registers stackMap a
  obtain ⟨n,he,hn⟩ := CounterConversions.unary_correct d (by simp [d,a,input,projectState,stackMap])
  let m := CounterPrograms.value bits
  let e := CounterConversions.state CounterConversions.zeroRegs [] (List.replicate m true)
  have he' : Eval CounterConversions.unaryCmd n d e := by
    simpa [d,a,input,projectState,stackMap,e,m] using he
  let b := embedState registers stackMap a e
  have hexpand : Eval expand (n+1) a b :=
    eval_liftCommand_from_state _ _ _ _ _ _ (Fin.castAdd_injective 3 7) (by decide) he'
  have hb : b.stacks=Function.update (fun _ => []) 6 (List.replicate m true) := by
    funext i
    have h0 := embedState_stack registers stackMap a e (by decide) 0
    have h1 := embedState_stack registers stackMap a e (by decide) 1
    have h2 := embedState_stack registers stackMap a e (by decide) 2
    fin_cases i
    all_goals first
      | simpa [b,e,stackMap,CounterConversions.state] using h0
      | simpa [b,e,stackMap,CounterConversions.state] using h1
      | simpa [b,e,stackMap,CounterConversions.state] using h2
      | (rw [show b.stacks _=a.stacks _ from
           embedState_stack_frame registers stackMap a e _ (by decide)]
         simp [a,input])
  let c := Subexp.TupleProgram.pushedState 7 0 false b
  have hc : c=SubexpUnaryRangeProgram.data b c.regs 0 m [false] := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [c,hb]
  obtain ⟨rf,hindex,_⟩ := RowSelectionProgram.Index.alphabet_eval b c.regs m
  rw [←hc] at hindex
  let f := SubexpUnaryRangeProgram.data b rf m 0
    (ProgramEncoding.encodeRecords (RowSelectionProgram.Index.alphabet m))
  have hclear := BankRoutines.clear_call_eval (5 : Fin 10) (0 : Fin 10) 1 f.regs f.stacks
  have hf : (⟨readRegs f.regs 0 1 none,
      StackRoutines.clearStacks 5 f.stacks⟩ : Data)=
      output (readRegs rf 0 1 none) m := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [f,StackRoutines.clearStacks,
      output,hb]
  rw [hf] at hclear
  have heval := hexpand.seq ((Subexp.TupleProgram.pushConst_eval 7 0 false b).seq
    (hindex.seq hclear))
  refine ⟨(n+1)+(2+((1+RowSelectionProgram.Index.steps 0 m)+(2*m+3))),
    readRegs rf 0 1 none,?_,?_⟩
  · have hi := RowSelectionProgram.Index.steps_le 0 m
    have hn' : n ≤ CounterConversions.coreBound bits := by
      simpa [d,a,input,projectState,stackMap] using hn
    change _ ≤ CounterConversions.coreBound bits+m*(12*m+32)+8
    nlinarith
  · simpa [command,expand,a,f,SubexpUnaryRangeProgram.data] using heval

end SubexponentialSAT.SqrtLog.LeafOuterNative.References

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

variable {X Row : Type*} [Fintype X] {m : ℕ}


open LeafOuterProgram

theorem references_eval_oai (a : Data) (ha : ReferencesReady a) :
    ∃ t b, t ≤ routeCost (782,0) a+LeafOuterNative.References.budget (a.stacks 782)+1 ∧
      Eval references t a b ∧ b.stacks=Function.update a.stacks 320
        (ProgramEncoding.encodeRecords (RowSelectionProgram.Index.alphabet
          (CounterPrograms.value (a.stacks 782)))) := by
  let c := routed (782,0) a
  let d := projectState referenceRegisters referenceStacks c
  have hd : d=LeafOuterNative.References.input d.regs (a.stacks 782) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [d,c,projectState,referenceStacks,routed,LeafOuterNative.References.input,
        ha.empty 1 (by decide),ha.empty 2 (by decide),ha.empty 3 (by decide),ha.empty 4 (by decide),
        ha.empty 5 (by decide),ha.empty 6 (by decide),ha.empty 7 (by decide),ha.empty 8 (by decide),
        ha.empty 320 (by decide)]
  obtain ⟨t,rf,ht,he⟩ := LeafOuterNative.References.command_eval d.regs (a.stacks 782)
  rw [←hd] at he
  let b := embedState referenceRegisters referenceStacks c
    (LeafOuterNative.References.output rf (CounterPrograms.value (a.stacks 782)))
  have hl := eval_liftCommand_from_state LeafOuterNative.References.command 0 7 referenceRegisters referenceStacks c
    (Fin.castAdd_injective 10 30) (by decide) he
  have hr := route_eval (782,0) (by unfold routeValid; decide) a ha.scratch
  refine ⟨routeCost (782,0) a+(t+1),b,by omega,hr.seq hl,?_⟩
  funext i
  by_cases hx : ∃ j, referenceStacks j=i
  · obtain ⟨j,rfl⟩ := hx
    rw [show b.stacks (referenceStacks j)=
      (LeafOuterNative.References.output rf (CounterPrograms.value (a.stacks 782))).stacks j from
        embedState_stack _ _ _ _ (by decide) j]
    fin_cases j <;> simp [referenceStacks,LeafOuterNative.References.output,
      ha.empty 0 (by decide),ha.empty 1 (by decide),ha.empty 2 (by decide),ha.empty 3 (by decide),
      ha.empty 4 (by decide),ha.empty 5 (by decide),ha.empty 6 (by decide),ha.empty 7 (by decide),ha.empty 8 (by decide)]
  · have h0 : i≠0 := by intro hi; apply hx; exact ⟨0,hi.symm⟩
    have h320 : i≠320 := by intro hi; apply hx; exact ⟨7,hi.symm⟩
    rw [show b.stacks i=c.stacks i from embedState_stack_frame _ _ _ _ i hx]
    simp [c,routed,h0,h320]

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter.references_eval_oai
