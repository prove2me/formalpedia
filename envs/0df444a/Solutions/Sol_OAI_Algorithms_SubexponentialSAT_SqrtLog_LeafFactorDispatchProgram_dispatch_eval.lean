-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:52:30.658436+00:00
-- url     : https://prove2.me/submissions/649a6b26-873d-4ee1-9b31-60ef6df63161

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S107
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram_hashBranch_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram_markedBranch_eval

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

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid factor classification and source lookup. IDs are runtime data. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem clear_eval (d : Data) (src : Fin 16) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  have h := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have ht := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [clear,cleared,StackRoutines.clearProgram,StackRoutines.clearResult,
    StackRoutines.clearStacks,StructuredProgram.State.withPC,Nat.add_assoc] using ht

/-- The existing comparison only removes cells; this records its paid cleanup bound. -/
theorem less_trace (left right : List Bool) (regs : Fin 4 → Bool) :
    ∃ n rf l r, n ≤ 4*left.length+6 ∧
      Trace CodeSearchProgram.unaryLessProgram n
        (CodeSearchProgram.unaryLessCfg (some 0) regs left right)
        (CodeSearchProgram.unaryLessCfg none rf l r) ∧
      rf 3=decide (left.length < right.length) ∧ l.length ≤ left.length ∧ r.length ≤ right.length := by
  induction left generalizing right regs with
  | nil =>
    refine ⟨5,_,[],right,by simp,CodeSearchProgram.unaryLess_nil regs right,?_,by simp,le_rfl⟩
    cases right <;> simp
  | cons a left ih =>
    cases right with
    | nil =>
      refine ⟨6,_,left,[],by simp,CodeSearchProgram.unaryLess_right_nil regs a left,by simp,by simp,le_rfl⟩
    | cons b right =>
      obtain ⟨n,rf,l,r,hn,ht,hf,hl,hr⟩ :=
        ih right (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
      refine ⟨4+n,rf,l,r,?_,(CodeSearchProgram.unaryLess_round regs a b left right).trans ht,?_,?_,?_⟩
      · simp only [List.length_cons]; omega
      · simpa using hf
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega

theorem lessClean_eval (d : Data) :
    ∃ n e, n ≤ 6*(d.stacks 8).length+2*(d.stacks 9).length+12 ∧
      Eval lessClean n d e ∧ e.regs 3=decide ((d.stacks 8).length < (d.stacks 9).length) ∧
      e.stacks=Function.update (Function.update d.stacks 8 []) 9 [] ∧ Stable d e := by
  obtain ⟨n,rf,l,r,hn,ht,hf,hl,hr⟩ := less_trace (d.stacks 8) (d.stacks 9) (d.regs ∘ cmpRegs)
  have hir : Function.Injective cmpRegs := Fin.castAdd_injective _ _
  have hip : Function.Injective cmpPorts := by decide
  let a : State 4 2 := ⟨d.regs ∘ cmpRegs,![d.stacks 8,d.stacks 9]⟩
  let b : State 4 2 := ⟨rf,![l,r]⟩
  let c := embedState cmpRegs cmpPorts d b
  have ha : embedState cmpRegs cmpPorts d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ hir hip
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have he := eval_call_lifted CodeSearchProgram.unaryLessProgram cmpRegs cmpPorts d hir hip
    (a := a) (b := b) ht
  rw [ha] at he
  have hc8 : c.stacks 8=l := embedState_stack _ _ _ _ hip 0
  have hc9 : c.stacks 9=r := embedState_stack _ _ _ _ hip 1
  have hc3 : c.regs 3=rf 3 := embedState_register _ _ _ _ hir 3
  let e := cleared (cleared c 8) 9
  have heval := he.seq ((clear_eval c 8).seq (clear_eval (cleared c 8) 9))
  refine ⟨n+(2*l.length+3+(2*r.length+3)),e,by omega,?_,?_,?_,?_⟩
  · simpa [e, lessClean, compare, hc8, hc9, cleared] using heval
  · simpa [e,cleared,readRegs,hc3] using hf
  · funext i
    by_cases h8 : i=8
    · subst i; simp [e,cleared]
    by_cases h9 : i=9
    · subst i; simp [e,cleared]
    · have hframe : c.stacks i=d.stacks i := by
        apply embedState_stack_frame
        rintro ⟨j,hj⟩
        fin_cases j <;> simp_all [cmpPorts]
      simpa [e,cleared,h8,h9] using hframe
  · intro i hi
    have hi0 : i≠0 := by intro h; subst i; simp at hi
    have hi1 : i≠1 := by intro h; subst i; simp at hi
    have hframe : c.regs i=d.regs i := by
      apply embedState_register_frame
      rintro ⟨j,hj⟩
      have hh := congrArg Fin.val hj
      simp [cmpRegs] at hh
      omega
    simpa [e,cleared,readRegs,hi0,hi1] using hframe

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem bump_eval (d : Data) (extra : Bool) :
    Eval (bump extra) (if extra then 4 else 2) d (bumped d extra) := by
  have h := Subexp.TupleProgram.pushConst_eval (9 : Fin 16) (0 : Fin 8) true d
  cases extra with
  | false =>
    have he := h.seq (Eval.base (StructuredProgram.Eval.skip _))
    simpa [bump,bumped,Subexp.TupleProgram.pushedState] using he
  | true =>
    have he := h.seq (Subexp.TupleProgram.pushConst_eval (9 : Fin 16) (0 : Fin 8) true _)
    simpa [bump,bumped,Subexp.TupleProgram.pushedState,List.replicate_succ] using he

theorem test_eval (d : Data) (f h : ℕ) (extra : Bool)
    (hf : d.stacks 6=Encoding.encodeNat f) (hh : d.stacks 3=unary h)
    (h8 : d.stacks 8=[]) (h9 : d.stacks 9=[]) (h14 : d.stacks 14=[]) :
    ∃ n e, n ≤ 13*f+9*h+45 ∧ Eval (test extra) n d e ∧
      e.regs 3=decide (f < h+(if extra then 1 else 0)) ∧ e.stacks=d.stacks ∧ Stable d e := by
  let a := afterCopy d 6 8 0 1
  let b := afterCopy a 3 9 0 1
  let c := bumped b extra
  have h1 : Eval (copy 6 8) (7*(f+1)+5) d a := by
    simpa [copy,hf] using copy_eval d 6 8 14 0 1 (by decide) (by decide) (by decide) (by decide) h14
  have h2 : Eval (copy 3 9) (7*h+5) a b := by
    simpa [copy,b,a,afterCopy,StackRoutines.copyStacks,hh] using
      copy_eval a 3 9 14 0 1 (by decide) (by decide) (by decide) (by decide)
        (by simpa [a,afterCopy,StackRoutines.copyStacks] using h14)
  have h3 := bump_eval b extra
  have hc8 : (c.stacks 8).length=f+1 := by
    simp [c,b,a,bumped,afterCopy,StackRoutines.copyStacks,hf,h8]
  have hc9 : (c.stacks 9).length=h+(if extra then 2 else 1) := by
    simp [c,b,a,bumped,afterCopy,StackRoutines.copyStacks,hh,h9,Nat.add_comm]
  obtain ⟨n,e,hn,he,hflag,hes,her⟩ := lessClean_eval c
  refine ⟨7*(f+1)+5+(7*h+5+((if extra then 4 else 2)+n)),e,?_,
    h1.seq (h2.seq (h3.seq he)),?_,?_,?_⟩
  · rw [hc8,hc9] at hn
    cases extra <;> simp_all <;> omega
  · rw [hc8,hc9] at hflag
    convert hflag using 2 ; cases extra <;> simp
  · rw [hes]
    funext i
    fin_cases i <;> simp [c,b,a,bumped,afterCopy,StackRoutines.copyStacks,h8,h9]
  · intro i hi
    rw [her i hi]
    have hi0 : i≠0 := by intro he; subst i; simp at hi
    have hi1 : i≠1 := by intro he; subst i; simp at hi
    simp [c,b,a,bumped,afterCopy,readRegs,hi0,hi1]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem mark_eval (d : Data) (isHash isMarked : Bool) :
    Eval (mark isHash isMarked) 2 d (marked d isHash isMarked) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (5 : Fin 8) isHash) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (.set (6 : Fin 8) isMarked) _))
  simpa [mark,marked,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h

theorem neutralBranch_eval (d : Data) (f : ℕ)
    (hi : d.stacks 6=Encoding.encodeNat f) (hout : d.stacks 15=[]) :
    ∃ e, Eval neutralBranch (2*f+7) d e ∧ Finished d e false false [] := by
  refine ⟨marked (cleared d 6) false false,?_,?_⟩
  · simpa [neutralBranch,hi,Nat.mul_add,Nat.add_assoc] using
      (clear_eval d 6).seq (mark_eval (cleared d 6) false false)
  · simp [Finished,finishedStacks,marked,cleared,hout,readRegs]

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem Finished.rebase {d a e : Data} {isHash isMarked : Bool} {bits : List Bool}
    (hs : a.stacks=d.stacks) (hr : a.regs 7=d.regs 7) (h : Finished a e isHash isMarked bits) :
    Finished d e isHash isMarked bits := by
  rcases h with ⟨he,h5,h6,h7⟩
  exact ⟨by simpa [finishedStacks,hs] using he,h5,h6,h7.trans hr⟩

theorem dispatch_eval_oai (d : Data) (rows clauses : List (List Bool))
    (hasMarked : Bool) (m f : ℕ)
    (hrows : d.stacks 0=Encoding.encodeList id rows)
    (hclauses : d.stacks 1=Encoding.encodeList id clauses)
    (hcount : d.stacks 3=unary rows.length)
    (hmark : hasMarked=true → d.stacks 4=Encoding.encodeNat m)
    (hid : d.stacks 6=Encoding.encodeNat f)
    (hflag : d.regs 7=hasMarked)
    (hvalid : hasMarked=true → m < clauses.length)
    (hc : FetchClean d) (ht : TestClean d) :
    ∃ n e, n ≤ dispatchBound rows clauses m f ∧ Eval dispatch n d e ∧
      Finished d e (decide (f < rows.length)) (hasMarked && decide (f=rows.length))
        (selectedPayload rows clauses hasMarked m f) := by
  obtain ⟨n1,a,hn1,he1,ha3,has,har⟩ := test_eval d f rows.length false hid hcount ht.1 ht.2.1 ht.2.2
  have ha7 : a.regs 7=d.regs 7 := har 7 (by decide)
  have hac : FetchClean a := by simpa [FetchClean,has] using hc
  have hat : TestClean a := by simpa [TestClean,has] using ht
  by_cases hf : f < rows.length
  · have haf : a.regs 3=true := by simpa [hf] using ha3
    let i : Fin rows.length := ⟨f,hf⟩
    obtain ⟨nb,e,hnb,heb,hfin⟩ := hashBranch_eval a rows i
      (by simpa [has] using hrows) (by simpa [has,i] using hid) hac
    refine ⟨n1+(nb+1),e,?_,he1.seq (Eval.ite_true haf heb),?_⟩
    · unfold dispatchBound branchBound; omega
    · have hr := hfin.rebase has ha7
      have hne : f≠rows.length := by omega
      simpa [selectedPayload,hf,hne,i,List.getD_eq_getElem _ _ hf] using hr
  · have haf : a.regs 3=false := by simpa [hf] using ha3
    obtain ⟨n2,b,hn2,he2,hb3,hbs,hbr⟩ := test_eval a f rows.length true
      (by simpa [has] using hid) (by simpa [has] using hcount) hat.1 hat.2.1 hat.2.2
    have hbs' : b.stacks=d.stacks := hbs.trans has
    have hb7 : b.regs 7=d.regs 7 := (hbr 7 (by decide)).trans ha7
    have hbc : FetchClean b := by simpa [FetchClean,hbs'] using hc
    by_cases heq : f=rows.length
    · have hbf : b.regs 3=true := by simpa [heq] using hb3
      cases hm : hasMarked with
      | false =>
        have hbm : b.regs 7=false := hb7.trans (hflag.trans hm)
        obtain ⟨e,he,hfin⟩ := neutralBranch_eval b f (by simpa [hbs'] using hid)
          (by simpa [hbs'] using hc 15 (by decide))
        refine ⟨n1+((n2+((2*f+7+1)+1))+1),e,?_,
          he1.seq (Eval.ite_false haf (he2.seq (Eval.ite_true hbf (Eval.ite_false hbm he)))),?_⟩
        · unfold dispatchBound branchBound; omega
        · have hr := hfin.rebase hbs' hb7
          simpa [selectedPayload,hf,hm] using hr
      | true =>
        have hbm : b.regs 7=true := hb7.trans (hflag.trans hm)
        let i : Fin clauses.length := ⟨m,hvalid hm⟩
        obtain ⟨nb,e,hnb,heb,hfin⟩ := markedBranch_eval b clauses i f
          (by simpa [hbs'] using hclauses) (by simpa [hbs'] using hid)
          (by simpa [hbs',i] using hmark hm) hbc (by simpa [hbs'] using ht.2.2)
        refine ⟨n1+((n2+((nb+1)+1))+1),e,?_,
          he1.seq (Eval.ite_false haf (he2.seq (Eval.ite_true hbf (Eval.ite_true hbm heb)))),?_⟩
        · dsimp [i] at hnb; unfold dispatchBound branchBound; omega
        · have hr := hfin.rebase hbs' hb7
          simpa [selectedPayload,hf,hm,heq,i,List.getElem?_eq_getElem (hvalid hm)] using hr
    · have hnle : ¬f < rows.length+1 := by omega
      have hbf : b.regs 3=false := by simpa [hnle] using hb3
      obtain ⟨e,he,hfin⟩ := neutralBranch_eval b f (by simpa [hbs'] using hid)
        (by simpa [hbs'] using hc 15 (by decide))
      refine ⟨n1+((n2+(2*f+7+1))+1),e,?_,
        he1.seq (Eval.ite_false haf (he2.seq (Eval.ite_false hbf he))),?_⟩
      · unfold dispatchBound branchBound; omega
      · have hr := hfin.rebase hbs' hb7
        simpa [selectedPayload,hf,heq] using hr

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.dispatch_eval_oai
