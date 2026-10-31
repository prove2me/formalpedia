-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:29:28.683186+00:00
-- url     : https://prove2.me/submissions/e2a96912-5f57-4b56-985d-a94cd98a435b

import Mathlib
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram_HeadGate_keyCall_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

theorem increment_eval {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (incrementCmd p) (rippleCost true (d.stacks p.counter) + 1)
      d (incrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram true) p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (ripple_local_trace true (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (incrementCmd p) _
    (install p d _ _ _ _ []) (incrementResult p d) at h
  rw [← hs, install_self] at h
  exact h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace KeyEquality

open OAI.Algorithms.SubexponentialSAT.SubexpRecordScan

theorem command_eval (regs : Fin 5 → Bool) (left right frame : List Bool) :
    ∃ n ≤ 18 * left.length + 9 * right.length + 25, ∃ out,
      Eval command n (recordState regs left [] right [] [] frame)
        (recordState out left [] right [] [] frame) ∧
      out 4 = decide (left = right) := by
  let r₁ := readRegs regs 0 1 none
  let r₂ := readRegs r₁ 0 1 none
  have h₁ : Eval (.call (StackRoutines.copyProgram 0 1 4 (0 : Fin 5) 1))
      (7 * left.length + 5)
      (recordState regs left [] right [] [] frame)
      (recordState r₁ left left right [] [] frame) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, storage, r₁] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.copy_eval (recordState regs left [] right [] [] frame)
        0 1 4 (by decide) (by decide) (by decide) rfl
  have h₂ : Eval (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (7 * right.length + 5)
      (recordState r₁ left left right [] [] frame)
      (recordState r₂ left left right right [] frame) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, storage, r₂] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.copy_eval (recordState r₁ left left right [] [] frame)
        2 3 4 (by decide) (by decide) (by decide) rfl
  obtain ⟨nc, hnc, rc, left', right', hc, hanswer, hl, hr⟩ :=
    compareKeys_eval r₂ left left right right [] frame
  let r₃ := readRegs rc 0 1 none
  let r₄ := readRegs r₃ 0 1 none
  have h₃ : Eval (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
      (2 * left'.length + 3)
      (recordState rc left left' right right' [] frame)
      (recordState r₃ left [] right right' [] frame) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, storage, r₃] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.clear_eval (recordState rc left left' right right' [] frame) 1
  have h₄ : Eval (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1))
      (2 * right'.length + 3)
      (recordState r₃ left [] right right' [] frame)
      (recordState r₄ left [] right [] [] frame) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, storage, r₄] using
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.clear_eval (recordState r₃ left [] right right' [] frame) 3
  refine ⟨_, by omega, r₄, h₁.seq (h₂.seq (hc.seq (h₃.seq h₄))), ?_⟩
  first | (simpa [r₄, r₃, readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hanswer) | (simpa [r₄, r₃, readRegs] using hanswer)

end KeyEquality

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The Boolean part of a local squarefree head weight, executed by a fixed
parallel scan of the assignment, support mask, and head mask. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram

open SubexponentialSAT BitProgram StructuredCalls

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem popAssignment_eval (r : Fin 8 → Bool) (a s h : List Bool) :
    StructuredProgram.Eval popAssignment 1 (data r a s h) (ready r a s h) := by
  have he := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 0 0 3) (data r a s h)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply state_ext
  · rfl
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))

private theorem body_eval (r : Fin 8 → Bool) (a s h : Bool) (as ss hs : List Bool) :
    ∃ rf, StructuredProgram.Eval body 7
      (ready r (a::as) (s::ss) (h::hs)) (ready rf as ss hs) ∧
      rf 6 = (r 6 && (!(s && h) || a)) := by
  let d0 := ready r (a::as) (s::ss) (h::hs)
  let d1 := (StructuredProgram.Atom.pop 1 1 4).eval d0
  let d2 := (StructuredProgram.Atom.pop 2 2 5).eval d1
  let d3 := (StructuredProgram.Atom.band 7 1 2).eval d2
  let d4 := (StructuredProgram.Atom.bnot 7 7).eval d3
  let d5 := (StructuredProgram.Atom.bor 7 7 0).eval d4
  let d6 := (StructuredProgram.Atom.band 6 6 7).eval d5
  have hd : d6 = data d6.regs as ss hs := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [d0,d1,d2,d3,d4,d5,d6,ready,data,tapes,
        StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
        StructuredProgram.State.ofCfg]
  have hp := popAssignment_eval d6.regs as ss hs
  rw [←hd] at hp
  refine ⟨d6.regs, ?_, ?_⟩
  · exact StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 1 1 4) d0)
      (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 2 2 5) d1)
        (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.band 7 1 2) d2)
          (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.bnot 7 7) d3)
            (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.bor 7 7 0) d4)
              (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.band 6 6 7) d5) hp)))))
  · simp [d0,d1,d2,d3,d4,d5,d6,ready,data,tapes,readRegs,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
      StructuredProgram.State.ofCfg]

private theorem loop_eval (r : Fin 8 → Bool) (a s h : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, StructuredProgram.Eval loop (8*a.length+1) (ready r a s h) (data rf [] [] []) ∧
      rf 6 = (r 6 && good a s h) := by
  induction a generalizing r s h with
  | nil =>
    have hs : s=[] := List.length_eq_zero_iff.mp has.symm
    have hh : h=[] := List.length_eq_zero_iff.mp hah.symm
    subst s; subst h
    refine ⟨readRegs r 0 3 none, ?_, ?_⟩
    · exact StructuredProgram.Eval.while_false (by simp [ready,data,readRegs])
    · simp [readRegs,good]
  | cons a as ih =>
    cases s with
    | nil => simp at has
    | cons s ss =>
      cases h with
      | nil => simp at hah
      | cons h hs =>
        obtain ⟨rb,eb,hb⟩ := body_eval r a s h as ss hs
        obtain ⟨rf,ef,hf⟩ := ih rb ss hs (by simpa using has) (by simpa using hah)
        refine ⟨rf, ?_, ?_⟩
        · have he := StructuredProgram.Eval.while_true
            (by simp [ready,data,readRegs] : (ready r (a::as) (s::ss) (h::hs)).regs 3 = true)
            eb ef
          convert he using 1 ; simp [] ; omega
        · rw [hf,hb]
          simp [good,Bool.and_assoc]

/-- Exact scan execution. All three work tapes are consumed and register6 is
true precisely when every selected assignment bit is true. -/
theorem command_eval (r : Fin 8 → Bool) (a s h : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Eval command (8*a.length+3) (data r a s h) (data rf [] [] []) ∧
      rf 6 = good a s h := by
  let r0 := Function.update r 6 true
  have e0 : StructuredProgram.Eval (.atom (.set 6 true)) 1
      (data r a s h) (data r0 a s h) := StructuredProgram.Eval.atom _ _
  have ep := popAssignment_eval r0 a s h
  obtain ⟨rf,ef,hf⟩ := loop_eval r0 a s h has hah
  refine ⟨rf, ?_, ?_⟩
  · convert Eval.base (e0.seq (ep.seq ef)) using 1 ; omega
  · simpa [r0] using hf

theorem program_trace (r : Fin 8 → Bool) (a s h : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Trace program (8*a.length+4)
      ((data r a s h).withPC (some program.entry))
      ((data rf [] [] []).withPC none) ∧ rf 6 = good a s h := by
  obtain ⟨rf,he,hf⟩ := command_eval r a s h has hah
  exact ⟨rf, by simpa [Nat.add_assoc] using compiled_halt_trace he 0 0, hf⟩

end SubexponentialSAT.SqrtLog.LeafWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving physical wrapper for the Boolean head-weight scan. The actual
ring zero and one are arbitrary runtime words, so the ring degree is dynamic. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem stackMap_injective : Function.Injective stackMap := by decide

private theorem embedKernel (r old : Fin 8 → Bool)
    (a s h zero one x y z oldX oldY oldZ out : List Bool) :
    embedState id stackMap (data old a s h zero one oldX oldY oldZ out)
      (LeafWeightProgram.data r x y z) = data r a s h zero one x y z out := by
  apply embedState_eq_of_ports id stackMap _ _ _ Function.injective_id stackMap_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h5 : i ≠ 5 := by
      intro e
      apply hi
      exact ⟨0, by simpa [stackMap] using e.symm⟩
    have h6 : i ≠ 6 := by
      intro e
      apply hi
      exact ⟨1, by simpa [stackMap] using e.symm⟩
    have h7 : i ≠ 7 := by
      intro e
      apply hi
      exact ⟨2, by simpa [stackMap] using e.symm⟩
    have hs : tapes a s h zero one x y z out =
        Function.update (Function.update (Function.update
          (tapes a s h zero one oldX oldY oldZ out) 5 x) 6 y) 7 z := by
      rw [update5,update6,update7]
    change tapes a s h zero one x y z out i =
      tapes a s h zero one oldX oldY oldZ out i
    rw [hs]
    rw [Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5]

theorem scan_eval (r : Fin 8 → Bool) (a s h zero one out : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Eval scan (8*a.length+4) (data r a s h zero one a s h out)
      (data rf a s h zero one [] [] [] out) ∧ rf 6 = good a s h := by
  obtain ⟨rf,he,hv⟩ := LeafWeightProgram.program_trace r a s h has hah
  have hx := eval_call_lifted LeafWeightProgram.program id stackMap
    (data r a s h zero one a s h out) Function.injective_id stackMap_injective he
  rw [embedKernel,embedKernel] at hx
  exact ⟨rf,hx,hv⟩

end SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.CorrectionGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafWeightProgram.Native

private theorem copy_eval (src dst : Fin 10) (hsd : src ≠ dst)
    (hst : src ≠ 8) (htd : (8 : Fin 10) ≠ dst)
    (r : Fin 8 → Bool) (stk : Fin 10 → List Bool) (ht : stk 8 = []) :
    Eval (copy src dst) (7*(stk src).length+5) ⟨r,stk⟩
      ⟨readRegs r 0 3 none,copyStacks src dst stk⟩ := by
  apply Eval.call
  have he := halt_after_trace _
    (copyProgram_trace src dst 8 (0 : Fin 8) 3 hsd hst htd (by decide) r stk ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC,copyResult,copyProgram,Nat.add_assoc] using he

/-- An actual preserving Boolean correction test. Its result is a Boolean
register, so the following conditional does not inspect a coefficient low bit. -/
theorem command_eval (r : Fin 8 → Bool) (a E H : List Bool)
    (haE : a.length=E.length) (haH : a.length=H.length) :
    ∃ rf, Eval command (29*a.length+19) (data r a E H [] [] [] [] [] [])
      (data rf a E H [] [] [] [] [] []) ∧ rf 6=LeafWeightProgram.good a E H := by
  have e1 := copy_eval 0 5 (by decide) (by decide) (by decide) r
    (tapes a E H [] [] [] [] [] []) rfl
  change Eval (copy 0 5) (7*a.length+5)
    (data r a E H [] [] [] [] [] [])
    ⟨readRegs r 0 3 none,Function.update (tapes a E H [] [] [] [] [] []) 5 (a++[])⟩ at e1
  rw [List.append_nil,update5] at e1
  let r1 := readRegs r 0 3 none
  have e2 := copy_eval 1 6 (by decide) (by decide) (by decide) r1
    (tapes a E H [] [] a [] [] []) rfl
  change Eval (copy 1 6) (7*E.length+5)
    (data r1 a E H [] [] a [] [] [])
    ⟨readRegs r1 0 3 none,Function.update (tapes a E H [] [] a [] [] []) 6 (E++[])⟩ at e2
  rw [List.append_nil,update6] at e2
  let r2 := readRegs r1 0 3 none
  have e3 := copy_eval 2 7 (by decide) (by decide) (by decide) r2
    (tapes a E H [] [] a E [] []) rfl
  change Eval (copy 2 7) (7*H.length+5)
    (data r2 a E H [] [] a E [] [])
    ⟨readRegs r2 0 3 none,Function.update (tapes a E H [] [] a E [] []) 7 (H++[])⟩ at e3
  rw [List.append_nil,update7] at e3
  obtain ⟨rf,es,hs⟩ := scan_eval (readRegs r2 0 3 none) a E H [] [] [] haE haH
  refine ⟨rf,?_,hs⟩
  have he := e1.seq (e2.seq (e3.seq es))
  convert he using 1
  · rfl
  · omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.CorrectionGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem equalityCall_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool) :
    ∃ n ≤ 18*key.length+9*wanted.length+26, ∃ out,
      Eval equalityCall n (state regs W bits rows key wanted E H)
        (state out W bits rows key wanted E H) ∧ out 4=decide (key=wanted) := by
  let a := state regs W bits rows key wanted E H
  have hr : Function.Injective equalityRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective equalityStacks := by decide
  have hp : projectState equalityRegisters equalityStacks a =
      OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ equalityRegisters) key [] wanted [] [] [] := by
    apply congrArg (StructuredProgram.State.mk _)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨n,hn,out,he,hanswer⟩ :=
    AttainedSignatureProgram.KeyEquality.command_eval (regs ∘ equalityRegisters) key wanted []
  rw [←hp] at he
  have hc := eval_call_from_state AttainedSignatureProgram.KeyEquality.program
    equalityRegisters equalityStacks a hr hs (compiled_halt_trace he 0 0)
  let e := embedState equalityRegisters equalityStacks a
    (OAI.Algorithms.SubexponentialSAT.SubexpRecordScan.recordState out key [] wanted [] [] [])
  have heq : e = state e.regs W bits rows key wanted E H := by
    apply embedState_eq_of_ports equalityRegisters equalityStacks a _ _ hr hs
    · intro i; exact embedState_register equalityRegisters equalityStacks a _ hr i
    · intro i hi; exact embedState_register_frame equalityRegisters equalityStacks a _ i hi
    · intro i; fin_cases i <;> rfl
    · intro i _; rfl
  have ha : e.regs 4=decide (key=wanted) := by
    change e.regs (equalityRegisters 4)=_
    rw [embedState_register equalityRegisters equalityStacks a _ hr]
    exact hanswer
  change Eval equalityCall (n+1) a e at hc
  rw [heq] at hc
  exact ⟨n+1,by omega,e.regs,hc,ha⟩

theorem correctionCall_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool)
    (hE : bits.length=E.length) (hH : bits.length=H.length) :
    ∃ out, Eval correctionCall (29*bits.length+20)
      (state regs W bits rows key wanted E H) (state out W bits rows key wanted E H) ∧
      out 6=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good bits E H ∧ out 15=regs 15 := by
  let a := state regs W bits rows key wanted E H
  have hr : Function.Injective keyRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective correctionStacks := by decide
  have hp : projectState keyRegisters correctionStacks a =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.Native.data (regs ∘ keyRegisters)
        bits E H [] [] [] [] [] [] := by
    apply congrArg (StructuredProgram.State.mk _)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨out,he,hanswer⟩ := CorrectionGate.command_eval (regs ∘ keyRegisters) bits E H hE hH
  rw [←hp] at he
  have hc := eval_call_from_state CorrectionGate.program keyRegisters correctionStacks a hr hs
    (compiled_halt_trace he 0 0)
  let e := embedState keyRegisters correctionStacks a
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.Native.data out bits E H [] [] [] [] [] [])
  have heq : e = state e.regs W bits rows key wanted E H := by
    apply embedState_eq_of_ports keyRegisters correctionStacks a _ _ hr hs
    · intro i; exact embedState_register keyRegisters correctionStacks a _ hr i
    · intro i hi; exact embedState_register_frame keyRegisters correctionStacks a _ i hi
    · intro i; fin_cases i <;> rfl
    · intro i _; rfl
  have ha : e.regs 6=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good bits E H := by
    change e.regs (keyRegisters 6)=_
    rw [embedState_register keyRegisters correctionStacks a _ hr]
    exact hanswer
  have hf : e.regs 15=regs 15 := by
    exact embedState_register_frame keyRegisters correctionStacks a _ 15 (by
      rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      simp [keyRegisters] at hv
      omega)
  change Eval correctionCall (29*bits.length+19+1) a e at hc
  rw [heq] at hc
  exact ⟨e.regs,by simpa [Nat.add_assoc] using hc,ha,hf⟩

theorem command_eval (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (wanted E H : List Bool)
    (hlen : ∀ row ∈ rows, row.length=bits.length)
    (hE : bits.length=E.length) (hH : bits.length=H.length) :
    ∃ n ≤ budget W bits rows wanted, ∃ out,
      Eval command n (state regs W bits rows [] wanted E H)
        (state out W bits rows [] wanted E H) ∧
      out 15=(decide (signatureValue W bits rows=wanted) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good bits E H) := by
  obtain ⟨nk,hnk,rk,hk⟩ := keyCall_eval regs W bits rows [] wanted E H hlen
  simp only [List.append_nil] at hk
  obtain ⟨ne,hne,re,he,hanswer⟩ :=
    equalityCall_eval rk W bits rows (signatureValue W bits rows) wanted E H
  let rc := Function.update re 15 (re 4)
  have hcopy : Eval (.base (.atom (.copy 15 4))) 1
      (state re W bits rows (signatureValue W bits rows) wanted E H)
      (state rc W bits rows (signatureValue W bits rows) wanted E H) :=
    .base (.atom _ _)
  obtain ⟨rr,hr,hcorr,hframe⟩ :=
    correctionCall_eval rc W bits rows (signatureValue W bits rows) wanted E H hE hH
  let rb := Function.update rr 15 (rr 15 && rr 6)
  have hband : Eval (.base (.atom (.band 15 15 6))) 1
      (state rr W bits rows (signatureValue W bits rows) wanted E H)
      (state rb W bits rows (signatureValue W bits rows) wanted E H) :=
    .base (.atom _ _)
  let rf := readRegs rb 0 1 none
  have hclear : Eval clearKey (2*(signatureValue W bits rows).length+3)
      (state rb W bits rows (signatureValue W bits rows) wanted E H)
      (state rf W bits rows [] wanted E H) := by
    have hc : Eval clearKey _
        (state rb W bits rows (signatureValue W bits rows) wanted E H)
        ⟨rf,StackRoutines.clearStacks 14
          (state rb W bits rows (signatureValue W bits rows) wanted E H).stacks⟩ :=
      .call _ (ListRegisterProgram.clear_run 14 0 1 rb _)
    convert hc using 1
    · simp [state]
    · apply congrArg (StructuredProgram.State.mk rf)
      funext i; fin_cases i <;> simp [state,StackRoutines.clearStacks]
  refine ⟨_,?_,rf,hk.seq (he.seq (hcopy.seq (hr.seq (hband.seq hclear)))),?_⟩
  · dsimp [budget]
    omega
  · simp [rf,rb,rc,readRegs,hcorr,hframe,hanswer]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem copy_eval (d : Data) (src dst : Fin 896)
    (hsd : src≠dst) (hst : src≠31) (htd : (31:Fin 896)≠dst) (ht : d.stacks 31=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copyState d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

theorem clear_eval (d : Data) (src : Fin 896) :
    Eval (clear src) (2*(d.stacks src).length+3) d (clearState d src) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

theorem stage_eval (d : Data) (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[]) :
    Eval stage (7*sourceLength d+30) d (staged d) := by
  have h31 : d.stacks 31=[] := hclean 31
  let d1 := copyState d 864 0
  let d2 := copyState d1 859 12
  let d3 := copyState d2 865 15
  let d4 := copyState d3 866 16
  let d5 := copyState d4 867 17
  have h1 := copy_eval d 864 0 (by decide) (by decide) (by decide) h31
  have h2 := copy_eval d1 859 12 (by decide) (by decide) (by decide)
    (by simp [d1,copyState,copyStacks,h31])
  have h3 := copy_eval d2 865 15 (by decide) (by decide) (by decide)
    (by simp [d2,d1,copyState,copyStacks,h31])
  have h4 := copy_eval d3 866 16 (by decide) (by decide) (by decide)
    (by simp [d3,d2,d1,copyState,copyStacks,h31])
  have h5 := copy_eval d4 867 17 (by decide) (by decide) (by decide)
    (by simp [d4,d3,d2,d1,copyState,copyStacks,h31])
  have h6 := copy_eval d5 868 18 (by decide) (by decide) (by decide)
    (by simp [d5,d4,d3,d2,d1,copyState,copyStacks,h31])
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  · rfl
  · simp [sourceLength,d5,d4,d3,d2,d1,copyState,copyStacks]
    omega
  · rfl

theorem stage_project (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words)) :
    projectState registers stackMap (staged d) =
      HeadGate.state ((staged d).regs ∘ registers) (d.stacks 864) (d.stacks 859) rows []
        (d.stacks 866) (d.stacks 867) (d.stacks 868) := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  have hi := hclean i
  fin_cases i <;>
    simp_all [stackMap,staged,copyState,copyStacks]

theorem stage_high (d : Data) (i : Fin 896) (hi : 32 ≤ i.val) :
    (staged d).stacks i=d.stacks i := by
  have h0 : i≠0 := by intro h; subst i; omega
  have h12 : i≠12 := by intro h; subst i; omega
  have h15 : i≠15 := by intro h; subst i; omega
  have h16 : i≠16 := by intro h; subst i; omega
  have h17 : i≠17 := by intro h; subst i; omega
  have h18 : i≠18 := by intro h; subst i; omega
  simp [staged,copyState,copyStacks,h0,h12,h15,h16,h17,h18]

theorem cleanup_eval (d : Data) :
    Eval cleanup (2*lowLength d+18) d (cleaned d) := by
  let d1 := clearState d 0
  let d2 := clearState d1 12
  let d3 := clearState d2 15
  let d4 := clearState d3 16
  let d5 := clearState d4 17
  have h1 := clear_eval d 0
  have h2 := clear_eval d1 12
  have h3 := clear_eval d2 15
  have h4 := clear_eval d3 16
  have h5 := clear_eval d4 17
  have h6 := clear_eval d5 18
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  · rfl
  · simp [lowLength,d5,d4,d3,d2,d1,clearState,clearStacks]
    omega
  · rfl

theorem cleaned_staged (d : Data) (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[]) :
    (cleaned (staged d)).stacks=d.stacks := by
  funext i
  by_cases hi : i.val < 32
  · obtain ⟨j,rfl⟩ : ∃ j : Fin 32, stackMap j=i := ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
    have hh := hclean j
    fin_cases j <;>
      simp_all [stackMap,cleaned,clearState,clearStacks,staged,copyState,copyStacks]
  · have hh : 32 ≤ i.val := by omega
    have h0 : i≠0 := by intro h; subst i; omega
    have h12 : i≠12 := by intro h; subst i; omega
    have h15 : i≠15 := by intro h; subst i; omega
    have h16 : i≠16 := by intro h; subst i; omega
    have h17 : i≠17 := by intro h; subst i; omega
    have h18 : i≠18 := by intro h; subst i; omega
    simp only [cleaned,clearState,clearStacks,Function.update_of_ne h0,
      Function.update_of_ne h12,Function.update_of_ne h15,Function.update_of_ne h16,
      Function.update_of_ne h17,Function.update_of_ne h18]
    exact stage_high d i hh

theorem staged_lowLength (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words)) :
    lowLength (staged d)=sourceLength d := by
  have hp := stage_project d rows hclean hmatrix
  have h0 := congrArg (fun a => a.stacks (0:Fin 32)) hp
  have h12 := congrArg (fun a => a.stacks (12:Fin 32)) hp
  have h15 := congrArg (fun a => a.stacks (15:Fin 32)) hp
  have h16 := congrArg (fun a => a.stacks (16:Fin 32)) hp
  have h17 := congrArg (fun a => a.stacks (17:Fin 32)) hp
  have h18 := congrArg (fun a => a.stacks (18:Fin 32)) hp
  simp [projectState,stackMap,HeadGate.state] at h0 h12 h15 h16 h17 h18
  simp [lowLength,sourceLength,h0,h12,h15,h16,h17,h18,hmatrix]

theorem command_eval_frame (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length=(d.stacks 859).length)
    (hE : (d.stacks 859).length=(d.stacks 867).length)
    (hH : (d.stacks 859).length=(d.stacks 868).length) :
    ∃ n ≤ HeadGate.budget (d.stacks 864) (d.stacks 859) rows (d.stacks 866)+
      9*sourceLength d+49, ∃ out,
      Eval command n d ⟨out,d.stacks⟩ ∧
      out 15=(decide (signatureValue (d.stacks 864) (d.stacks 859) rows=d.stacks 866) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good (d.stacks 859) (d.stacks 867) (d.stacks 868)) ∧
      ∀ i : Fin 40, 16 ≤ i.val → out i=d.regs i := by
  have hp := stage_project d rows hclean hmatrix
  have hr : Function.Injective registers := Fin.castAdd_injective _ _
  have hs : Function.Injective stackMap := Fin.castAdd_injective _ _
  obtain ⟨n,hn,out,he,hv⟩ := HeadGate.command_eval ((staged d).regs ∘ registers)
    (d.stacks 864) (d.stacks 859) rows (d.stacks 866) (d.stacks 867) (d.stacks 868) hlen hE hH
  rw [←hp] at he
  have hc := eval_call_from_state HeadGate.program registers stackMap (staged d) hr hs
    (compiled_halt_trace he 12 12)
  let e := embedState registers stackMap (staged d)
    (HeadGate.state out (d.stacks 864) (d.stacks 859) rows []
      (d.stacks 866) (d.stacks 867) (d.stacks 868))
  have heq : e=⟨e.regs,(staged d).stacks⟩ := by
    apply embedState_eq_of_ports registers stackMap (staged d) _ _ hr hs
    · intro i; exact embedState_register registers stackMap (staged d) _ hr i
    · intro i hi; exact embedState_register_frame registers stackMap (staged d) _ i hi
    · intro i
      exact congrArg (fun a => a.stacks i) hp
    · intro i _; rfl
  have hstacks := congrArg (fun a : Data => a.stacks) heq
  change e.stacks=(staged d).stacks at hstacks
  have hflag : e.regs 15=out 15 :=
    embedState_register registers stackMap (staged d) _ hr 15
  change Eval callGate (n+1) (staged d) e at hc
  have hcleanup := cleanup_eval e
  have hlenE : lowLength e=sourceLength d := by
    simpa only [lowLength,hstacks] using staged_lowLength d rows hclean hmatrix
  rw [hlenE] at hcleanup
  have hfinal : (cleaned e).stacks=d.stacks := by
    have h := cleaned_staged d hclean
    simpa only [cleaned,clearState,clearStacks,hstacks] using h
  have hfinalFlag : (cleaned e).regs 15=out 15 := by
    simpa [cleaned,clearState,readRegs] using hflag
  have hframe : ∀ i : Fin 40, 16 ≤ i.val → (cleaned e).regs i=d.regs i := by
    intro i hi
    have h0 : i≠0 := by intro h; subst i; omega
    have h1 : i≠1 := by intro h; subst i; omega
    have hout : i ∉ Set.range registers := by
      rintro ⟨j,hj⟩
      have hjv := congrArg Fin.val hj
      simp only [registers,Fin.val_castAdd] at hjv
      omega
    have hh := embedState_register_frame registers stackMap (staged d)
      (HeadGate.state out (d.stacks 864) (d.stacks 859) rows []
        (d.stacks 866) (d.stacks 867) (d.stacks 868)) i hout
    change e.regs i=(staged d).regs i at hh
    simpa [cleaned,clearState,staged,copyState,readRegs,h0,h1] using hh
  have hall := (stage_eval d hclean).seq (hc.seq hcleanup)
  refine ⟨7*sourceLength d+30+(n+1+(2*sourceLength d+18)),
    by omega,(cleaned e).regs,?_,hfinalFlag.trans hv,hframe⟩
  convert hall using 1
  · rfl
  · exact congrArg (StructuredProgram.State.mk (cleaned e).regs) hfinal.symm

/-- The concrete leaf-ABI wrapper reads cursor859 and persistent metadata864..868,
clears its low scratch bank, and preserves every stack of the caller. -/
theorem command_eval (d : Data) (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, d.stacks (stackMap i)=[])
    (hmatrix : d.stacks 865=words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length=(d.stacks 859).length)
    (hE : (d.stacks 859).length=(d.stacks 867).length)
    (hH : (d.stacks 859).length=(d.stacks 868).length) :
    ∃ n ≤ HeadGate.budget (d.stacks 864) (d.stacks 859) rows (d.stacks 866)+
      9*sourceLength d+49, ∃ out,
      Eval command n d ⟨out,d.stacks⟩ ∧
      out 15=(decide (signatureValue (d.stacks 864) (d.stacks 859) rows=d.stacks 866) &&
        OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.good (d.stacks 859) (d.stacks 867) (d.stacks 868)) := by
  obtain ⟨n,hn,out,he,hv,_⟩ := command_eval_frame d rows hclean hmatrix hlen hE hH
  exact ⟨n,hn,out,he,hv⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

open HeadEvaluationProgram.StagedGate (copy copyState copy_eval clear clearState clear_eval)


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

/-- Compose the real gate, the selected branch, and the real ripple increment.
The branch contract is an internal composition rule; the final scan instantiates
it with the named assignment-factor and dense-add commands. -/
theorem body_eval_oai (accepted : Code) (a : Data) (rows : List (List (List Bool)))
    (C : ℕ) (P : Data → Prop)
    (hclean : ∀ i : Fin 32, a.stacks (HeadEvaluationProgram.StagedGate.stackMap i) = [])
    (hmatrix : a.stacks 865 = words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length = (a.stacks 859).length)
    (hE : (a.stacks 859).length = (a.stacks 867).length)
    (hH : (a.stacks 859).length = (a.stacks 868).length)
    (hs : a.stacks 861 = [])
    (haccepted : gateValue a rows = true → ∀ out : Fin 40 → Bool, out 15 = true →
      ∃ nb b, nb ≤ C ∧ Eval accepted nb ⟨out, a.stacks⟩ b ∧
        b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
        b.stacks 861 = [] ∧ P b)
    (hrejected : gateValue a rows = false → ∀ out : Fin 40 → Bool, P ⟨out, a.stacks⟩) :
    ∃ steps b, steps ≤ bodyBudget a rows C ∧
      Eval (body accepted) steps a (Counters.incrementResult cursorPorts b) ∧
      b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
      b.stacks 861 = [] ∧ P b := by
  obtain ⟨ng, hng, out, hg, hv⟩ := HeadEvaluationProgram.StagedGate.command_eval
    a rows hclean hmatrix hlen hE hH
  change out 15 = gateValue a rows at hv
  have hbranch : ∃ nb b, nb ≤ C ∧
      Eval (.ite 15 accepted (.base .skip)) (nb + 1) ⟨out, a.stacks⟩ b ∧
      b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
      b.stacks 861 = [] ∧ P b := by
    cases hh : out 15 with
    | false =>
        refine ⟨0, ⟨out, a.stacks⟩, Nat.zero_le C,
          .ite_false hh (.base (.skip _)), rfl, rfl, hs, ?_⟩
        exact hrejected (hv.symm.trans hh) out
    | true =>
        obtain ⟨nb, b, hb, he, hc, hf, hbs, hp⟩ := haccepted (hv.symm.trans hh) out hh
        exact ⟨nb, b, hb, .ite_true hh he, hc, hf, hbs, hp⟩
  obtain ⟨nb, b, hb, he, hc, hf, hbs, hp⟩ := hbranch
  have hi := Counters.increment_eval cursorPorts b hbs
  refine ⟨ng + (nb + 1 + (rippleCost true (b.stacks 859) + 1)), b, ?_,
    hg.seq (he.seq hi), hc, hf, hbs, hp⟩
  have hr := rippleCost_le true (b.stacks 859)
  rw [hc] at hr
  dsimp only [bodyBudget]
  rw [hc]
  omega

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval_oai
