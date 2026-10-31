-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:33:17.067838+00:00
-- url     : https://prove2.me/submissions/2283f143-bf87-4a70-89ad-5f29eb73d8ee

import Mathlib
import Definitions.Def_OAIQ081S162

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem popMask_eval (regs : Fin 4 → Bool) (mask high low out : List Bool) :
    Eval popMask 1 (state regs mask high low out) (popped regs mask high low out) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 4) 0 1)
    (state regs mask high low out))) using 1
  · rfl
  · apply congrArg (StructuredProgram.State.mk _)
    first | done | (funext i; fin_cases i <;> rfl)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestrictionTotal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Every correctly sized pair of branch streams is accepted by the actual
merge program, and the resulting original-coordinate assignment is unique. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem merge_spec (mask high low : List Bool)
    (hh : high.length = highCount mask)
    (hs : high.length + low.length = mask.length) :
    (merge mask high low).length = mask.length ∧
    selected true mask (merge mask high low) = high ∧
    selected false mask (merge mask high low) = low := by
  induction mask generalizing high low with
  | nil =>
      have hhigh : high = [] := List.eq_nil_of_length_eq_zero (by simpa [highCount, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful] using hh)
      have hlow : low = [] := List.eq_nil_of_length_eq_zero (by simpa [hhigh] using hs)
      simp [hhigh, hlow, merge, selected]
  | cons b mask ih =>
      cases b with
      | false =>
          have hh' : high.length = highCount mask := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          cases low with
          | nil =>
              have hb : highCount mask ≤ mask.length := by
                exact List.length_filter_le _ _
              simp only [List.length_nil, List.length_cons] at hs
              omega
          | cons x low =>
              have hs' : high.length + low.length = mask.length := by
                simp only [List.length_cons] at hs
                omega
              obtain ⟨hlen, hhigh, hlow⟩ := ih high low hh' hs'
              simp [merge, selected, hlen, hhigh, hlow]
      | true =>
          have hh' : high.length = highCount mask + 1 := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          cases high with
          | nil => simp at hh'
          | cons x high =>
              have hh'' : high.length = highCount mask := by simpa using hh'
              have hs' : high.length + low.length = mask.length := by
                simp only [List.length_cons] at hs
                omega
              obtain ⟨hlen, hhigh, hlow⟩ := ih high low hh'' hs'
              simp [merge, selected, hlen, hhigh, hlow]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original-coordinate high-value vector. The existing merger reads
false from its empty low stream, so no high-ID producer or zero-padding oracle
is required. It consumes the mask and high bits and emits the reversed vector. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem zero_iteration (regs : Fin 4 → Bool) (b x : Bool)
    (mask high out : List Bool) :
    ∃ rf, Eval body 4
      (popped regs (b :: mask) (if b then x :: high else high) [] out)
      (popped rf mask high [] ((if b then x else false) :: out)) := by
  let a := popped regs (b :: mask) (if b then x :: high else high) [] out
  let item : Option Bool := if b then some x else none
  let r := readRegs (readRegs regs 0 1 (some b)) 2 3 item
  refine ⟨r, ?_⟩
  have hp : Eval pushBit 1 (state r mask high [] out)
      (state r mask high [] ((if b then x else false) :: out)) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.push (3 : Fin 4) 2)
      (state r mask high [] out))) using 1
    · rfl
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    fin_cases i <;> cases b <;> simp [r, item, state, readRegs,
 StructuredProgram.Atom.instr,
 execInstr]
  have hl : Eval loadBit 2 a (state r mask high [] out) := by
    cases b with
    | false =>
        apply Eval.ite_false (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 4) 2 3) a)) using 1
        all_goals try with_reducible_and_instances rfl
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs, StructuredProgram.Atom.instr, execInstr]
    | true =>
        apply Eval.ite_true (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 4) 2 3) a)) using 1
        all_goals try with_reducible_and_instances rfl
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs, StructuredProgram.Atom.instr, execInstr]
  exact hl.seq (hp.seq (popMask_eval r mask high [] ((if b then x else false) :: out)))

theorem zero_loop_eval (regs : Fin 4 → Bool) (mask high out : List Bool)
    (hh : high.length = highCount mask) :
    ∃ rf, Eval loop (5 * mask.length + 1)
      (popped regs mask high [] out)
      (state rf [] [] [] ((zeroMerge mask high).reverse ++ out)) := by
  induction mask generalizing regs high out with
  | nil =>
      have hhigh : high = [] := List.eq_nil_of_length_eq_zero (by
        simpa [highCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful] using hh)
      subst high
      exact ⟨readRegs regs 0 1 none, Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases b with
      | false =>
          have hh' : high.length = highCount mask := by
            simpa [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] using hh
          obtain ⟨ri, hi⟩ := zero_iteration regs false false mask high out
          obtain ⟨rf, hr⟩ := ih ri high (false :: out) hh'
          refine ⟨rf, ?_⟩
          have h := Eval.while_true (show (popped regs (false :: mask) high [] out).regs 1 = true by rfl) hi hr
          convert h using 1 <;> simp only [loop, zeroMerge, merge, List.length_cons,
            List.headD_nil, List.tail_nil, List.reverse_cons, List.append_assoc,
            List.singleton_append, Nat.mul_add, Nat.mul_one,
            Nat.add_comm, Nat.add_left_comm] ; omega
      | true =>
          cases high with
          | nil => simp [highCount, Subexp.PaddedCompletion.trueCount,
              Subexp.PaddedCompletion.successful] at hh
          | cons x high =>
              have hh' : high.length = highCount mask := by
                simpa [highCount, Subexp.PaddedCompletion.trueCount,
                  Subexp.PaddedCompletion.successful] using hh
              obtain ⟨ri, hi⟩ := zero_iteration regs true x mask high out
              obtain ⟨rf, hr⟩ := ih ri high (x :: out) hh'
              refine ⟨rf, ?_⟩
              have h := Eval.while_true (show (popped regs (true :: mask) (x :: high) [] out).regs 1 = true by rfl) hi hr
              convert h using 1 <;> simp only [loop, zeroMerge, merge, List.length_cons,
                List.headD_cons, List.tail_cons, List.reverse_cons, List.append_assoc,
                List.singleton_append, Nat.mul_add, Nat.mul_one,
                Nat.add_comm, Nat.add_left_comm] ; omega

theorem merge_zero_pad (mask high : List Bool) (l : ℕ) :
    merge mask high (List.replicate l false) = zeroMerge mask high := by
  induction mask generalizing high l with
  | nil => rfl
  | cons b mask ih =>
      cases b
      · cases l <;> simp [zeroMerge, merge, ih, List.replicate_succ]
      · simp [zeroMerge, merge, ih]

/-- The emitted vector has exactly the supplied high bits and zero on every
free coordinate. It retains the full original length. -/
theorem zeroMerge_spec (mask high : List Bool) (hh : high.length = highCount mask) :
    (zeroMerge mask high).length = mask.length ∧
    selected true mask (zeroMerge mask high) = high ∧
    selected false mask (zeroMerge mask high) =
      List.replicate (mask.length - highCount mask) false := by
  have hc : highCount mask ≤ mask.length := List.length_filter_le _ _
  have hs : high.length + (List.replicate (mask.length - highCount mask) false).length =
      mask.length := by simp only [List.length_replicate]; omega
  have h := merge_spec mask high (List.replicate (mask.length - highCount mask) false) hh hs
  simpa only [merge_zero_pad] using h

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical scan merges a current-head assignment with the bucket
representative, keeping the original ambient coordinate order. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem popAssignment_eval (r : Fin 8 → Bool) (a h b out tmp : List Bool) :
    StructuredProgram.Eval popAssignment 1 (data r a h b out tmp) (ready r a h b out tmp) := by
  have he := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 0 0 3) (data r a h b out tmp)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply state_ext
  · rfl
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))

private theorem body_eval (r : Fin 8 → Bool) (a h b : Bool)
    (as hs bs out tmp : List Bool) :
    ∃ rf, StructuredProgram.Eval body 5
      (ready r (a::as) (h::hs) (b::bs) out tmp)
      (ready rf as hs bs out ((if h then a else b)::tmp)) := by
  let d0 := ready r (a::as) (h::hs) (b::bs) out tmp
  let d1 := (StructuredProgram.Atom.pop 1 1 4).eval d0
  let d2 := (StructuredProgram.Atom.pop 2 2 5).eval d1
  let d3 := data d2.regs as hs bs out ((if h then a else b)::tmp)
  have ep : StructuredProgram.Eval put 2 d2 d3 := by
    cases h
    · apply StructuredProgram.Eval.ite_false
      · simp [d0,d1,d2,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
          ]
      · convert StructuredProgram.Eval.atom (StructuredProgram.Atom.push 4 2) d2 using 1
        all_goals try with_reducible_and_instances rfl
        apply state_ext
        · rfl
        · funext i; fin_cases i <;>
            simp [d0,d1,d2,d3,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
              StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
              ]
    · apply StructuredProgram.Eval.ite_true
      · simp [d0,d1,d2,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
          ]
      · convert StructuredProgram.Eval.atom (StructuredProgram.Atom.push 4 0) d2 using 1
        all_goals try with_reducible_and_instances rfl
        apply state_ext
        · rfl
        · funext i; fin_cases i <;>
            simp [d0,d1,d2,d3,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
              StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
              ]
  have ex := popAssignment_eval d2.regs as hs bs out ((if h then a else b)::tmp)
  exact ⟨d2.regs, (StructuredProgram.Eval.atom (.pop 1 1 4) d0).seq
    ((StructuredProgram.Eval.atom (.pop 2 2 5) d1).seq (ep.seq ex))⟩

private theorem loop_eval (r : Fin 8 → Bool) (a h b out tmp : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, StructuredProgram.Eval loop (6*a.length+1) (ready r a h b out tmp)
      (data rf [] [] [] out ((merge a h b).reverse++tmp)) := by
  induction a generalizing r h b tmp with
  | nil =>
    have hh : h=[] := List.length_eq_zero_iff.mp hah.symm
    have hb : b=[] := List.length_eq_zero_iff.mp hab.symm
    subst h; subst b
    exact ⟨readRegs r 0 3 none, StructuredProgram.Eval.while_false
      (by simp [ready,data,readRegs])⟩
  | cons a as ih =>
    cases h with
    | nil => simp at hah
    | cons h hs =>
      cases b with
      | nil => simp at hab
      | cons b bs =>
        obtain ⟨rb,eb⟩ := body_eval r a h b as hs bs out tmp
        obtain ⟨rf,ef⟩ := ih rb hs bs ((if h then a else b)::tmp)
          (by simpa using hah) (by simpa using hab)
        have he := StructuredProgram.Eval.while_true
          (by simp [ready,data,readRegs] : (ready r (a::as) (h::hs) (b::bs) out tmp).regs 3=true)
          eb ef
        refine ⟨rf, ?_⟩
        convert he using 1 <;> simp [merge,List.reverse_cons,List.append_assoc] ; omega

/-- All work inputs are consumed; the forward-order result appears on stack3. -/
theorem command_eval (r : Fin 8 → Bool) (a h b : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Eval command (9*a.length+5) (data r a h b [] [])
      (data rf [] [] [] (merge a h b) []) := by
  obtain ⟨rs,es⟩ := loop_eval r a h b [] [] hah hab
  have ep := popAssignment_eval r a h b [] []
  have esc : Eval (.base scan) (6*a.length+2) (data r a h b [] [])
      (data rs [] [] [] [] (merge a h b).reverse) := by
    have hn : 1 + (6*a.length+1) = 6*a.length+2 := by omega
    simpa only [hn,List.append_nil] using Eval.base (ep.seq es)
  have et := halt_after_trace _
    (transferProgram_trace (4 : Fin 5) 3 (0 : Fin 8) 3 (by decide) (by decide)
      rs (tapes [] [] [] [] (merge a h b).reverse)) 3 rfl rfl
  have hst : transferStacks (4 : Fin 5) 3 (tapes [] [] [] [] (merge a h b).reverse) =
      tapes [] [] [] (merge a h b) [] := by
    funext i
    fin_cases i <;> simp [transferStacks,tapes]
  have eh : Eval (.call (transferProgram 4 3 0 3)) (3*a.length+3)
      (data rs [] [] [] [] (merge a h b).reverse)
      (data (readRegs rs 0 3 none) [] [] [] (merge a h b) []) := by
    apply Eval.call
    dsimp only [transferResult] at et
    rw [hst] at et
    simpa [data,StructuredProgram.State.withPC,transferProgram,tapes,Nat.add_assoc] using et
  exact ⟨readRegs rs 0 3 none, by convert esc.seq eh using 1 ; omega⟩

theorem program_trace (r : Fin 8 → Bool) (a h b : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Trace program (9*a.length+6)
      ((data r a h b [] []).withPC (some program.entry))
      ((data rf [] [] [] (merge a h b) []).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval r a h b hah hab
  exact ⟨rf, by simpa [Nat.add_assoc] using compiled_halt_trace he 0 3⟩

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving shell for the assignment merge. Only output9 and registers
change; the masters and both reserved words are preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

private theorem copy_eval (src dst : Fin 10) (hsd : src ≠ dst)
    (hst : src ≠ 8) (htd : (8 : Fin 10) ≠ dst)
    (r : Fin 8 → Bool) (stk : Fin 10 → List Bool) (ht : stk 8 = []) :
    Eval (copy src dst) (7*(stk src).length+5) ⟨r,stk⟩
      ⟨readRegs r 0 3 none,copyStacks src dst stk⟩ := by
  apply Eval.call
  have he := halt_after_trace _
    (copyProgram_trace src dst 8 (0 : Fin 8) 3 hsd hst htd (by decide) r stk ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC,copyResult,copyProgram,Nat.add_assoc] using he

theorem stackMap_injective : Function.Injective stackMap := by decide

private theorem embedKernel (r old : Fin 8 → Bool)
    (a h b u v x y z oldX oldY oldZ out oldOut : List Bool) :
    embedState id stackMap (data old a h b u v oldX oldY oldZ oldOut)
      (LeafAssignmentMergeProgram.data r x y z out []) = data r a h b u v x y z out := by
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
    have h9 : i ≠ 9 := by
      intro e
      apply hi
      exact ⟨3, by simpa [stackMap] using e.symm⟩
    have hs : tapes a h b u v x y z out =
        Function.update (Function.update (Function.update (Function.update
          (tapes a h b u v oldX oldY oldZ oldOut) 5 x) 6 y) 7 z) 9 out := by
      rw [LeafWeightProgram.Native.update5,LeafWeightProgram.Native.update6,
        LeafWeightProgram.Native.update7,LeafWeightProgram.Native.update9]
    change tapes a h b u v x y z out i =
      tapes a h b u v oldX oldY oldZ oldOut i
    rw [hs]
    rw [Function.update_of_ne h9,Function.update_of_ne h7,
      Function.update_of_ne h6,Function.update_of_ne h5]

theorem scan_eval (r : Fin 8 → Bool) (a h b u v : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Eval scan (9*a.length+6) (data r a h b u v a h b [])
      (data rf a h b u v [] [] [] (merge a h b)) := by
  obtain ⟨rf,he⟩ := LeafAssignmentMergeProgram.program_trace r a h b hah hab
  have hx := eval_call_lifted LeafAssignmentMergeProgram.program id stackMap
    (data r a h b u v a h b []) Function.injective_id stackMap_injective he
  rw [embedKernel,embedKernel] at hx
  exact ⟨rf,hx⟩

/-- Local3 and4 are arbitrary preserved words, so this helper can share the
weight helper's ABI without overwriting the cached ring constants. -/
theorem command_eval (r : Fin 8 → Bool) (a h b u v : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Eval command (30*a.length+21) (data r a h b u v [] [] [] [])
      (data rf a h b u v [] [] [] (merge a h b)) := by
  have e1 := copy_eval 0 5 (by decide) (by decide) (by decide) r
    (tapes a h b u v [] [] [] []) rfl
  change Eval (copy 0 5) (7*a.length+5)
    (data r a h b u v [] [] [] [])
    ⟨readRegs r 0 3 none,Function.update (tapes a h b u v [] [] [] []) 5 (a++[])⟩ at e1
  rw [List.append_nil,LeafWeightProgram.Native.update5] at e1
  let r1 := readRegs r 0 3 none
  have e2 := copy_eval 1 6 (by decide) (by decide) (by decide) r1
    (tapes a h b u v a [] [] []) rfl
  change Eval (copy 1 6) (7*h.length+5)
    (data r1 a h b u v a [] [] [])
    ⟨readRegs r1 0 3 none,Function.update (tapes a h b u v a [] [] []) 6 (h++[])⟩ at e2
  rw [List.append_nil,LeafWeightProgram.Native.update6] at e2
  let r2 := readRegs r1 0 3 none
  have e3 := copy_eval 2 7 (by decide) (by decide) (by decide) r2
    (tapes a h b u v a h [] []) rfl
  change Eval (copy 2 7) (7*b.length+5)
    (data r2 a h b u v a h [] [])
    ⟨readRegs r2 0 3 none,Function.update (tapes a h b u v a h [] []) 7 (b++[])⟩ at e3
  rw [List.append_nil,LeafWeightProgram.Native.update7] at e3
  obtain ⟨rf,ef⟩ := scan_eval (readRegs r2 0 3 none) a h b u v hah hab
  refine ⟨rf, ?_⟩
  have he := e1.seq (e2.seq (e3.seq ef))
  convert he using 1 ; omega

theorem program_trace (r : Fin 8 → Bool) (a h b u v : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Trace program (30*a.length+22)
      ((data r a h b u v [] [] [] []).withPC (some program.entry))
      ((data rf a h b u v [] [] [] (merge a h b)).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval r a h b u v hah hab
  exact ⟨rf, by simpa [program, Nat.add_assoc] using compiled_halt_trace he 0 9⟩

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

private theorem copy_eval (src dst : Fin 12) (hsd : src ≠ dst)
    (hst : src ≠ 8) (htd : (8 : Fin 12) ≠ dst)
    (a : Data) (ht : a.stacks 8 = []) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a
      ⟨readRegs a.regs 0 1 none,copyStacks src dst a.stacks⟩ := by
  exact .call _ (ListRegisterProgram.copy_run src dst 8 0 1 hsd hst htd (by decide)
    a.regs a.stacks ht)

private theorem expand_frame (bits mask baseline u v out : List Bool)
    (i : Fin 12) (hi : ¬∃ j, expandStacks j=i) :
    (![bits,mask,baseline,u,v,[],[],out,[],[],[],[]] : Fin 12 → List Bool) i =
      ![bits,mask,baseline,u,v,bits,mask,[],[],[],[],[]] i := by
  have h5 : i≠5 := by intro h; exact hi ⟨1,h.symm⟩
  have h6 : i≠6 := by intro h; exact hi ⟨0,h.symm⟩
  have h7 : i≠7 := by intro h; exact hi ⟨3,h.symm⟩
  fin_cases i <;> simp_all

private theorem merge_frame (bits mask baseline u v full out : List Bool)
    (i : Fin 12) (hi : ¬∃ j, mergeStacks j=i) :
    (![bits,mask,baseline,u,v,[],[],[],[],full,out,[]] : Fin 12 → List Bool) i =
      ![bits,mask,baseline,u,v,[],[],[],[],full,[],[]] i := by
  have h10 : i≠10 := by intro h; exact hi ⟨9,h.symm⟩
  fin_cases i <;> simp_all

theorem expand_eval (regs : Fin 8 → Bool) (bits mask baseline u v : List Bool)
    (hh : bits.length = Restriction.highCount mask) :
    ∃ (rf : Fin 8 → Bool), Eval expand (5*mask.length+3)
      (state regs bits mask baseline u v bits mask [] [] [] [] [])
      (state rf bits mask baseline u v [] [] (Restriction.zeroMerge mask bits).reverse [] [] [] []) := by
  let a := state regs bits mask baseline u v bits mask [] [] [] [] []
  obtain ⟨rs,hl⟩ := Restriction.zero_loop_eval (regs ∘ smallRegs) mask bits [] hh
  have he := (Restriction.popMask_eval (regs ∘ smallRegs) mask bits [] []).seq hl
  have ht : Trace Restriction.program (5*mask.length+3)
      ((Restriction.state (regs ∘ smallRegs) mask bits [] []).withPC
        (some Restriction.program.entry))
      ((Restriction.state rs [] [] [] (Restriction.zeroMerge mask bits).reverse).withPC none) := by
    have hn : 1 + (5*mask.length+1) + 1 = 5*mask.length+3 := by omega
    simpa only [Restriction.program, Restriction.command, List.append_nil, hn] using
      compiled_halt_trace he 0 3
  have hp : projectState smallRegs expandStacks a =
      Restriction.state (regs ∘ smallRegs) mask bits [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [← hp] at ht
  have hx := eval_call_from_state Restriction.program smallRegs expandStacks a
    (Fin.castAdd_injective _ _) (by decide) ht
  let rf : Fin 8 → Bool := fun i => if h : i.val < 4 then rs ⟨i.val,h⟩ else regs i
  have hb : embedState smallRegs expandStacks a
      (Restriction.state rs [] [] [] (Restriction.zeroMerge mask bits).reverse) =
      state rf bits mask baseline u v [] [] (Restriction.zeroMerge mask bits).reverse [] [] [] [] := by
    apply embedState_eq_of_ports smallRegs expandStacks a _ _
      (Fin.castAdd_injective _ _) (by decide)
    · intro i
      simp [state,rf,smallRegs,i.isLt,Restriction.state]
    · intro i hi
      have hn : ¬i.val<4 := by
        intro hh
        exact hi ⟨⟨i.val,hh⟩,Fin.ext rfl⟩
      simp [state,rf,hn,a]
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      exact expand_frame bits mask baseline u v _ i hi
  refine ⟨rf,?_⟩
  simpa only [expand, hb] using hx

theorem transfer_eval (regs : Fin 8 → Bool) (bits mask baseline u v full : List Bool) :
    Eval transfer (3*full.length+3)
      (state regs bits mask baseline u v [] [] full.reverse [] [] [] [])
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] full [] []) := by
  have h := ListRegisterProgram.transfer_run (7 : Fin 12) 9 (0 : Fin 8) 1
    (by decide) (by decide) regs
    (state regs bits mask baseline u v [] [] full.reverse [] [] [] []).stacks
  apply Eval.call
  have hs : transferStacks 7 9 (state regs bits mask baseline u v [] [] full.reverse [] [] [] []).stacks =
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] full [] []).stacks := by
    funext i; fin_cases i <;> simp [transferStacks,state]
  change Trace _ (3*full.reverse.length+3) _ _ at h
  rw [hs] at h
  simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC, state,
    List.length_reverse] using h

theorem merge_eval (regs : Fin 8 → Bool) (bits mask baseline u v full : List Bool)
    (hm : full.length = mask.length) (hb : full.length = baseline.length) :
    ∃ rf, Eval merge (30*full.length+22)
      (state regs bits mask baseline u v [] [] [] [] full [] [])
      (state rf bits mask baseline u v [] [] [] [] full
        (LeafAssignmentMergeProgram.merge full mask baseline) []) := by
  let a := state regs bits mask baseline u v [] [] [] [] full [] []
  obtain ⟨rf,ht⟩ := LeafAssignmentMergeProgram.Native.program_trace regs full mask baseline u v hm hb
  have hp : projectState id mergeStacks a =
      LeafAssignmentMergeProgram.Native.data regs full mask baseline u v [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [← hp] at ht
  have hx := eval_call_from_state LeafAssignmentMergeProgram.Native.program id mergeStacks a
    Function.injective_id (by decide) ht
  have he : embedState id mergeStacks a
      (LeafAssignmentMergeProgram.Native.data rf full mask baseline u v [] [] []
        (LeafAssignmentMergeProgram.merge full mask baseline)) =
      state rf bits mask baseline u v [] [] [] [] full
        (LeafAssignmentMergeProgram.merge full mask baseline) [] := by
    apply embedState_eq_of_ports id mergeStacks a _ _ Function.injective_id (by decide)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      exact merge_frame bits mask baseline u v full _ i hi
  exact ⟨rf,by simpa only [merge,he] using hx⟩

theorem clear_eval (regs : Fin 8 → Bool) (bits mask baseline u v full out : List Bool) :
    Eval clear (2*full.length+3)
      (state regs bits mask baseline u v [] [] [] [] full out [])
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] [] out []) := by
  have h := ListRegisterProgram.clear_run (9 : Fin 12) (0 : Fin 8) 1 regs
    (state regs bits mask baseline u v [] [] [] [] full out []).stacks
  apply Eval.call
  have hs : clearStacks 9 (state regs bits mask baseline u v [] [] [] [] full out []).stacks =
      (state (readRegs regs 0 1 none) bits mask baseline u v [] [] [] [] [] out []).stacks := by
    funext i; fin_cases i <;> simp [clearStacks,state]
  change Trace (clearProgram 9 0 1) (2*full.length+3) _ _ at h
  rw [hs] at h
  simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC, state] using h

/-- Compressed h-bit head assignments are expanded and merged physically;
all masters survive, and every temporary is empty on return. -/
theorem command_eval (regs : Fin 8 → Bool) (bits mask baseline u v : List Bool)
    (hh : bits.length = Restriction.highCount mask) (hm : mask.length = baseline.length) :
    ∃ rf, Eval command (7*bits.length+47*mask.length+41)
      (state regs bits mask baseline u v [] [] [] [] [] [] [])
      (state rf bits mask baseline u v [] [] [] [] []
        (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge mask bits) mask baseline) []) := by
  have h1 := copy_eval 0 5 (by decide) (by decide) (by decide)
    (state regs bits mask baseline u v [] [] [] [] [] [] []) rfl
  have h1' : Eval (copy 0 5) (7*bits.length+5)
      (state regs bits mask baseline u v [] [] [] [] [] [] [])
      (state (readRegs regs 0 1 none) bits mask baseline u v bits [] [] [] [] [] []) := by
    convert h1 using 1
    · simp [state]
    · apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;> simp [copyStacks, state]
  have h2 := copy_eval 1 6 (by decide) (by decide) (by decide)
    (state (readRegs regs 0 1 none) bits mask baseline u v bits [] [] [] [] [] []) rfl
  have h2' : Eval (copy 1 6) (7*mask.length+5)
      (state (readRegs regs 0 1 none) bits mask baseline u v bits [] [] [] [] [] [])
      (state (readRegs (readRegs regs 0 1 none) 0 1 none) bits mask baseline u v bits mask [] [] [] [] []) := by
    convert h2 using 1
    · simp [state]
    · apply congrArg (StructuredProgram.State.mk _)
      funext i; fin_cases i <;> simp [copyStacks, state]
  obtain ⟨r3,h3⟩ := expand_eval (readRegs (readRegs regs 0 1 none) 0 1 none) bits mask baseline u v hh
  have hlen : (Restriction.zeroMerge mask bits).length = mask.length :=
    (Restriction.zeroMerge_spec mask bits hh).1
  have h4 := transfer_eval r3 bits mask baseline u v (Restriction.zeroMerge mask bits)
  obtain ⟨r5,h5⟩ := merge_eval (readRegs r3 0 1 none) bits mask baseline u v (Restriction.zeroMerge mask bits)
    hlen (hlen.trans hm)
  have h6 := clear_eval r5 bits mask baseline u v (Restriction.zeroMerge mask bits)
    (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge mask bits) mask baseline)
  refine ⟨readRegs r5 0 1 none,?_⟩
  have hx := h1'.seq (h2'.seq (h3.seq (h4.seq (h5.seq h6))))
  rw [hlen] at hx
  convert hx using 1
  · rfl
  · omega

end Overlay

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem command_eval_oai (a : Data) (he : ∀ i∈changed, a.stacks i=[])
    (hh : (a.stacks 859).length=Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length=(a.stacks 869).length) :
    ∃ rf, Eval command (7*(a.stacks 859).length+47*(a.stacks 670).length+42)
      a (result a rf) := by
  have hp : projectState regMap stackMap a = Overlay.state (a.regs ∘ regMap)
      (a.stacks 859) (a.stacks 670) (a.stacks 869) (a.stacks 870) (a.stacks 871)
      [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [stackMap,
        he 145 (by simp [changed]),he 872 (by simp [changed]),he 873 (by simp [changed]),
        he 874 (by simp [changed]),he 875 (by simp [changed]),he 876 (by simp [changed]),
        he 877 (by simp [changed])]
  obtain ⟨rf,hs⟩ := Overlay.command_eval (a.regs ∘ regMap)
    (a.stacks 859) (a.stacks 670) (a.stacks 869) (a.stacks 870) (a.stacks 871) hh hm
  have ht := compiled_halt_trace hs 0 10
  rw [← hp] at ht
  exact ⟨rf,eval_call_from_state Overlay.program regMap stackMap a
    (Fin.castAdd_injective _ _) (by decide) ht⟩

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.command_eval_oai
