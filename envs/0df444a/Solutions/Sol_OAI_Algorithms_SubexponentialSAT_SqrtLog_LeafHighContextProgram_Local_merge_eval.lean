-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.merge_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:15:31.879364+00:00
-- url     : https://prove2.me/submissions/034c97fa-d5ea-42fd-94f3-3f6972815231

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144

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

theorem zero_program_runsIn (regs : Fin 4 → Bool) (mask high out : List Bool)
    (hh : high.length = highCount mask) :
    ∃ rf, RunsIn program (5 * mask.length + 3)
      ((state regs mask high [] out).withPC (some program.entry))
      ((state rf [] [] [] ((zeroMerge mask high).reverse ++ out)).withPC none) := by
  obtain ⟨rf, hl⟩ := zero_loop_eval regs mask high out hh
  have he := (popMask_eval regs mask high [] out).seq hl
  refine ⟨rf, 1 + (5 * mask.length + 1) + 1, by omega, ?_⟩
  exact compiled_halt_trace he 0 3

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

/-- Transport only a caller's initial state; do not rewrite through its program. -/
theorem transport_initial {r s l : ℕ} (p : Program r s l) (bound : ℕ)
    {a b final : State r s} (hab : a = b)
    (h : RunsIn p bound (a.withPC (some p.entry)) (final.withPC none)) :
    RunsIn p bound (b.withPC (some p.entry)) (final.withPC none) := by
  cases hab
  exact h


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramMerge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem merge_eval_oai (regs : Fin 4 → Bool) (counter mask forward high : List Bool)
    (hh : high.length = HighIncidenceProgram.Restriction.highCount mask) :
    ∃ n rf, n ≤ 5*mask.length+3 ∧ Eval mergeStep n
      (state regs counter mask forward [] [] [] high mask [] [])
      (state rf counter mask forward
        (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse [] [] [] [] [] []) := by
  let a := state regs counter mask forward [] [] [] high mask [] []
  obtain ⟨rf,raw⟩ := HighIncidenceProgram.Restriction.zero_program_runsIn regs mask high [] hh
  have hfinish : HighIncidenceProgram.Restriction.state rf [] [] []
      ((HighIncidenceProgram.Restriction.zeroMerge mask high).reverse ++ []) =
      HighIncidenceProgram.Restriction.state rf [] [] []
        (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse := by rw [List.append_nil]
  have hr := Eq.mp (congrArg (fun finish =>
    RunsIn HighIncidenceProgram.Restriction.program (5*mask.length+3)
      ((HighIncidenceProgram.Restriction.state regs mask high [] []).withPC
        (some HighIncidenceProgram.Restriction.program.entry))
      (finish.withPC none)) hfinish) raw
  have ha : restrictState id mergeStacks a =
      HighIncidenceProgram.Restriction.state regs mask high [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have hr' := transport_initial HighIncidenceProgram.Restriction.program
    (5*mask.length+3) ha.symm hr
  obtain ⟨n,hn,he⟩ := lifted_call HighIncidenceProgram.Restriction.program id mergeStacks
    Function.injective_id (by decide) a
    (HighIncidenceProgram.Restriction.state rf [] [] []
      (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse)
    (5*mask.length+3) hr'
  have hb : embedState id mergeStacks a
      (HighIncidenceProgram.Restriction.state rf [] [] []
        (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse) =
      state rf counter mask forward (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse
        [] [] [] [] [] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (by decide)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;>
        first
        | rfl
        | exact (hi ⟨0,rfl⟩).elim
        | exact (hi ⟨1,rfl⟩).elim
        | exact (hi ⟨2,rfl⟩).elim
        | exact (hi ⟨3,rfl⟩).elim
  have he' := Eq.mp (congrArg (fun b => Eval mergeStep n a b) hb) he
  exact ⟨n,rf,hn,he'⟩



end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.merge_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.merge_eval_oai
