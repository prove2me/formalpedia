-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:07:10.556001+00:00
-- url     : https://prove2.me/submissions/9ae93cb2-d0cd-489e-8269-7ccca3235f40

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_ExecCoreChildProgram_program_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_programB_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_resultB_length_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSemanticHelpers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact list identities used when composing executable CNF filters. -/
namespace SubexponentialSAT.Encoding
universe u

/-- Filtering discards complete frames; this bound needs no property of the
payload encoder. -/
theorem length_encodeList_filter_le {α : Type u} (enc : α → List Bool)
    (keep : α → Bool) (values : List α) :
    (encodeList enc (values.filter keep)).length ≤ (encodeList enc values).length := by
  induction values with
  | nil => simp
  | cons a values ih =>
    cases h : keep a with
    | false =>
      simp [ h, length_encodeList_cons] ; omega
    | true =>
      simp [ h, length_encodeList_cons] ; omega

end SubexponentialSAT.Encoding

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

/-- Clause deduplication retains a subsequence of the original payloads. -/
theorem length_encodeList_dedupClauses_le (enc : Clause α → List Bool) (F : Formula α) :
    (Encoding.encodeList enc (dedupClauses F)).length ≤
      (Encoding.encodeList enc F).length := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega

/-- Absorption cannot increase the serialized formula length, even when the
payload encoder uses unequal-length clause encodings. -/
theorem length_encodeList_absorb_le (enc : Clause α → List Bool) (F : Formula α) :
    (Encoding.encodeList enc (absorb F)).length ≤
      (Encoding.encodeList enc F).length := by
  unfold absorb
  exact (Encoding.length_encodeList_filter_le enc _ _).trans
    (length_encodeList_dedupClauses_le enc F)

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseSelfFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Complete fixed-master clause filtering

This wrapper performs the actual initial copy, record scan, cleanup, and
record-order restoration. Its input and output are on stack 13; every other
stack is empty at both boundaries.
-/

namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)


theorem ready_eq_state (d : Data) (hready : Ready d) :
    d = state d.regs [] [] [] (d.stacks 13) [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  by_cases hi : i = 13
  · subst i
    rfl
  · rw [hready i hi]
    fin_cases i <;> simp_all []

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


/-- The returned child adds at most the serialized core record to the parent
length. This is independent of list order and duplicate literal encodings. -/
theorem result_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (result F selected H)).length ≤
      (formulaCode F).length + 2 * (clauseCode H).length + 2 := by
  have hfilter := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  have habsorb := ExecCNF.length_encodeList_absorb_le clauseCode
    (H :: ExecCNF.eraseClauses F selected)
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at hfilter
  change (formulaCode (result F selected H)).length ≤
    (Encoding.encodeList clauseCode (H :: ExecCNF.eraseClauses F selected)).length at habsorb
  rw [Encoding.length_encodeList_cons] at habsorb
  change (formulaCode (result F selected H)).length ≤ 2 * (clauseCode H).length + 2 +
    (formulaCode (ExecCNF.eraseClauses F selected)).length at habsorb
  omega

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecBranchControllerSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual copying, child calls, and framed output for the two-child controller.
Ports 0--6 hold pending work, leaves, both outputs, parent, core, and selection.
Ports 7--22 are a reusable 16-stack child workspace. -/

namespace SubexponentialSAT.ExecBranchControllerSupport

open BitProgram StructuredCalls


theorem bankPort_injective : Function.Injective bankPort := fun _ _ h => bankPort_inj.mp h

theorem state_stacks (regs regs' : Regs) (front : Front) (bank : Bank) :
    (state regs front bank).stacks = (state regs' front bank).stacks := rfl

theorem state_update_bank (regs : Regs) (front : Front) (bank : Bank)
    (i : Fin 16) (bits : List Bool) :
    state regs front (Function.update bank i bits) =
      ⟨regs, Function.update (state regs front bank).stacks (bankPort i) bits⟩ := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
  · change (state regs front (Function.update bank i bits)).stacks (frontPort k) =
      Function.update (state regs front bank).stacks (bankPort i) bits (frontPort k)
    simp
  · change (state regs front (Function.update bank i bits)).stacks (bankPort k) =
      Function.update (state regs front bank).stacks (bankPort i) bits (bankPort k)
    simp [Function.update_apply]

theorem state_update_front (regs : Regs) (front : Front) (bank : Bank)
    (i : Fin 7) (bits : List Bool) :
    state regs (Function.update front i bits) bank =
      ⟨regs, Function.update (state regs front bank).stacks (frontPort i) bits⟩ := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
  · change (state regs (Function.update front i bits) bank).stacks (frontPort k) =
      Function.update (state regs front bank).stacks (frontPort i) bits (frontPort k)
    simp [Function.update_apply]
  · change (state regs (Function.update front i bits) bank).stacks (bankPort k) =
      Function.update (state regs front bank).stacks (frontPort i) bits (bankPort k)
    simp []

theorem copyInto_eval (src : Fin 7) (dst tmp : Fin 16) (regs : Regs)
    (front : Front) (bank : Bank) (hne : tmp ≠ dst)
    (hdst : bank dst = []) (htmp : bank tmp = []) :
    Eval (copyInto src dst tmp) (7 * (front src).length + 5)
      (state regs front bank)
      (state (reset regs) front (Function.update bank dst (front src))) := by
  have h := ListRegisterProgram.copy_run (frontPort src) (bankPort dst) (bankPort tmp)
    (0 : Fin 15) 1 (front_ne_bank _ _) (front_ne_bank _ _)
    (fun h => hne (bankPort_inj.mp h)) (by decide)
    regs (state regs front bank).stacks (by simpa using htmp)
  rw [state_update_bank]
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hdst, reset, state_front, state_bank,
    state_stacks regs (reset regs)] using h

theorem load_eval (regs : Regs) (front : Front) :
    Eval load (loadCost front) (idle regs front)
      (state (reset regs) front (loaded (reset regs) front).stacks) := by
  let b1 : Bank := Function.update emptyBank 9 (front 5)
  let b2 : Bank := Function.update b1 12 (front 6)
  let b3 : Bank := Function.update b2 13 (front 4)
  have h1 := copyInto_eval 5 9 0 regs front emptyBank (by decide) rfl rfl
  have h2 := copyInto_eval 6 12 0 (reset regs) front b1 (by decide)
    (by simp [b1, emptyBank]) (by simp [b1, emptyBank])
  have h3 := copyInto_eval 4 13 0 (reset (reset regs)) front b2 (by decide)
    (by simp [b2, b1, emptyBank]) (by simp [b2, b1, emptyBank])
  have hb : b3 = (loaded (reset regs) front).stacks := by
    funext i
    fin_cases i <;> simp [b3, b2, b1, emptyBank, loaded, ExecClauseFiltersProgram.state]
  have h := h1.seq (h2.seq h3)
  change Eval load _ (idle regs front) (state _ front b3) at h
  rw [hb, reset_reset, reset_reset] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold loadCost
  omega

theorem embed_child (frameRegs : Regs) (front : Front) (frameBank : Bank)
    (child : State 15 16) :
    embedState id bankPort (state frameRegs front frameBank) child =
      state child.regs front child.stacks := by
  apply embedState_eq_of_ports id bankPort _ _ _ Function.injective_id bankPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; simp
  · intro i
    refine Fin.addCases (m := 7) (n := 16) (fun j hi => ?_) (fun j hi => ?_) i
    · exact (state_front child.regs front child.stacks j).trans
        (state_front frameRegs front frameBank j).symm
    · exact (hi ⟨j, rfl⟩).elim

theorem callChild_eval {l : ℕ} (p : Program 15 16 l) (front : Front)
    {n : ℕ} {a b : State 15 16}
    (h : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (callChild p) n (state a.regs front a.stacks) (state b.regs front b.stacks) := by
  have he := eval_call_lifted p id bankPort (state a.regs front a.stacks)
    Function.injective_id bankPort_injective h
  simpa only [embed_child, callChild] using he

theorem emitReg_injective : Function.Injective emitReg := Fin.castAdd_injective 3 12
theorem emitPort_injective (i : Fin 2) : Function.Injective (emitPort i) := by
  fin_cases i <;> decide

theorem emitInto_eval (i : Fin 2) (bits : List Bool) (d : Data)
    (hpayload : d.stacks (bankPort 0) = bits.reverse) :
    Eval (emitInto i) (5 * bits.length + 7) d (emitAfter i bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks (frontPort 0)) (d.stacks (frontPort 1))
    (d.stacks (frontPort (outputPort i))) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks (frontPort 0)) (d.stacks (frontPort 1))
    (ExecWorklistProgram.record bits ++ d.stacks (frontPort (outputPort i))) []
  have ha : embedState emitReg (emitPort i) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective (emitPort_injective i)
    · intro j; fin_cases j <;> rfl
    · intro j hj; rfl
    · intro j; fin_cases j <;> simp [a, emitPort, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hpayload]
    · intro j hj; rfl
  have hb : embedState emitReg (emitPort i) d b = emitAfter i bits d := by
    apply embedState_eq_of_ports _ _ _ _ _ emitReg_injective (emitPort_injective i)
    · intro j
      fin_cases j <;> simp [b, emitReg, emitAfter, emittedRegs, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      simp [emitAfter, emittedRegs, h0, h1]
    · intro j
      fin_cases j <;> simp [b, emitPort, emitAfter, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, Ne.symm (outputPort_ne_zero i), Ne.symm (outputPort_ne_one i)]
    · intro j hj
      have ho : j ≠ frontPort (outputPort i) := fun h => hj ⟨2, h.symm⟩
      have hp : j ≠ bankPort 0 := fun h => hj ⟨3, h.symm⟩
      simp [emitAfter, ho, hp]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits
    (d.stacks (frontPort 0)) (d.stacks (frontPort 1))
    (d.stacks (frontPort (outputPort i))) (d.regs 0) (d.regs 1) (d.regs 2)
  have he := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram emitReg (emitPort i) d
    emitReg_injective (emitPort_injective i) ht
  change Eval (emitInto i) _ (embedState emitReg (emitPort i) d a)
    (embedState emitReg (emitPort i) d b) at he
  simpa only [ha, hb] using he

theorem toPayload_eval (regs : Regs) (front : Front) (bits : List Bool) :
    Eval toPayload (3 * bits.length + 3)
      (state regs front (wordBank 13 bits))
      (state (reset regs) front (wordBank 0 bits.reverse)) := by
  let d := state regs front (wordBank 13 bits)
  have hs : StackRoutines.transferStacks (bankPort 13) (bankPort 0) d.stacks =
      (state (reset regs) front (wordBank 0 bits.reverse)).stacks := by
    funext j
    refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
    · change StackRoutines.transferStacks (bankPort 13) (bankPort 0) d.stacks (frontPort k) =
        (state (reset regs) front (wordBank 0 bits.reverse)).stacks (frontPort k)
      simp [StackRoutines.transferStacks, d, wordBank, emptyBank]
    · change StackRoutines.transferStacks (bankPort 13) (bankPort 0) d.stacks (bankPort k) =
        (state (reset regs) front (wordBank 0 bits.reverse)).stacks (bankPort k)
      fin_cases k <;> simp [StackRoutines.transferStacks, d, wordBank, emptyBank]
  have h := ListRegisterProgram.transfer_run (bankPort 13) (bankPort 0) (0 : Fin 15) 1
    (by decide) (by decide) regs d.stacks
  rw [state_bank] at h
  rw [hs] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, d, wordBank,
    emptyBank, reset, state_regs] using h

theorem frameChild_eval (i : Fin 2) (regs : Regs) (front : Front) (bits : List Bool) :
    Eval (frameChild i) (8 * bits.length + 10)
      (state regs front (wordBank 13 bits))
      (idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
        (ExecWorklistProgram.record bits ++ front (outputPort i)))) := by
  let d := state (reset regs) front (wordBank 0 bits.reverse)
  have he := emitInto_eval i bits d (by simp [d, wordBank])
  have hfinal : emitAfter i bits d =
      idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
        (ExecWorklistProgram.record bits ++ front (outputPort i))) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    refine Fin.addCases (m := 7) (n := 16) (fun k => ?_) (fun k => ?_) j
    · change (emitAfter i bits d).stacks (frontPort k) =
        (idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
          (ExecWorklistProgram.record bits ++ front (outputPort i)))).stacks (frontPort k)
      simp [emitAfter, d, idle, Function.update_apply]
    · change (emitAfter i bits d).stacks (bankPort k) =
        (idle (emittedRegs (reset regs)) (Function.update front (outputPort i)
          (ExecWorklistProgram.record bits ++ front (outputPort i)))).stacks (bankPort k)
      by_cases hk : k = 0 <;> simp [emitAfter, d, idle, wordBank, emptyBank, hk]
  rw [hfinal] at he
  have h := (toPayload_eval regs front bits).seq he
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  omega

/-- Compose a measured execution of a concrete child table with the actual
input copies and frame writer. This lemma only links real instruction traces. -/
theorem buildChild_eval {l : ℕ} (p : Program 15 16 l) (i : Fin 2)
    (regs : Regs) (front : Front) (bits : List Bool) (rf : Regs) {n : ℕ}
    (h : Trace p n ((loaded (reset regs) front).withPC (some p.entry))
      ((ExecClauseFiltersProgram.state rf [] [] [] bits [] []).withPC none)) :
    Eval (buildChild p i) (loadCost front + (n + (8 * bits.length + 10)))
      (idle regs front)
      (idle (emittedRegs (reset rf)) (Function.update front (outputPort i)
        (ExecWorklistProgram.record bits ++ front (outputPort i)))) := by
  have hc := callChild_eval p front h
  have hbank : (ExecClauseFiltersProgram.state rf [] [] [] bits [] []).stacks =
      wordBank 13 bits := by
    funext j
    fin_cases j <;> simp [ExecClauseFiltersProgram.state, wordBank, emptyBank]
  rw [hbank] at hc
  exact (load_eval regs front).seq (hc.seq (frameChild_eval i rf front bits))

theorem clearFront_eval (i : Fin 7) (regs : Regs) (front : Front) :
    Eval (clearFront i) (2 * (front i).length + 3) (idle regs front)
      (idle (reset regs) (Function.update front i [])) := by
  have h := ListRegisterProgram.clear_run (frontPort i) (0 : Fin 15) 1 regs (idle regs front).stacks
  rw [show (idle regs front).stacks (frontPort i) = front i by simp [idle]] at h
  change Eval _ _ _ (state (reset regs) (Function.update front i []) emptyBank)
  rw [state_update_front]
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, StackRoutines.clearStacks,
    reset, idle, state_regs, state_stacks regs (reset regs)] using h

theorem cleanInputs_eval (regs : Regs) (front : Front) :
    Eval cleanInputs (2 * ((front 4).length + (front 5).length + (front 6).length) + 9)
      (idle regs front) (idle (reset regs) (cleanFront front)) := by
  have h1 := clearFront_eval 4 regs front
  have h2 := clearFront_eval 5 (reset regs) (Function.update front 4 [])
  have h3 := clearFront_eval 6 (reset (reset regs)) (Function.update (Function.update front 4 []) 5 [])
  have h := h1.seq (h2.seq h3)
  simp only [Function.update_of_ne (by decide : (5 : Fin 7) ≠ 4),
    Function.update_of_ne (by decide : (6 : Fin 7) ≠ 5),
    Function.update_of_ne (by decide : (6 : Fin 7) ≠ 4), reset_reset] at h
  convert h using 1
  · omega
  · rfl

end SubexponentialSAT.ExecBranchControllerSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

open ExecBranchControllerSupport

private theorem loaded_ready (regs : Regs) (front : Front) :
    ExecCoreChildProgram.InputReady (loaded regs front) := by
  intro i h9 h12 h13
  fin_cases i <;> first | exact False.elim (h9 rfl) | exact False.elim (h12 rfl) |
    exact False.elim (h13 rfl) | rfl

theorem command_eval (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) :
    ∃ t ≤ 610000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
      Eval command t (inputState regs pending header F S H)
        (outputState pending header F S H) := by
  let f0 := inputFront pending header F S H
  let wordA := ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)
  let wordB := ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)
  obtain ⟨a, haReady, haOut, t, ht, ha⟩ :=
    ExecCoreChildProgram.program_runsIn F S H (loaded (reset regs) f0) rfl rfl rfl
      (loaded_ready (reset regs) f0)
  have haEq : a = ExecClauseFiltersProgram.state a.regs [] [] [] wordA [] [] := by
    simpa only [haOut] using ExecClauseFiltersProgram.ready_eq_state a haReady
  rw [haEq] at ha
  have hA := buildChild_eval ExecCoreChildProgram.program 0 regs f0 wordA a.regs ha
  simp only [show outputPort 0 = 2 from rfl, show f0 2 = [] from rfl, List.append_nil] at hA
  let ra := emittedRegs (reset a.regs)
  let fa : Front := Function.update f0 2 (ExecWorklistProgram.record wordA)
  obtain ⟨b, hbReady, hbOut, u, hu, hb⟩ :=
    programB_runsIn F S H (loaded (reset ra) fa) rfl rfl rfl (loaded_ready (reset ra) fa)
  have hbEq : b = ExecClauseFiltersProgram.state b.regs [] [] [] wordB [] [] := by
    simpa only [hbOut] using ExecClauseFiltersProgram.ready_eq_state b hbReady
  rw [hbEq] at hb
  have hB := buildChild_eval programB 1 ra fa wordB b.regs hb
  simp only [show outputPort 1 = 3 from rfl, show fa 3 = [] from rfl, List.append_nil] at hB
  let rb := emittedRegs (reset b.regs)
  let fb : Front := Function.update fa 3 (ExecWorklistProgram.record wordB)
  have hclean := cleanInputs_eval rb fb
  have hreset := RegisterResetProgram.all_eval (idle (reset rb) (cleanFront fb))
  have hfinal : cleanFront fb = outputFront pending header wordA wordB := by
    funext i
    fin_cases i <;> simp [cleanFront, fb, fa, f0, inputFront, outputFront]
  have hfull := hA.seq (hB.seq (hclean.seq hreset))
  rw [hfinal] at hfull
  change Eval command _ (inputState regs pending header F S H)
    (outputState pending header F S H) at hfull
  refine ⟨_, ?_, hfull⟩
  let V := ExecCoreChildProgram.inputVolume F S H
  have hv : 1 ≤ V := by dsimp [V, ExecCoreChildProgram.inputVolume]; omega
  have hsq : V ≤ V ^ 2 := by nlinarith [Nat.mul_le_mul_left V hv]
  have hsum : (ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length ≤ V := by
    dsimp [V, ExecCoreChildProgram.inputVolume]
    omega
  have hlenA : wordA.length ≤ V := by
    have h := ExecCoreChildProgram.result_length_le F S H
    dsimp [wordA, V, ExecCoreChildProgram.inputVolume]
    omega
  have hlenB : wordB.length ≤ 5 * V := resultB_length_le F S H
  have hload0 : loadCost f0 ≤ 7 * V + 15 := by
    change 7 * ((ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length) + 15 ≤ _
    omega
  have hloadA : loadCost fa = loadCost f0 := by simp [loadCost, fa]
  have hcleanup : 2 * ((fb 4).length + (fb 5).length + (fb 6).length) + 9 ≤ 2 * V + 9 := by
    change 2 * ((ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length) + 9 ≤ _
    omega
  change t ≤ 3300 * V ^ 2 at ht
  change u ≤ 600000 * V ^ 2 at hu
  change loadCost f0 + (t + (8 * wordA.length + 10)) +
    (loadCost fa + (u + (8 * wordB.length + 10)) +
      (2 * ((fb 4).length + (fb 5).length + (fb 6).length) + 9 + 15)) ≤ 610000 * V ^ 2
  rw [hloadA]
  nlinarith

theorem program_runsIn_oai (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) :
    RunsIn program (620000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
      ((inputState regs pending header F S H).withPC (some program.entry))
      ((outputState pending header F S H).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval regs pending header F S H
  refine ⟨t + 1, ?_, compiled_halt_trace he 4 2⟩
  have hv : 0 < ExecCoreChildProgram.inputVolume F S H := by
    unfold ExecCoreChildProgram.inputVolume
    omega
  have hp := pow_pos hv 2
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn_oai
