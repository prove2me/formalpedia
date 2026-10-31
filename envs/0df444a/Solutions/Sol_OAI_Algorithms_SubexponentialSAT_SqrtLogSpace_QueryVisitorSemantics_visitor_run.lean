-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:59:30.905099+00:00
-- url     : https://prove2.me/submissions/1e342655-ab96-469e-af7a-fa9edd35c166

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTupleState_finish
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTupleState_initialize_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_baseline_pass
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_evaluation_pass
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_representativeWord_selected
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLogic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section Traces

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- A frame observation preserved by each actual step is preserved by the run. -/
theorem frame_trace {Frame : Type} (frame : Cfg → Frame)
    (preserve : ∀ a b, step a = some b → frame b = frame a)
    {steps : ℕ} {a b : Cfg} (h : Trace step steps a b) : frame b = frame a := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (preserve _ _ hs)

end Traces

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

theorem execInstr_register_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin r)
    (hk : k ∉ registerWrites instr) : (execInstr instr c).regs k = c.regs k := by
  cases instr <;> simp_all [registerWrites, execInstr, readRegs]

theorem step_register_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin r)
    (safe : ∀ label, a.pc = some label → k ∉ registerWrites (p.code label))
    (hs : step p a = some b) : b.regs k = a.regs k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_register_frame _ _ _ (safe label hp)

end BitPrograms

end SubexponentialSAT.ProgramLogic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandRegisterFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Register frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

open OAI BitProgram ProgramLogic

theorem trace_register_frame {r s l : ℕ} (p : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (ht : Trace p steps a b)
    (i : Fin r) (hi : i ∉ programWrites p) : b.regs i = a.regs i := by
  apply ProgramLogic.frame_trace (fun c : Cfg r s l => c.regs i) ?_ ht
  intro a b hs
  exact step_register_frame p i (fun label _ => (not_mem_programWrites p i).mp hi label) hs

theorem base_eval_register_frame {r s : ℕ} {c : StructuredProgram.Cmd r s}
    {steps : ℕ} {a b : StructuredProgram.State r s}
    (ht : StructuredProgram.Eval c steps a b) (i : Fin r)
    (hi : i ∉ baseWrites c) : b.regs i = a.regs i := by
  induction ht with
  | skip => rfl
  | atom atom a => exact execInstr_register_frame (atom.instr (0 : Fin 1)) (a.withPC none) i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ baseWrites first ∧ i ∉ baseWrites second := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Every actual execution preserves each register outside the static writes. -/
theorem eval_register_frame {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (ht : StructuredCalls.Eval c steps a b) (i : Fin r)
    (hi : i ∉ writes c) : b.regs i = a.regs i := by
  induction ht with
  | base he => exact base_eval_register_frame he i hi
  | call p ht => exact trace_register_frame p ht i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ writes first ∧ i ∉ writes second := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Relocation changes every destination by precisely the declared register map. -/
theorem relocate_writes {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (instr : Instr r s l) :
    registerWrites (ProgramLinking.relocateInstr register stack label returnPc instr) =
      (registerWrites instr).image register := by
  cases instr <;> cases returnPc <;> simp [ProgramLinking.relocateInstr, registerWrites]

theorem not_mem_liftProgram {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    i ∉ programWrites (ProgramLinking.liftProgram p register stack) := by
  rw [not_mem_programWrites]
  intro label
  simp only [relocate_writes, Finset.mem_image, not_exists]
  intro j hj
  exact hi ⟨j, hj.2⟩


theorem not_mem_liftCommand {r s R S : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (i : Fin R) (hi : ¬ ∃ j, register j = i) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) :=
  not_mem_liftProgram _ register stack i hi

/-- These primitive loops can only write their explicit value/presence registers. -/
theorem not_mem_clearProgram {r s : ℕ} (src : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.clearProgram src value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.copyProgram src dst tmp value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
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

theorem merge_ofFn {n : ℕ} (a h b : Fin n → Bool) :
    merge (List.ofFn a) (List.ofFn h) (List.ofFn b) =
      List.ofFn (fun i => if h i then a i else b i) := by
  induction n with
  | zero => simp [merge]
  | succ n ih => simp [List.ofFn_succ,merge,ih]

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadRepresentativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafAssignmentMergeProgram

/-- Exact meaning of repeated executions of the original ambient merge scan.
A head's supplied word need only agree with the target at its selected coordinates. -/
theorem merge_fold_ofFn {n : ℕ} {G : Type*} (heads : List G)
    (mask current : G → Fin n → Bool) (baseline target : Fin n → Bool)
    (hcurrent : ∀ g ∈ heads,∀ v,mask g v=true → current g v=target v) :
    heads.foldl (fun acc g => merge (List.ofFn (current g)) (List.ofFn (mask g)) acc)
        (List.ofFn baseline) =
      List.ofFn (fun v => if heads.any (fun g => mask g v) then target v else baseline v) := by
  induction heads generalizing baseline with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons,merge_ofFn]
    rw [ih _ (fun h hh => hcurrent h (by simp [hh]))]
    apply congrArg List.ofFn
    funext v
    have hg := hcurrent g (by simp) v
    cases hm : mask g v <;> cases ht : gs.any (fun h => mask h v) <;>
      simp only [List.any_cons, hm, ht, Bool.or_false, Bool.or_true, Bool.false_eq_true,
        ite_true, if_true, ite_false]
    exact hg hm

/-- All representative heads reconstruct the full ambient assignment, with
fixed-high coordinates retained. Head order and repeated visits are harmless. -/
theorem representative_heads {n : ℕ} {G : Type*} [DecidableEq G]
    (H : Finset (Fin n)) (high : H → Bool) (head : Fin n → G)
    (reps : ∀ g,Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (heads : List G) (hcover : ∀ g,g∈heads) (current : G → Fin n → Bool)
    (hcurrent : ∀ g ∈ heads,∀ v (hv : v∉H) (hg : head v=g),
      current g v=reps g ⟨⟨v,hv⟩,hg⟩) :
    heads.foldl (fun acc g => merge (List.ofFn (current g))
        (List.ofFn (fun v => decide (v∉H ∧ head v=g))) acc)
        (List.ofFn (HighIncidence.glue H high (fun _ => false))) =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val) reps)) := by
  classical
  rw [merge_fold_ofFn heads _ _ _
    (HighIncidence.glue H high (Moments.assemble (fun v : {v : Fin n // v∉H} => head v.val) reps))]
  · apply congrArg List.ofFn
    funext v
    by_cases hv : v∈H
    · have hm : heads.any (fun g => decide (v∉H ∧ head v=g))=false := by simp [hv]
      simp [HighIncidence.glue, hv]
    · have hm : heads.any (fun g => decide (v∉H ∧ head v=g))=true := by
        apply List.any_eq_true.mpr
        exact ⟨head v,hcover (head v),by simp [hv]⟩
      simp only [hm, ite_true, if_true]
  · intro g hg v hv
    have hm : v∉H ∧ head v=g := of_decide_eq_true hv
    rw [hcurrent g hg v hm.1 hm.2]
    simp only [HighIncidence.glue, dite_eq_right hm.1, Moments.assemble]
    have hg := hm.2
    subst g
    rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem trace_prefix_bound_trans {α : Type*} {step : α → Option α}
    {a b : α} {firstSteps secondSteps : ℕ} {P : α → Prop}
    (first : Computation.Trace step firstSteps a b)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ secondSteps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps + secondSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle htrace
  by_cases hprefix : prefixSteps ≤ firstSteps
  · exact hfirst prefixSteps intermediate hprefix htrace
  · exact hsecond (prefixSteps - firstSteps) intermediate (by omega)
      (trace_suffix htrace first (by omega))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

private theorem base_entry_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l) :
    StructuredProgram.entry c (label ∘ embed) (label exit) =
      label (StructuredProgram.entry c embed exit) := by
  induction c generalizing l L with
  | skip => rfl
  | atom => rfl
  | seq first second ihf ihs =>
      change StructuredProgram.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem base_code_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (site : StructuredProgram.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredProgram.code c embed exit site) =
      StructuredProgram.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | skip => exact site.elim
  | atom op => cases op <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredProgram.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [base_entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredProgram.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (base_entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (base_entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (base_entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem entry_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l) :
    StructuredCalls.entry c (label ∘ embed) (label exit) =
      label (StructuredCalls.entry c embed exit) := by
  induction c generalizing l L with
  | base c => exact base_entry_map c label embed exit
  | call => rfl
  | seq first second ihf ihs =>
      change StructuredCalls.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem code_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (site : StructuredCalls.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredCalls.code c embed exit site) =
      StructuredCalls.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | base c => exact base_code_map c label embed exit site
  | call p =>
      simp only [StructuredCalls.code]
      cases p.code site <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredCalls.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredCalls.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem commandLabel_sites {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit ∘ StructuredCalls.siteAddress c = embed := by
  funext site
  exact commandLabel_site c embed exit site

private theorem commandLabel_entry {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s) :
    commandLabel c embed exit (StructuredCalls.compiled c inputStack outputStack).entry =
      StructuredCalls.entry c embed exit := by
  change commandLabel c embed exit
    (StructuredCalls.entry c (StructuredCalls.siteAddress c) (StructuredCalls.exitAddress c)) = _
  rw [← entry_map c (commandLabel c embed exit) (StructuredCalls.siteAddress c)
    (StructuredCalls.exitAddress c), commandLabel_sites, commandLabel_exit]

private theorem commandLabel_code {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site)
    (pc : Fin (StructuredCalls.size c + 1)) (hpc : pc ≠ StructuredCalls.exitAddress c) :
    caller.code (commandLabel c embed exit pc) =
      ProgramLinking.relocateInstr id id (commandLabel c embed exit) none
        ((StructuredCalls.compiled c inputStack outputStack).code pc) := by
  obtain ⟨site, rfl⟩ : ∃ site, pc = StructuredCalls.siteAddress c site := by
    cases heq : (StructuredCalls.labelEquiv c).symm pc with
    | none =>
        have hp := congrArg (StructuredCalls.labelEquiv c) heq
        exact (hpc (by simpa [StructuredCalls.exitAddress] using hp)).elim
    | some site =>
        exact ⟨site, by simpa [StructuredCalls.siteAddress] using
          (congrArg (StructuredCalls.labelEquiv c) heq)⟩
  rw [commandLabel_site, StructuredCalls.compiled_site, code_map,
    commandLabel_sites, commandLabel_exit]
  exact hcode site

/-- A bound proved for one compiled structured block transfers to every
installation of that same block in a finite caller table. No bound on the
caller's total runtime is used. -/
theorem command_stack_bound {r s L : ℕ} {c : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval c steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled c inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled c inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry c embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  let routine := StructuredCalls.compiled c inputStack outputStack
  let label := commandLabel c embed exit
  let frame := a.withPC (some (StructuredCalls.entry c embed exit))
  have full := StructuredCalls.compiled_trace heval inputStack outputStack
  obtain ⟨source, hs⟩ := trace_prefix_exists full hle
  have hactive : source.pc ≠ none := by
    intro hnone
    have halted := ProgramLinking.trace_from_halted routine (trace_suffix full hs hle) hnone
    change some (StructuredCalls.exitAddress c) = none at halted
    cases halted
  have htable : ∀ pc, routine.code pc ≠ .halt →
      caller.code (label pc) = ProgramLinking.relocateInstr id id label none (routine.code pc) := by
    intro pc hnot
    apply commandLabel_code c caller embed exit inputStack outputStack hcode pc
    intro heq
    subst pc
    exact hnot (StructuredCalls.compiled_exit c inputStack outputStack)
  have hrelocated := ProgramLinking.relocate_trace_before_halt routine caller id id
    label none frame Function.injective_id Function.injective_id htable hs hactive
  have hinitial : ProgramLinking.embedCfg id id label none frame
      (a.withPC (some routine.entry)) = frame := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, routine, label, frame,
      StructuredProgram.State.withPC, commandLabel_entry]
  rw [hinitial] at hrelocated
  have heq := trace_same_length_unique hp hrelocated
  rw [heq]
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- Sequential command blocks share one uniform space bound. -/
theorem sequence_stack_bound {r s L : ℕ} {first second : StructuredCalls.Cmd r s}
    {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (hf : StructuredCalls.Eval first n a b) (hs : StructuredCalls.Eval second m b c)
    (inputStack outputStack : Fin s)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled first inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled first inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled second inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled second inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.seq first second) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.seq first second) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.seq first second) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  exact trace_prefix_bound_trans
    (StructuredCalls.eval_trace hf caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hf inputStack outputStack hfirst caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hs inputStack outputStack hsecond caller (embed ∘ Sum.inr)
      exit (fun q => hcode (.inr q)))

/-- The final concrete halt instruction changes no stack and preserves the
bound already established through the command's exit boundary. -/
theorem compiled_halt_stack_bound {r s : ℕ} {command : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval command steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp
  by_cases hbefore : prefixSteps ≤ steps
  · exact hsource prefixSteps intermediate hbefore hp
  · have hlast : prefixSteps = steps + 1 := by omega
    subst prefixSteps
    have heq := trace_same_length_unique hp
      (StructuredCalls.compiled_halt_trace heval inputStack outputStack)
    rw [heq]
    have hend := hsource steps (b.withPC (some (StructuredCalls.exitAddress command))) le_rfl
      (StructuredCalls.compiled_trace heval inputStack outputStack)
    exact hend

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- On an actual ambient assignment, extraction followed by expansion and
overlay changes precisely the selected head coordinates. -/
theorem overlay_selected (mask current baseline : List Bool)
    (hc : mask.length = current.length) (hb : mask.length = baseline.length) :
    LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge mask (Restriction.selected true mask current)) mask baseline =
      LeafAssignmentMergeProgram.merge current mask baseline := by
  induction mask generalizing current baseline with
  | nil =>
      have he : current=[] := List.eq_nil_of_length_eq_zero hc.symm
      simp [he,Restriction.zeroMerge,Restriction.merge,LeafAssignmentMergeProgram.merge]
  | cons b mask ih =>
      cases current with
      | nil => simp at hc
      | cons x current =>
          cases baseline with
          | nil => simp at hb
          | cons y baseline =>
              cases b <;> simp [Restriction.zeroMerge,Restriction.merge,Restriction.selected,
                LeafAssignmentMergeProgram.merge,ih current baseline (by simpa using hc) (by simpa using hb)]

theorem overlay_ofFn {n : ℕ} (head current baseline : Fin n → Bool) :
    LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (List.ofFn head)
        (Restriction.selected true (List.ofFn head) (List.ofFn current)))
      (List.ofFn head) (List.ofFn baseline) =
      List.ofFn (fun v => if head v then current v else baseline v) := by
  rw [overlay_selected _ _ _ (by simp) (by simp),LeafAssignmentMergeProgram.merge_ofFn]

end Overlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram


open CommandRegisterFrames

/-- Caller flags above the sixteen-register cache bank survive every actual
prefix, including all guarded calls and clearing steps. -/
theorem command_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) : i ∉ writes command := by
  have hout : ¬ ∃ j, FactorAssignmentProgram.localRegister j = i := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    have := j.isLt
    omega
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  have hclear (ports : List (Fin 896)) : i ∉ writes (clearBank ports) :=
    not_mem_liftCommand _ _ _ _ _ i hout
  have hsetup : i ∉ writes FactorAssignmentProgram.setup :=
    not_mem_liftCommand _ _ _ _ _ i hout
  have union_not_mem {s t : Finset (Fin 40)} (hs : i ∉ s) (ht : i ∉ t) : i ∉ s ∪ t := by
    simpa only [Finset.mem_union, not_or] using And.intro hs ht
  have hoverwrite (src dst : Fin 896) : i ∉ writes (QueryTupleVisitor.overwrite src dst) :=
    union_not_mem (not_mem_clearProgram dst 0 1 i h0 h1)
      (not_mem_copyProgram src dst 841 0 1 i h0 h1)
  exact union_not_mem (hclear entryPorts)
    (union_not_mem hsetup (union_not_mem (hoverwrite 69 852)
      (union_not_mem (hoverwrite 703 869) (hclear lowPorts))))

theorem command_register_frame {steps : ℕ} {a b : Data}
    (he : Eval command steps a b) (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  eval_register_frame he i (command_not_mem_writes i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

/-- Restrict a prefix certificate to a shorter execution prefix. -/
theorem PrefixBound.monoSteps {command : Code} {steps fewer B : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hfewer : fewer ≤ steps) :
    PrefixBound command fewer a B :=
  ⟨fun q z hq hz i => h.bound q z (hq.trans hfewer) hz i⟩

theorem prefix_seq {first second : Code} {n m B : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval second m b c)
    (hp : PrefixBound first n a B) (hq : PrefixBound second m b B) :
    PrefixBound (.seq first second) (n+m) a B := by
  constructor
  exact StructuredSpace.sequence_stack_bound hf hs 838 838 hp.bound hq.bound
    (compiled (.seq first second) 838 838) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 838 838)

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryRepresentativeFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafAssignmentMergeProgram

theorem run_ofFn_reverse (mask : ℕ → List Bool) (base : ℕ) {r : ℕ}
    (words : Fin r → List Bool) (baseline : List Bool) :
    run mask base (List.ofFn words).reverse baseline =
      (List.finRange r).reverse.foldl (fun acc g =>
        merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + g.val)) (words g))
          (mask (base + g.val)) acc) baseline := by
  induction r generalizing baseline with
  | zero => simp [run]
  | succ r ih =>
    have hrange : List.finRange (r+1) =
        (List.finRange r).map Fin.castSucc ++ [Fin.last r] := by
      change List.ofFn (fun i : Fin (r+1) => i) = _
      rw [List.ofFn_succ', List.concat_eq_append]
      change List.ofFn (fun i : Fin r => i.castSucc) ++ [Fin.last r] =
        (List.ofFn (fun i : Fin r => i)).map Fin.castSucc ++ [Fin.last r]
      rw [List.map_ofFn]
      rfl
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, run,
      List.length_reverse, List.length_ofFn]
    rw [ih, hrange]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, ← List.map_reverse, List.foldl_map, Fin.val_last]
    rfl

theorem foldl_selected_ofFn {n : ℕ} {G : Type*} (heads : List G)
    (mask current : G → Fin n → Bool) (baseline : Fin n → Bool) :
    heads.foldl (fun acc g => merge
        (HighIncidenceProgram.Restriction.zeroMerge (List.ofFn (mask g))
          (HighIncidenceProgram.Restriction.selected true (List.ofFn (mask g))
            (List.ofFn (current g)))) (List.ofFn (mask g)) acc) (List.ofFn baseline) =
      heads.foldl (fun acc g => merge (List.ofFn (current g)) (List.ofFn (mask g)) acc)
        (List.ofFn baseline) := by
  induction heads generalizing baseline with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, HighQueryAdapter.Overlay.overlay_ofFn, merge_ofFn]
    exact ih _

/-- The actual reversed frame order and decreasing address reconstruct every
free head in its original ambient coordinates. Fixed-high bits and neutral
empty heads are retained. -/
theorem representative_words {n r : ℕ} (mask : ℕ → List Bool) (base : ℕ)
    (H : Finset (Fin n)) (high : H → Bool) (head : Fin n → Fin r)
    (reps : ∀ g, Moments.Head (fun v : {v : Fin n // v ∉ H} => head v.val) g → Bool)
    (words : Fin r → List Bool) (current : Fin r → Fin n → Bool)
    (hmask : ∀ g : Fin r, mask (base + g.val) =
      List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g)))
    (hwords : ∀ g : Fin r, words g = HighIncidenceProgram.Restriction.selected true
      (mask (base + g.val)) (List.ofFn (current g)))
    (hcurrent : ∀ g (v : Fin n) (hv : v ∉ H) (hg : head v = g),
      current g v = reps g ⟨⟨v,hv⟩,hg⟩) :
    run mask base (List.ofFn words).reverse
        (List.ofFn (HighIncidence.glue H high (fun _ => false))) =
      List.ofFn (HighIncidence.glue H high
        (Moments.assemble (fun v : {v : Fin n // v ∉ H} => head v.val) reps)) := by
  rw [run_ofFn_reverse]
  have hf : (fun (acc : List Bool) (g : Fin r) =>
      merge (HighIncidenceProgram.Restriction.zeroMerge (mask (base + g.val)) (words g))
        (mask (base + g.val)) acc) =
      (fun acc g => merge
        (HighIncidenceProgram.Restriction.zeroMerge
          (List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g)))
          (HighIncidenceProgram.Restriction.selected true
            (List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g)))
            (List.ofFn (current g))))
        (List.ofFn (fun v : Fin n => decide (v ∉ H ∧ head v = g))) acc) := by
    funext acc g
    rw [hwords g, hmask g]
  rw [hf, foldl_selected_ofFn]
  exact HeadRepresentativeSemantics.representative_heads H high head reps
    (List.finRange r).reverse (fun g => by simp) current
    (fun g _ v hv hg => hcurrent g v hv hg)

/-- A suffix of the reversed frame list determines the original head address. -/
theorem reverse_word_address {r : ℕ} (words : Fin r → List Bool)
    (pre : List (List Bool)) (word : List Bool) (rest : List (List Bool))
    (h : (List.ofFn words).reverse = pre ++ word :: rest) :
    ∃ i : Fin r, i.val = rest.length ∧ words i = word := by
  have hlen : r = pre.length + (rest.length + 1) := by
    have hh := congrArg List.length h
    simpa only [List.length_reverse,List.length_ofFn,List.length_append,
      List.length_cons] using hh
  have hi : rest.length < r := by omega
  refine ⟨⟨rest.length,hi⟩,rfl,?_⟩
  have hr : List.ofFn words = rest.reverse ++ word :: pre.reverse := by
    have hh := congrArg List.reverse h
    simpa only [List.reverse_reverse,List.reverse_append,List.reverse_cons,
      List.append_assoc,List.singleton_append] using hh
  have he := congrArg (fun xs : List (List Bool) => xs[rest.length]?) hr
  rw [List.getElem?_append_right (by simp)] at he
  simpa only [List.getElem?_ofFn, dite_eq_left hi, List.length_reverse, Nat.sub_self,
    List.getElem?_cons_zero, Option.some.injEq] using he

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace QueryMasterFrame

theorem trans {a b c : Data} (hab : QueryMasterFrame a b) (hbc : QueryMasterFrame b c) :
    QueryMasterFrame a c := ⟨fun i hi => (hbc.word i hi).trans (hab.word i hi)⟩

end QueryMasterFrame

/-- Actual cache initialization changes no retained query input. -/
theorem initialized_masterFrame {a b : Data} {n width d u J : ℕ}
    {one : RingProgram.Code (Word width) d}
    (h : QueryTupleInit.Initialized a b (n:=n) one u J) : QueryMasterFrame a b := by
  constructor
  intro i hi
  apply h.frame i
  simp only [masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage


/-- The query snapshot contains every actual loader master. -/
theorem source_master_queryMaster (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i∈QueryTupleState.masterPorts := by
  simp only [SignatureHeadLoader.masters, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem source_frame_of_queryFrame (base : LeafHeadSetupProgram.Data)
    (a b : State 40 896)
    (ha : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : QueryTupleState.QueryMasterFrame a b) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  exact (hf.word (SignatureHeadLoader.lowStacks i) (source_master_queryMaster i hi)).trans
    (ha.stored i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact physical words for the emitted numeric head representatives. These
are proof-level coordinate maps; the executable cursor retains only its bounded
binary word and uses the existing native selected-coordinate scan. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
open Classical
open OAI.Algorithms.SubexponentialSAT.SqrtLog

open BucketTupleProgram.Concrete HeadIdentifierProgram

theorem ambientAssignment_head {n r : ℕ} (H : Finset (Fin n)) (head : Fin n → Fin r)
    (g : Fin r) (x : Moments.Head (fun v : {v : Fin n // v∉H} => head v.val) g → Bool)
    (v : Fin n) (hv : v∉H) (hg : head v=g) :
    ambientAssignment H head g x v=x ⟨⟨v,hv⟩,hg⟩ := by
  simp only [ambientAssignment, dite_eq_left hv, dite_eq_left hg]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource

private theorem baselinePrefix_le (s : ProducedSource) (B : ℕ) :
    max (896*B+baselineCost s B) (914*B+18) ≤
      2400*(B+1)+baselineCost s B := by
  apply max_le
  · omega
  · omega


/-- The stored representative frames already pay for the parser's payload
mass; the proof does not construct any assignment enumeration. -/
theorem frame_word_mass (words : List (List Bool)) :
    (words.map List.length).sum ≤ (suspendedFrames words).length := by
  induction words with
  | nil => simp [suspendedFrames]
  | cons word rest ih =>
    simp only [List.map_cons,List.sum_cons,suspendedFrames,List.flatMap_cons,
      List.length_append,Encoding.length_frame,List.length_reverse] at *
    omega


open scoped BigOperators


/-- The literal source certificate identifies the actual mask emitted at each
address with the original free head fiber. -/
theorem facts_mask (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) (g : Fin s.input.r) :
    mask s (s.base+g.val)=
      List.ofFn (fun v : Fin s.input.n => decide (v∉H ∧ head s.input.node v=g)) := by
  apply congrArg List.ofFn
  funext v
  apply Bool.eq_iff_iff.mpr
  have hv : v.val < s.input.n := v.isLt
  simpa only [ProducedSource.base,HeadIdentifierProgram.chosenIds,List.mem_filter,List.mem_range,
    hv,true_and,decide_eq_true_eq,exists_prop] using facts.selected g v

private theorem baselinePrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) :
    max (896*P+baselineCost s P) (914*P+18) ≤ visitorSpace s q P B := by
  calc
    max (896*P+baselineCost s P) (914*P+18) ≤
        2400*(P+1)+baselineCost s P := baselinePrefix_le s P
    _ ≤ 2400*(P+1)+baselineCost s P+
        QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P :=
      Nat.le_add_right _ _
    _ ≤ visitorSpace s q P B := Nat.le_max_left _ _

private theorem evaluationSpace_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) :
    evaluationSpace s q P B ≤ visitorSpace s q P B :=
  Nat.le_max_right _ _

private theorem evaluationPrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) :
    max (evaluationSpace s q P B) (914*P+18) ≤ visitorSpace s q P B := by
  apply max_le
  · exact evaluationSpace_le_visitorSpace s q P B
  · exact (Nat.le_max_right (896*P+baselineCost s P) (914*P+18)).trans
      (baselinePrefix_le_visitorSpace s q P B)

private theorem initialPrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B steps : ℕ)
    (hsteps : steps ≤ 1500*(P+1)) :
    896*P+steps ≤ visitorSpace s q P B := by
  calc
    896*P+steps ≤ 896*P+1500*(P+1) := Nat.add_le_add_left hsteps _
    _ ≤ 2400*(P+1) := by omega
    _ ≤ 2400*(P+1)+baselineCost s P := Nat.le_add_right _ _
    _ ≤ 2400*(P+1)+baselineCost s P+
        QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P :=
      Nat.le_add_right _ _
    _ ≤ visitorSpace s q P B := Nat.le_max_left _ _

private theorem finishPrefix_le_visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B steps : ℕ)
    (hsteps : steps+1 ≤
      QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+16*P+25) :
    896*P+steps ≤ visitorSpace s q P B := by
  let budget := QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P
  have hstep : steps ≤ budget+16*P+25 := (Nat.le_succ steps).trans hsteps
  calc
    896*P+steps ≤ 896*P+(budget+16*P+25) := Nat.add_le_add_left hstep _
    _ = (912*P+25)+budget := by omega
    _ ≤ 2400*(P+1)+budget := Nat.add_le_add_right (by omega) _
    _ ≤ (2400*(P+1)+baselineCost s P)+budget :=
      Nat.add_le_add_right (Nat.le_add_right _ _) _
    _ ≤ visitorSpace s q P B := Nat.le_max_left _ _

/-- The actual fixed visitor first reconstructs every representative, then
multiplies every restricted head sum, and finally adds one completed readout.
All execution witnesses are produced by the concrete commands in this proof. -/
theorem visitor_run_oai (s : ProducedSource) {d M P S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M P S Z B s.bound width)
    (reps : ∀ g, Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool)
    (hbalanced : ∀ g : Fin s.input.r,
      HeadIdentifierProgram.count (HeadIdentifierProgram.predicate s.input.rows s.input.low
        (s.base+g.val)) s.input.n ≤ height)
    (a : Data) {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q s.input.node H high E U M a)
    (hm : PairAccumulatorMeaning q pairValue a) (ha : WordBound P a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames (List.ofFn (fun g =>
      QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps)).reverse)
    (haddress : a.stacks 845=unary (s.base+s.input.r)) (hcurrent : a.stacks 838=[]) :
    ∃ steps b, Eval QueryVisitorProgram.visitor steps a b ∧
      QueryReady q s.input.node H high E U M b ∧
      PairAccumulatorMeaning q (pairValue+Dense.readout (∏ g : Fin s.input.r,
        QueryVisitorHead.headValue q s.input.node H E U high owner head g reps
          (QueryVisitorHead.factorIds s.input g))) b ∧
      QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      (∀ i∈SignatureTupleProgram.currentHeadPorts,b.stacks i=[]) ∧
      steps+1 ≤ visitorCost s q P S Z B height ∧
      QueryExecution.PrefixBound QueryVisitorProgram.visitor (steps+1) a (visitorSpace s q P B) := by
  let words := fun g => QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g reps
  let frameWords := (List.ofFn words).reverse
  obtain ⟨ni,a1,hi,hr1,hm1,hinit,hb1,hci,entries,hbytes,hgood,hunit⟩ :=
    QueryTupleState.initialize_run hr hm ha caps.cache
  have hv1 : DenseWord q 852 1 a1 := ⟨entries,hbytes,hgood,hunit⟩
  have hf1:=initialized_masterFrame hinit
  have hs1:=source_frame_of_queryFrame s.masters a a1 hs hf1
  have hbaseline1 : a1.stacks 869=List.ofFn
      (HighIncidence.glue H high (fun _ => false)) := hinit.baseline.trans hr.highBits
  have hlen1 : (a1.stacks 869).length=s.input.n := by rw [hbaseline1,List.length_ofFn]
  have hshape : ∀ pre word rest,frameWords=pre++word::rest →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (s.base+rest.length)).length := by
    intro pre word rest hsplit
    obtain ⟨g,hg,he⟩:=QueryRepresentativeFold.reverse_word_address words pre word rest hsplit
    rw [←he]
    change (List.ofFn _).length=_
    rw [List.length_ofFn]
    change (HeadIdentifierProgram.chosenIds
      (HeadIdentifierProgram.predicate s.input.rows s.input.low (s.base+g.val)) s.input.n).length=_
    rw [hg]
    rfl
  obtain ⟨nb,a2,hbase,hr2,hm2,hv2,hf2,hb2,hcursor2,h841,hbaseline2,_,hports2,hregs2,hcb,hpb⟩ :=
    baseline_pass s s.base frameWords hr1 hm1 hv1 hb1 hs1
      ((hinit.frame 837 (by decide)).trans hreps)
      (by simpa only [frameWords,List.length_reverse,List.length_ofFn] using
        (hinit.frame 845 (by decide)).trans haddress)
      ((hinit.frame 838 (by decide)).trans hcurrent) hinit.scratch hlen1 hshape caps.load
  have hfullbase : a2.stacks 869=List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.input.node v.val) reps)) := by
    rw [hbaseline2,hbaseline1]
    exact QueryRepresentativeFold.representative_words (mask s) s.base H high (head s.input.node)
      reps words (fun g => SignatureTupleWords.ambientAssignment H (head s.input.node) g (reps g))
      (facts_mask s q H owner head facts) (fun g => representativeWord_selected s q H owner head facts g reps)
      (fun g v hv hg => SignatureTupleWords.ambientAssignment_head H (head s.input.node) g (reps g) v hv hg)
  have hs2:=source_frame_of_queryFrame s.masters a1 a2 hs1 hf2
  have hreps2 : a2.stacks 837=suspendedFrames frameWords :=
    (hports2 837 (by decide)).trans ((hinit.frame 837 (by decide)).trans hreps)
  have haddress2 : a2.stacks 845=unary (s.base+s.input.r) :=
    (hports2 845 (by decide)).trans ((hinit.frame 845 (by decide)).trans haddress)
  obtain ⟨ne,a3,he,hr3,hm3,hv3,hf3,hb3,_,_,_,hports3,hregs3,hce,hpe⟩ :=
    evaluation_pass s q H E U high owner head facts caps reps hbalanced a2 hr2 hm2 hv2 hb2
      hs2 hreps2 haddress2 hcursor2.current h841 hfullbase
  obtain ⟨product,hprodBytes,hprodGood,hprodValue⟩:=hv3.entries
  obtain ⟨nf,b,hf,hrb,hmb,hbb,hff,hcurrentb,hframe,hregs,hcf⟩ :=
    QueryTupleState.finish hr3 hm3 product hprodGood hprodBytes hb3 caps.multiply
  have whole : Eval QueryVisitorProgram.visitor (ni+(nb+(ne+nf))) a b :=
    hi.seq (hbase.seq (he.seq hf))
  have hmass : (frameWords.map List.length).sum ≤ P :=
    (frame_word_mass _).trans (by rw [←hreps];exact ha 837)
  have htime : ni+(nb+(ne+nf))+1 ≤ visitorCost s q P S Z B height := by
    dsimp only [frameWords] at hmass
    simp only [frameWords,List.length_reverse,List.length_ofFn] at hcb
    unfold visitorCost
    have hd : (baselineCost s P+evaluationCost s q P S Z B height+20)*s.input.r =
        (baselineCost s P+10)*s.input.r+(evaluationCost s q P S Z B height+10)*s.input.r := by ring
    rw [hd]
    omega
  let D := visitorSpace s q P B
  have hpi : QueryExecution.PrefixBound QueryTupleInit.command ni a D :=
    (QueryExecution.prefix_local QueryTupleInit.command ni P a ha).mono
      (initialPrefix_le_visitorSpace s q P B ni hci)
  have hpb' : QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.baselineHead) nb a1 D := by
    exact (hpb.monoSteps (Nat.le_succ nb)).mono (baselinePrefix_le_visitorSpace s q P B)
  have hpe' : QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.evaluateHead) ne a2 D := by
    exact (hpe.monoSteps (Nat.le_succ ne)).mono (evaluationPrefix_le_visitorSpace s q P B)
  have hpf : QueryExecution.PrefixBound QueryExecution.TupleEnd.command nf a3 D :=
    (QueryExecution.prefix_local QueryExecution.TupleEnd.command nf P a3 hb3).mono
      (finishPrefix_le_visitorSpace s q P B nf hcf)
  have hpwhole:=QueryExecution.prefix_seq hi (hbase.seq (he.seq hf)) hpi
    (QueryExecution.prefix_seq hbase (he.seq hf) hpb' (QueryExecution.prefix_seq he hf hpe' hpf))
  refine ⟨_,b,whole,hrb,?_,hf1.trans (hf2.trans (hf3.trans hff)),hbb,?_,?_,hcurrentb,htime,?_⟩
  · simpa only [hprodValue,one_mul] using hmb
  · intro i hi'
    have hn : 128 ≤ i.val ∧ i∉currentHeadPorts ∧ i≠851 ∧ i≠852 ∧ i∉QueryTupleInit.changed := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
      rcases hi' with rfl|rfl|rfl|rfl
      all_goals decide
    exact (hframe i hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1).trans
      ((hports3 i hi').trans ((hports2 i hi').trans (hinit.frame i hn.2.2.2.2)))
  · intro i hi'
    exact (hregs i hi').trans ((hregs3 i hi').trans ((hregs2 i hi').trans
      (QueryTupleInit.command_register_frame hi i hi')))
  · constructor
    exact StructuredSpace.compiled_halt_stack_bound whole 838 838 hpwhole.bound


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run_oai
