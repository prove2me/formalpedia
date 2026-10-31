-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:48:12.863665+00:00
-- url     : https://prove2.me/submissions/2e6360e3-6757-48f1-a84a-fdd07c62c699

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorHead_head_multiply_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram_prepare_run

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

open BitProgram

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

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

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem headOrder_ids (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.headIds (headOrder p n)=chosenIds p n := by
  simp [HeadScatterProgram.headIds, headOrder, count]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

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


theorem selected_true_length (mask xs : List Bool) (hlen : mask.length = xs.length) :
    (selected true mask xs).length = Subexp.PaddedCompletion.trueCount mask := by
  induction mask generalizing xs with
  | nil => simp [selected, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful]
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have ht : mask.length = xs.length := by simpa using hlen
          cases b <;> simp [selected, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful] at * <;> exact ih xs ht

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

theorem selected_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    Restriction.selected true (xs.map p) (xs.map x) = (xs.filter p).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [Restriction.selected, hp, ih]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

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
open HeadIdentifierProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- The actual chosen-ID word fixes the ascending selection order. -/
theorem headOrder_stream (p : ℕ → Bool) (n : ℕ) :
    (List.finRange n).filter (fun v => p v.val)=List.ofFn (headOrder p n) := by
  apply (List.map_injective_iff.mpr (Fin.val_injective : Function.Injective (Fin.val (n:=n))))
  rw [List.map_ofFn]
  change _=HeadScatterProgram.headIds (headOrder p n)
  rw [headOrder_ids]
  simpa only [List.map_coe_finRange,chosenIds,Function.comp_def] using
    (List.filter_map (f:=(Fin.val : Fin n → ℕ)) (p:=p) (l:=List.finRange n)).symm

/-- The native selected-bit scan emits exactly the current head's ambient
coordinates in the already emitted headOrder, including the empty head. -/
theorem selected_headOrder (p : ℕ → Bool) (n : ℕ) (x : Fin n → Bool) :
    Restriction.selected true (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn x) =
      List.ofFn (fun i => x (headOrder p n i)) := by
  rw [List.ofFn_eq_map,List.ofFn_eq_map,Order.selected_map,headOrder_stream,List.map_ofFn]
  rfl

/-- The physical selected-mask population is the actual emitted head width. -/
theorem headOrder_highCount (p : ℕ → Bool) (n : ℕ) :
    Restriction.highCount (List.ofFn (fun v : Fin n => p v.val))=count p n := by
  have hh := Restriction.selected_true_length (List.ofFn (fun v : Fin n => p v.val))
    (List.ofFn (fun _ : Fin n => true)) (by simp)
  rw [selected_headOrder,List.length_ofFn] at hh
  exact hh.symm

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
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

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem result_frame (a : Data) (rf : Fin 4 → Bool) (i : Fin 896)
    (hi : i ∉ changed) : (result a rf).stacks i = a.stacks i := by
  have hn : ¬ ∃ j, stackMap j=i := by
    rintro ⟨j,rfl⟩
    fin_cases j <;> simp [stackMap,changed] at hi
  rw [show (result a rf).stacks i = (copied a).stacks i from
    embedState_stack_frame regs stackMap (copied a) _ i hn]
  have h1 : i ≠ 879 := by intro he; subst i; simp [changed] at hi
  have h2 : i ≠ 878 := by intro he; subst i; simp [changed] at hi
  simp [copied,copyStacks,h1,h2]

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi


@[simp] theorem prepared_E (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 867=Restriction.selected true (a.stacks 670) (a.stacks 858) := by
  rw [result_E,reset_frame a 670 (by decide),reset_frame a 858 (by decide)]

@[simp] theorem prepared_H (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 868=List.replicate (Restriction.highCount (a.stacks 670)) true := by
  rw [result_H,reset_frame a 670 (by decide)]

theorem prepared_frame (a : Data) (rf : Fin 4 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result (resetState a) rf).stacks i=a.stacks i :=
  (result_frame (resetState a) rf i hi).trans (reset_frame a i hi)

end NativeHeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
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

theorem prefix_seq {first second : Code} {n m B : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval second m b c)
    (hp : PrefixBound first n a B) (hq : PrefixBound second m b B) :
    PrefixBound (.seq first second) (n+m) a B := by
  constructor
  exact StructuredSpace.sequence_stack_bound hf hs 838 838 hp.bound hq.bound
    (compiled (.seq first second) 838 838) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 838 838)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeyNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# One full integer signature on the leaf ABI

All port numbers here are leaf-local. The actual key-only machine preserves
the assignment, shifted matrix and every unrelated caller word; it has no
predecessor, countdown, or signature-table input.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

open BitProgram StructuredCalls AttainedSignatureProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem Ready.projection {a : State 40 896} {W bits : List Bool}
    {rows : List (List (List Bool))} (ready : Ready a W bits rows) :
    projectState registers stackPorts a = state (a.regs ∘ registers) W bits rows [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change a.stacks (stackPorts i) = _
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h12 : i = 12
  · subst i; exact ready.assignment
  by_cases h14 : i = 14
  · subst i; exact ready.output
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  rw [ready.scratch i h0 h12 h14 h15]
  fin_cases i <;> simp_all

theorem output_stacks (a : State 40 896) (out : Fin 8 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) (ready : Ready a W bits rows) :
    (outputState a out W bits rows).stacks =
      Function.update a.stacks (stackPorts 14) (signatureValue W bits rows) := by
  have hlocal : (state out W bits rows (signatureValue W bits rows)).stacks =
      Function.update (state (a.regs ∘ registers) W bits rows []).stacks 14
        (signatureValue W bits rows) := by
    funext i
    fin_cases i <;> simp [state]
  have hemb : Function.extend stackPorts
      (state (a.regs ∘ registers) W bits rows []).stacks a.stacks = a.stacks := by
    change (embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows [])).stacks = _
    rw [← ready.projection, embedState_project _ _ _ registers.injective stackPorts.injective]
  change Function.extend stackPorts _ a.stacks = _
  rw [hlocal, ProgramLinking.extend_update stackPorts.injective, hemb]

theorem output_register_frame (a : State 40 896) (out : Fin 8 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) (j : Fin 40) (hj : 8 ≤ j.val) :
    (outputState a out W bits rows).regs j = a.regs j := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  dsimp [registers] at hv
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid setup for one visited signature head. The physical key workspace,
old master words and selector outputs are cleared by the command itself. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter QueryTupleVisitor
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem reset_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ cleared) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i cleared a.stacks hi

/-- Only the concrete immutable input words are premises; scratch and output
readiness are established by the paid reset. -/
theorem reset_ready (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words)) :
    SignatureKeyNative.Ready (resetState a) W bits rows := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (reset_frame a 141 (by decide)).trans hW
  · exact (reset_frame a 838 (by decide)).trans hbits
  · exact BankRoutines.clearBankStacks_mem 866 cleared a.stacks (by decide)
  · exact (reset_frame a 847 (by decide)).trans hrows
  · intro i h0 h12 h14 h15
    apply BankRoutines.clearBankStacks_mem
    fin_cases i <;> first | contradiction | decide

theorem masters_stacks (a : State 40 896) :
    (mastersState a).stacks = Function.update
      (Function.update (Function.update a.stacks 864 (a.stacks 141)) 865 (a.stacks 847))
      175 (a.stacks 671) := by
  rw [mastersState, overwriteState_stacks 671 175 (by decide),
    overwriteState_stacks 847 865 (by decide),
    overwriteState_stacks 141 864 (by decide)]
  simp

theorem result_frame (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words))
    (i : Fin 896) (hi : i ∉ cleared) (h864 : i ≠ 864) (h865 : i ≠ 865) (h175 : i ≠ 175)
    (hselect : i ∉ NativeHeadSelect.changed) :
    (result a kr sr W bits rows).stacks i = a.stacks i := by
  have h866 : i ≠ 866 := by intro h; subst i; exact hi (by decide)
  rw [result, NativeHeadSelect.prepared_frame _ sr i hselect, masters_stacks,
    Function.update_of_ne h175, Function.update_of_ne h865, Function.update_of_ne h864,
    SignatureKeyNative.output_stacks _ kr W bits rows (reset_ready a W bits rows hW hbits hrows),
    show SignatureKeyNative.stackPorts 14 = 866 from rfl,
    Function.update_of_ne h866, reset_frame a i hi]

/-- All DFS flags and every register outside the key routine's eight-register
bank survive the complete preparation. No register-save service is assumed. -/
theorem result_register_frame (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) (j : Fin 40) (hj : 8 ≤ j.val) :
    (result a kr sr W bits rows).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
  have ho (src dst : Fin 896) (b : State 40 896) :
      (overwriteState src dst b).regs j = b.regs j := by
    change readRegs (readRegs b.regs 0 1 none) 0 1 none j = b.regs j
    rw [readRegs_frame _ 0 1 j none h0 h1, readRegs_frame _ 0 1 j none h0 h1]
  have hs (b : State 40 896) : (NativeHeadSelect.result b sr).regs j = b.regs j := by
    have hn : ¬ ∃ i, NativeHeadSelect.regs i = j := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      have hil := i.isLt
      dsimp [NativeHeadSelect.regs] at hv
      omega
    rw [NativeHeadSelect.result, embedState_register_frame _ _ _ _ j hn]
    change readRegs (readRegs b.regs 0 1 none) 0 1 none j = b.regs j
    rw [readRegs_frame _ 0 1 j none h0 h1, readRegs_frame _ 0 1 j none h0 h1]
  rw [result, hs]
  change readRegs (mastersState _).regs 0 1 none j = a.regs j
  rw [readRegs_frame _ 0 1 j none h0 h1, mastersState, ho, ho, ho,
    SignatureKeyNative.output_register_frame _ kr W bits rows j hj]
  exact readRegs_frame a.regs 0 1 j none h0 h1

/-- The masters used by the subsequent restricted head sum are produced by
the same run, while the actual ambient mask and correction word are preserved. -/
theorem result_words (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words)) :
    let out := result a kr sr W bits rows
    out.stacks 864 = W ∧ out.stacks 865 = words (rows.map words) ∧
      out.stacks 866 = signatureValue W bits rows ∧
      out.stacks 867 = OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true
        (a.stacks 670) (a.stacks 858) ∧
      out.stacks 868 = List.replicate
        (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670)) true := by
  let keyed := SignatureKeyNative.outputState (resetState a) kr W bits rows
  have hks : keyed.stacks = Function.update (resetState a).stacks 866
      (signatureValue W bits rows) :=
    SignatureKeyNative.output_stacks _ kr W bits rows (reset_ready a W bits rows hW hbits hrows)
  have hm : (mastersState keyed).stacks = Function.update
      (Function.update (Function.update (Function.update (resetState a).stacks 866 (signatureValue W bits rows))
        864 W) 865 (words (rows.map words))) 175 (a.stacks 671) := by
    rw [masters_stacks, hks]
    simp only [Function.update_of_ne (by decide : (141 : Fin 896) ≠ 866),
      Function.update_of_ne (by decide : (847 : Fin 896) ≠ 866),
      Function.update_of_ne (by decide : (671 : Fin 896) ≠ 866),
      reset_frame a 141 (by decide), reset_frame a 847 (by decide),
      reset_frame a 671 (by decide), hW, hrows]
  have hm670 : (mastersState keyed).stacks 670 = a.stacks 670 := by
    rw [hm]
    simp only [Function.update_of_ne (by decide : (670 : Fin 896) ≠ 175),
      Function.update_of_ne (by decide : (670 : Fin 896) ≠ 865),
      Function.update_of_ne (by decide : (670 : Fin 896) ≠ 864),
      Function.update_of_ne (by decide : (670 : Fin 896) ≠ 866), reset_frame a 670 (by decide)]
  have hm858 : (mastersState keyed).stacks 858 = a.stacks 858 := by
    rw [hm]
    simp only [Function.update_of_ne (by decide : (858 : Fin 896) ≠ 175),
      Function.update_of_ne (by decide : (858 : Fin 896) ≠ 865),
      Function.update_of_ne (by decide : (858 : Fin 896) ≠ 864),
      Function.update_of_ne (by decide : (858 : Fin 896) ≠ 866), reset_frame a 858 (by decide)]
  dsimp only
  unfold result
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [NativeHeadSelect.prepared_frame _ sr 864 (by decide), hm]
    simp
  · rw [NativeHeadSelect.prepared_frame _ sr 865 (by decide), hm]
    simp
  · rw [NativeHeadSelect.prepared_frame _ sr 866 (by decide), hm]
    simp
  · rw [NativeHeadSelect.prepared_E, hm670, hm858]
  · rw [NativeHeadSelect.prepared_H, hm670]

/-- The loader's selected factor records are installed once for the complete
head rescan, in the exact physical bank consumed by the factor loop. -/
theorem result_factors (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words)) :
    (result a kr sr W bits rows).stacks 175 = a.stacks 671 := by
  rw [result, NativeHeadSelect.prepared_frame _ sr 175 (by decide), masters_stacks,
    Function.update_self, SignatureKeyNative.output_stacks _ kr W bits rows
      (reset_ready a W bits rows hW hbits hrows),
    show SignatureKeyNative.stackPorts 14 = 866 from rfl,
    Function.update_of_ne (by decide : (671 : Fin 896) ≠ 866), reset_frame a 671 (by decide)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed two-pass visit of one emitted attained-signature tuple. The first
pass reconstructs the entire ambient representative assignment; the second
rescans the assignments in each head against those fixed foreign values.
Every concrete subroutine is fixed here, without an evaluator argument. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram

open BitProgram StructuredCalls
noncomputable section

theorem evaluateLoadedHead_eval {n m : ℕ} {a b c : State 40 896}
    (hp : Eval SignatureHeadPrepare.command n a b)
    (he : Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
      QueryAssembler.TupleMultiply.command) m b c) :
    Eval evaluateLoadedHead (n + m) a c := by
  unfold evaluateLoadedHead
  exact hp.seq he

theorem evaluateLoadedHead_prefix {n m B : ℕ} {a b c : State 40 896}
    (hp : Eval SignatureHeadPrepare.command n a b)
    (he : Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
      QueryAssembler.TupleMultiply.command) m b c)
    (hpp : QueryExecution.PrefixBound SignatureHeadPrepare.command n a B)
    (hep : QueryExecution.PrefixBound
      (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) m b B) :
    QueryExecution.PrefixBound evaluateLoadedHead (n + m) a B := by
  unfold evaluateLoadedHead
  exact QueryExecution.prefix_seq hp he hpp hep

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorHead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete one-head visitor composes its actual loader, paid key setup,
restricted head rescan and tuple multiplication. Exponential work is kept
separate from the reusable boundary and all-prefix storage bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram
open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage
open scoped BigOperators
noncomputable section

private theorem retained_head (i : Fin 896) (hi : i∈retainedPorts) :
    i∈HeadSumNative.retainedPorts := by
  simp only [retainedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

private theorem control_retained (i : Fin 896) (hi : i∈controlPorts) :
    i∈retainedPorts := by
  simp only [controlPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

private theorem control_prepare (i : Fin 896) (hi : i∈controlPorts) :
    i∉SignatureHeadPrepare.cleared ∧ i≠864 ∧ i≠865 ∧ i≠175 ∧
      i∉HighQueryAdapter.NativeHeadSelect.changed := by
  simp only [controlPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- Paid key preparation installs the complete actual matrix, correction
mask and factor stream before the fixed head rescan and multiplication. -/
theorem prepare_head_multiply_run_oai {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
          ((chosenIds pick n).get i))
    (ids : List ℕ) (a : HeadSumProgram.Data)
    (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length  ≤  P)
    (hshape : a.stacks 651 = List.replicate (count pick n) false)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
    (hW : a.stacks 141 = W)
    (hmatrix : a.stacks 847 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hbits : a.stacks 838 =
      List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
    (hids : a.stacks 671 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hcount : count pick n+1  ≤  P) (hrows : q.ps.length  ≤  P)
    (hcoeff : ∀ j i, (c j i).length  ≤  P)
    (hcache : 4*M+6  ≤  P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J  ≤  P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1  ≤  S)
    (hradius : q.p.R+1  ≤  Q) (width : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length  ≤  width)
    (hZ : 1  ≤  Z) (hP : P  ≤  Z) (hbit : q.bitWidth  ≤  Z)
    (hdegree : d * baseWidth 3 q.p.t  ≤  Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length  ≤  Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0  ≤  Z)
    (B : ℕ)
    (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
      HeadAcceptedCorrect.budget q P S Z  ≤  B)
    (hcounter : 9*(count pick n+1)+8  ≤  B)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hpair : PairAccumulatorMeaning q pairValue a)
    (htuple : DenseWord q 852 tupleValue a)
    (hmul : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P)
    (hprepare : 16*(W.length+count pick n+
      (OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
        ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words)).length)+
      AttainedSignatureProgram.cost W
        (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
          (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
        (List.ofFn (fun j => List.ofFn (c j)))+1 ≤ P)
    (hselect : 11*n+6 ≤ P) :
    ∃ steps b,
      Eval QueryVisitorProgram.evaluateLoadedHead steps a b ∧
      QueryReady q node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (tupleValue*headValue q node H E U high owner head g reps ids) b ∧
      b.stacks 853=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈controlPorts,b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ 100*P+200+sumBudget q P S Z B (count pick n)+multiplyBudget q P ∧
      QueryExecution.PrefixBound QueryVisitorProgram.evaluateLoadedHead steps a
        (max (996*P+200) (max B (896*P+multiplyBudget q P))) := by
  let bits := List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
    (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g))
  let rows := List.ofFn (fun j => List.ofFn (c j))
  have hrowlen : ∀ row∈rows,row.length=bits.length := by
    intro row hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    rw [List.length_ofFn]
    simp only [bits, List.length_ofFn]
    rfl
  have hlen : (a.stacks 670).length=(a.stacks 858).length := by
    rw [hmask,hq.outer]
    simp
  obtain ⟨np,kr,sr,hp,hq',hpair',htuple',hmasters,hbound,hptime,hpprefix⟩ :=
    QueryVisitorProgram.prepare_run hq hpair htuple ha W bits rows hW hbits hmatrix hrowlen hlen
      (by simpa only [bits, rows, List.length_ofFn, count] using hprepare)
      (by simpa only [hmask,List.length_ofFn] using hselect)
  let mid := SignatureHeadPrepare.result a kr sr W bits rows
  have hf (i : Fin 896) (hi : i∉SignatureHeadPrepare.cleared) (h864 : i≠864)
      (h865 : i≠865) (h175 : i≠175) (hsel : i∉HighQueryAdapter.NativeHeadSelect.changed) :
      mid.stacks i=a.stacks i :=
    SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hmatrix i hi h864 h865 h175 hsel
  obtain ⟨hW',hrows',hkey',hE',hH'⟩ :=
    SignatureHeadPrepare.result_words a kr sr W bits rows hW hbits hmatrix
  have hE'' : mid.stacks 867=HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩) := by
    simpa only [hmask,hq.outer,LeafWeightProgram.supportBits] using hE'
  have hH'' : mid.stacks 868=List.replicate (count pick n) true := by
    simpa only [hmask,HeadRepresentativeSemantics.headOrder_highCount] using hH'
  have hids' : mid.stacks 175=ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids) :=
    (SignatureHeadPrepare.result_factors a kr sr W bits rows hW hbits hmatrix).trans hids
  obtain ⟨nh,out,he,hqo,hpo,hproduct,hzeroout,hmframe,hout,hof,hregs,hcost,hprefix⟩ :=
    head_multiply_run q node H E U high owner head g pick hs reps W c hc ids mid hq' hbound
      ((hf 651 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hshape)
      ((hf 670 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmask)
      ((hf 869 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbase)
      hW' hrows' hkey' hE'' hH'' hids' hzero hcount hrows hcoeff hcache hcapacity hsize
      hradius width hwidth hZ hP hbit hdegree hhashScale hmarkScale B hlocal hcounter hpair' htuple' hmul
  have hpref : QueryExecution.PrefixBound SignatureHeadPrepare.command np a (996*P+200) :=
    ⟨fun elapsed z hle hz => hpprefix.bound elapsed z (by omega) hz⟩
  refine ⟨np+nh, out, QueryVisitorProgram.evaluateLoadedHead_eval hp he,
    hqo, hpo, hproduct, hzeroout, hmasters.trans hmframe, hout, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hc,h864,h865,h175,hs⟩ := control_prepare i hi
    exact (hof i (control_retained i hi)).trans (hf i hc h864 h865 h175 hs)
  · intro i hi
    exact (hregs i hi).trans (SignatureHeadPrepare.result_register_frame a kr sr W bits rows i (by omega))
  · omega
  · exact QueryVisitorProgram.evaluateLoadedHead_prefix hp he
      (hpref.mono (Nat.le_max_left _ _)) (hprefix.mono (Nat.le_max_right _ _))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run_oai
