-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:48:46.869838+00:00
-- url     : https://prove2.me/submissions/78e1e3bc-3176-4104-b34e-f436831d19e3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation_commit_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_run_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

theorem highOrder_val {n : ℕ} (H : Finset (Fin n)) (i : Fin H.card) :
    (highOrder H i).val = (highCoordinates H).get
      ⟨i.val, by simp⟩ := by
  rfl

theorem highOrder_stream {n : ℕ} (H : Finset (Fin n)) (x : Fin n → Bool) :
    List.ofFn (fun i : Fin H.card => x (highOrder H i)) = (highCoordinates H).map x := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp only [ highOrder_val, List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]

theorem selected_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    Restriction.selected true (xs.map p) (xs.map x) = (xs.filter p).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [Restriction.selected, hp, ih]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The supplied high-coordinate odometer with a fixed-width exact accumulator.
The residual callback is an actual command; its interface is discharged by the
assembled query program. No branch family is stored on any source stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram
open OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer
open OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
open scoped BigOperators

variable {R S : ℕ}

theorem freeOrder_val {n : ℕ} (H : Finset (Fin n)) (i : Fin (n - H.card)) :
    (freeOrder H i).val = (freeCoordinates H).get ⟨i.val, by simp⟩ := rfl

theorem freeOrder_stream {n : ℕ} (H : Finset (Fin n)) (x : Fin n → Bool) :
    List.ofFn (fun i => x (freeOrder H i)) = (freeCoordinates H).map x := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp only [freeOrder_val, List.get_eq_getElem, List.getElem_map,
      List.getElem_ofFn]

private theorem selected_false_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected false (xs.map p) (xs.map x) =
      (xs.filter (fun v => !(p v))).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected, hp, ih]

theorem freeFill_high_stream {n : ℕ} (H : Finset (Fin n)) (bits : Fin (n - H.card) → Bool) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true (descendingHighMask H)
      (List.ofFn (freeFill H bits)).reverse = List.replicate H.card false := by
  rw [← OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates_stream]
  unfold descendingHighMask
  rw [OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.selected_map]
  change (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.highCoordinates H).map (freeFill H bits) = _
  rw [← OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.highOrder_stream]
  simp

theorem freeFill_low_stream {n : ℕ} (H : Finset (Fin n)) (bits : Fin (n - H.card) → Bool) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected false (descendingHighMask H)
      (List.ofFn (freeFill H bits)).reverse = (List.ofFn bits).reverse := by
  rw [← OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates_stream]
  unfold descendingHighMask
  rw [selected_false_map]
  have hp : (fun v : Fin n => !(decide (v ∈ H))) = (fun v => decide (v ∉ H)) := by
    funext v
    simp
  rw [hp]
  change (((List.finRange n).reverse).filter (fun v => decide (v ∉ H))).map (freeFill H bits) = _
  rw [List.filter_reverse, List.map_reverse]
  change ((freeCoordinates H).map (freeFill H bits)).reverse = _
  rw [← freeOrder_stream]
  simp


namespace ZeroHigh
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

/-- An empty fixed-coordinate stream supplies zero in the actual source program. -/
theorem iteration (regs : Fin 4 → Bool) (b x : Bool)
    (mask low out : List Bool) :
    ∃ rf, Eval body 4
      (popped regs (b :: mask) [] (if b then low else x :: low) out)
      (popped rf mask [] low ((if b then false else x) :: out)) := by
  let a := popped regs (b :: mask) [] (if b then low else x :: low) out
  let item : Option Bool := if b then none else some x
  let r := readRegs (readRegs regs 0 1 (some b)) 2 3 item
  refine ⟨r, ?_⟩
  have hp : Eval pushBit 1 (state r mask [] low out)
      (state r mask [] low ((if b then false else x) :: out)) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.push (3 : Fin 4) 2)
      (state r mask [] low out))) using 1
    · rfl
    · apply congrArg (StructuredProgram.State.mk _)
      funext i
      fin_cases i <;> cases b <;> simp [r, item, state, readRegs,
        StructuredProgram.Atom.instr, execInstr]
  have hl : Eval loadBit 2 a (state r mask [] low out) := by
    cases b with
    | false =>
        apply Eval.ite_false (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 4) 2 3) a)) using 1
        all_goals try with_reducible_and_instances rfl
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs,
          StructuredProgram.Atom.instr, execInstr]
    | true =>
        apply Eval.ite_true (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 4) 2 3) a)) using 1
        all_goals try with_reducible_and_instances rfl
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs,
          StructuredProgram.Atom.instr, execInstr]
  exact hl.seq (hp.seq (popMask_eval r mask [] low ((if b then false else x) :: out)))

theorem loop_eval (regs : Fin 4 → Bool) (mask xs out : List Bool)
    (hlen : mask.length = xs.length)
    (hzero : ∀ x ∈ selected true mask xs, x = false) :
    ∃ rf, Eval loop (5 * mask.length + 1)
      (popped regs mask [] (selected false mask xs) out)
      (state rf [] [] [] (xs.reverse ++ out)) := by
  induction mask generalizing regs xs out with
  | nil =>
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst xs
      exact ⟨readRegs regs 0 1 none, Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have hz : ∀ v ∈ selected true mask xs, v = false := by
            intro v hv
            apply hzero v
            cases b <;> simp [selected, hv]
          have hx : (if b then false else x) = x := by
            cases b
            · rfl
            · exact (hzero x (by simp [selected])).symm
          obtain ⟨ri, hi⟩ := iteration regs b x mask (selected false mask xs) out
          have hi' : Eval body 4
              (popped regs (b :: mask) [] (selected false (b :: mask) (x :: xs)) out)
              (popped ri mask [] (selected false mask xs) (x :: out)) := by
            simpa only [hx] using (show Eval body 4
              (popped regs (b :: mask) [] (selected false (b :: mask) (x :: xs)) out)
              (popped ri mask [] (selected false mask xs) ((if b then false else x) :: out)) by
                convert hi using 1
                all_goals try with_reducible_and_instances rfl
                cases b <;> rfl)
          obtain ⟨rf, hr⟩ := ih ri xs (x :: out) (by simpa using hlen) hz
          refine ⟨rf, ?_⟩
          have h := Eval.while_true (show
            (popped regs (b :: mask) [] (selected false (b :: mask) (x :: xs)) out).regs 1 = true by rfl) hi' hr
          convert h using 1 <;> simp only [loop, List.length_cons, List.reverse_cons,
            List.append_assoc, List.singleton_append, Nat.mul_add, Nat.mul_one,
            Nat.add_comm, Nat.add_left_comm]
          omega

theorem command_eval (regs : Fin 4 → Bool) (mask xs out : List Bool)
    (hlen : mask.length = xs.length)
    (hzero : ∀ x ∈ selected true mask xs, x = false) :
    ∃ rf, Eval command (5 * mask.length + 2)
      (state regs mask [] (selected false mask xs) out)
      (state rf [] [] [] (xs.reverse ++ out)) := by
  obtain ⟨rf, hr⟩ := loop_eval regs mask xs out hlen hzero
  refine ⟨rf, ?_⟩
  convert (popMask_eval regs mask [] (selected false mask xs) out).seq hr using 1
  · rfl
  · omega

end ZeroHigh

/-- Runtime zero insertion needs no supplied padding: the fixed high stream is
empty, and the concrete source pop operation returns false. -/
theorem freeFill_command_eval {n : ℕ} (regs : Fin 4 → Bool) (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) :
    ∃ rf, Eval OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.command (5 * n + 2)
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
        [] (List.ofFn bits).reverse [])
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
        (List.ofFn (freeFill H bits))) := by
  have hm : (descendingHighMask H).length = n := by
    simp [descendingHighMask, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates]
  have hz : ∀ x ∈ OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true
      (descendingHighMask H) (List.ofFn (freeFill H bits)).reverse, x = false := by
    rw [freeFill_high_stream]
    intro x hx
    exact (List.mem_replicate.mp hx).2
  obtain ⟨rf,he⟩ := ZeroHigh.command_eval regs (descendingHighMask H)
    (List.ofFn (freeFill H bits)).reverse [] (by simp [hm]) hz
  refine ⟨rf, ?_⟩
  simpa only [freeFill_low_stream, List.reverse_reverse, List.append_nil, hm] using he

/-- Zero insertion uses linear time and bounds every stack at every source
prefix, including unsuccessful pops of the intentionally empty high stream. -/
theorem freeFill_trace_space {n : ℕ} (regs : Fin 4 → Bool) (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) :
    ∃ rf, Trace OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program (5 * n + 3)
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
        [] (List.ofFn bits).reverse []).withPC
          (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry))
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
        (List.ofFn (freeFill H bits))).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ 5 * n + 3 →
        Trace OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program prefixSteps
          ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
            [] (List.ofFn bits).reverse []).withPC
              (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ 9 * n + 3 := by
  obtain ⟨rf,he⟩ := freeFill_command_eval regs H bits
  refine ⟨rf,?_,?_⟩
  · exact compiled_halt_trace he 0 3
  · have hi : dataBits
        ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
          [] (List.ofFn bits).reverse []).withPC
            (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry)) ≤ 4 * n := by
      apply StreamResources.dataBits_le_mul
      intro i
      fin_cases i <;> simp [OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state,
        descendingHighMask,
        OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates]
    intro prefixSteps intermediate hle htrace i
    have hb := StructuredSpace.local_stack_bound
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program (steps := 5*n+3)
      hi prefixSteps intermediate hle htrace i
    omega

/-- The physical zero-fill routine encodes exactly the same support transported
from residual indices to ambient coordinates, with no fixed variable inserted. -/
theorem freeFill_support {n : ℕ} (H : Finset (Fin n)) (U : Finset (Fin (n - H.card)))
    (v : Fin n) :
    freeFill H (fun i => decide (i ∈ U)) v =
      decide (v ∈ U.image (fun i => (freeOrder H i).val)) := by
  by_cases hv : v ∈ H
  · have hnot : v ∉ U.image (fun i => (freeOrder H i).val) := by
      intro hm
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
      exact (freeOrder H i).property (hi.symm ▸ hv)
    simp [freeFill, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue, hv, hnot]
  · let i := (freeOrder H).symm ⟨v,hv⟩
    have hi : (freeOrder H i).val = v := by simp [i]
    have hm : v ∈ U.image (fun j => (freeOrder H j).val) ↔ i ∈ U := by
      constructor
      · intro hm
        obtain ⟨j,hj,hv'⟩ := Finset.mem_image.mp hm
        have he : j = i := (freeOrder H).injective (Subtype.ext (hv'.trans hi.symm))
        exact he ▸ hj
      · intro hu
        exact Finset.mem_image.mpr ⟨i,hu,hi⟩
    rw [← hi, freeFill_order]
    simp only [hi, hm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_PairNativeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical pair traversal initialization and ambient-mask expansion. The
five low scratch ports325..329 are reclaimed before the caller returns; the
pair controller and persistent node/layout words are not scratch. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
open OAI BitProgram StructuredCalls


open SubexpSetupStorage

theorem fillRegister_injective : Function.Injective fillRegister := Fin.castLE_injective (by decide)
theorem fillStack_injective : Function.Injective fillStack := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [fillStack] at he
  omega

theorem fillPrepared_stack (isE : Bool) (a : Data) (i : Fin 896) :
    (fillPrepared isE a).stacks i =
      if i=325 then a.stacks 338 else if i=327 then a.stacks (fillInput isE)
      else if i ∈ scratch then [] else a.stacks i := by
  simp only [fillPrepared, prepareState, beforeCopies, copyManyState, copyState_stack,
    resetMany_stacks, clearMany_stacks]
  by_cases h325 : i=325
  · subst i; cases isE <;> simp [fillInput,scratch,clearMany_stacks]
  · by_cases h327 : i=327
    · subst i; cases isE <;> simp [fillInput,scratch,clearMany_stacks]
    · by_cases h329 : i=329 <;> cases isE <;>
        simp [fillInput,h325,h327,h329,scratch,clearMany_stacks]

theorem fillMiddle_stack (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool)
    (i : Fin 896) :
    (fillMiddle isE a rf word).stacks i =
      if i=328 then word else if i ∈ scratch then [] else a.stacks i := by
  by_cases hi : ∃ j, fillStack j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [fillMiddle, embedState_stack _ _ _ _ fillStack_injective]
    fin_cases j <;> simp [fillStack, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state, scratch]
  · have hframe := embedState_stack_frame fillRegister fillStack (fillPrepared isE a)
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] [] word) i hi
    rw [show (fillMiddle isE a rf word).stacks i = (fillPrepared isE a).stacks i from hframe,
      fillPrepared_stack]
    have h325 : i≠325 := by intro h; exact hi ⟨0,h.symm⟩
    have h327 : i≠327 := by intro h; exact hi ⟨2,h.symm⟩
    have h328 : i≠328 := by intro h; exact hi ⟨3,h.symm⟩
    simp [h325,h327,h328]

theorem fillResult_stack (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool)
    (i : Fin 896) :
    (fillResult isE a rf word).stacks i =
      if i=fillOutput isE then word else if i ∈ scratch then [] else a.stacks i := by
  simp only [fillResult, finishState, resetMany_stacks, clearMany_stacks,
    copyManyState, copyState_stack, List.map_cons, List.map_nil]
  by_cases hs : i ∈ scratch
  · have ho : i≠fillOutput isE := by
      intro h
      subst i
      cases isE <;> norm_num [fillOutput,scratch,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hs
    simp [hs,ho]
  · have h328 : i≠328 := by intro h; subst i; exact hs (by simp [scratch])
    by_cases ho : i=fillOutput isE
    · subst i
      cases isE <;> simp [fillOutput,fillMiddle_stack,scratch]
    · cases isE <;> simp_all [fillOutput,fillMiddle_stack,scratch,clearMany_stacks]

theorem fillCommand_eval {n : ℕ} (isE : Bool) (a : Data) (H : Finset (Fin n))
    (bits : Fin (n-H.card) → Bool)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hb : a.stacks (fillInput isE) = (List.ofFn bits).reverse) :
    ∃ rf, Eval (fillCommand isE)
      (prepareCost 329 scratch [(338,325),(fillInput isE,327)] a +
        (5*n+3+finishCost scratch [(328,fillOutput isE)]
          (fillMiddle isE a rf (List.ofFn (HighIncidenceProgram.freeFill H bits)))))
      a (fillResult isE a rf (List.ofFn (HighIncidenceProgram.freeFill H bits))) := by
  have hp : project fillRegister fillStack (fillPrepared isE a) =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state
        ((fillPrepared isE a).regs ∘ fillRegister)
        (HighIncidenceProgram.descendingHighMask H) [] (List.ofFn bits).reverse [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [Function.comp_apply, fillStack, fillPrepared_stack,
        scratch, hm, hb, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  obtain ⟨rf,htrace,_⟩ := HighIncidenceProgram.freeFill_trace_space
    ((fillPrepared isE a).regs ∘ fillRegister) H bits
  rw [← hp] at htrace
  refine ⟨rf,?_⟩
  exact isolated_eval OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program fillRegister fillStack
    fillRegister_injective fillStack_injective 329 scratch
    [(338,325),(fillInput isE,327)] [(328,fillOutput isE)] a
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
      (List.ofFn (HighIncidenceProgram.freeFill H bits)))
    (by cases isE <;> simp [fillInput]) (by cases isE <;> simp [fillOutput])
    (by rintro ⟨j,hj⟩; have he:=congrArg Fin.val hj; have hjlt:=j.isLt; simp [fillStack] at he; omega)
    (by simpa only [fillPrepared] using htrace)



theorem fillCommand_cost (isE : Bool) (a : Data) (B n : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) (rf : Fin 4 → Bool)
    (word : List Bool) (hw : word.length ≤ n) :
    prepareCost 329 scratch [(338,325),(fillInput isE,327)] a +
        (5*n+3+finishCost scratch [(328,fillOutput isE)] (fillMiddle isE a rf word)) ≤
      100*(B+n+1) := by
  have h0 := clearManyCost_le [329] a B hb
  have h1 : ∀ i, ((clearManyState [329] a).stacks i).length ≤ B := by
    intro i
    rw [clearMany_stacks]
    split <;> simp_all
  have h2 := clearManyCost_le scratch (clearManyState [329] a) B h1
  have h3 : ∀ i, ((fillMiddle isE a rf word).stacks i).length ≤ B+n := by
    intro i
    rw [fillMiddle_stack]
    split_ifs
    · exact hw.trans (Nat.le_add_left n B)
    · exact Nat.zero_le _
    · exact (hb i).trans (Nat.le_add_right B n)
  have h4 := clearManyCost_le [fillOutput isE] (fillMiddle isE a rf word) (B+n) h3
  have h5 : ∀ i,
      ((copyManyState [(328,fillOutput isE)]
        (clearManyState [fillOutput isE] (fillMiddle isE a rf word))).stacks i).length ≤ B+n := by
    intro i
    simp only [copyManyState, copyState_stack, clearMany_stacks]
    by_cases h : i=fillOutput isE
    · subst i
      cases isE <;> simp [fillOutput, fillMiddle_stack]
      all_goals omega
    · simp [h,clearMany_stacks,h3]
  have h6 := clearManyCost_le scratch
    (copyManyState [(328,fillOutput isE)]
      (clearManyState [fillOutput isE] (fillMiddle isE a rf word))) (B+n) h5
  simp only [prepareCost, finishCost, List.map_cons, List.map_nil,
    copyManyCost, Nat.add_zero]
  have hp0 : (beforeCopies 329 scratch a).stacks 338 = a.stacks 338 := by
    simp [beforeCopies,resetMany_stacks,clearMany_stacks,scratch]
  have hp1 : (copyState 338 325 (beforeCopies 329 scratch a)).stacks (fillInput isE) =
      a.stacks (fillInput isE) := by
    cases isE <;> simp [copyState_stack,fillInput,beforeCopies,resetMany_stacks,clearMany_stacks,scratch]
  have hout : (clearManyState [fillOutput isE] (fillMiddle isE a rf word)).stacks 328 = word := by
    cases isE <;> simp [clearMany_stacks,fillOutput,fillMiddle_stack]
  rw [hp0,hp1,hout]
  have hm := hb 338
  have hf := hb (fillInput isE)
  simp only [List.length_cons,List.length_nil,Nat.zero_add,one_mul] at h0 h4
  have hs : scratch.length = 5 := rfl
  rw [hs] at h2 h6
  omega

theorem expandResult_stack (a : Data) (rfE rfU : Fin 4 → Bool)
    (Eword Uword : List Bool) (i : Fin 896) :
    (expandResult a rfE rfU Eword Uword).stacks i =
      if i=857 then Uword else if i=858 then Eword
      else if i ∈ scratch then [] else a.stacks i := by
  simp only [expandResult,fillResult_stack,fillOutput,Bool.false_eq_true,↓reduceIte]
  by_cases hu : i=857
  · simp [hu]
  · by_cases he : i=858
    · subst i; simp [scratch]
    · by_cases hs : i ∈ scratch <;> simp [hu,he,hs]

theorem expandCommand_eval {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834 = (List.ofFn E).reverse)
    (hu : a.stacks 835 = (List.ofFn U).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ ticks rfE rfU, ticks ≤ 300*(B+n+1) ∧ Eval expandCommand ticks a
      (expandResult a rfE rfU (List.ofFn (HighIncidenceProgram.freeFill H E))
        (List.ofFn (HighIncidenceProgram.freeFill H U))) := by
  obtain ⟨rfE,hE⟩ := fillCommand_eval true a H E hm he
  let b := fillResult true a rfE (List.ofFn (HighIncidenceProgram.freeFill H E))
  have hbm : b.stacks 338 = HighIncidenceProgram.descendingHighMask H := by
    simpa [b,fillResult_stack,fillOutput,scratch] using hm
  have hbu : b.stacks 835 = (List.ofFn U).reverse := by
    simpa [b,fillResult_stack,fillOutput,scratch] using hu
  have hbb : ∀ i, (b.stacks i).length ≤ B+n := by
    intro i
    rw [show b=fillResult true a rfE (List.ofFn (HighIncidenceProgram.freeFill H E)) from rfl,
      fillResult_stack]
    split_ifs
    · simp only [List.length_ofFn]
      exact Nat.le_add_left n B
    · exact Nat.zero_le _
    · exact (hb i).trans (Nat.le_add_right B n)
  obtain ⟨rfU,hU⟩ := fillCommand_eval false b H U hbm hbu
  have htE := fillCommand_cost true a B n hb rfE
    (List.ofFn (HighIncidenceProgram.freeFill H E)) (by simp)
  have htU := fillCommand_cost false b (B+n) n hbb rfU
    (List.ofFn (HighIncidenceProgram.freeFill H U)) (by simp)
  exact ⟨_,rfE,rfU,by omega,hE.seq hU⟩

/-- One concrete run expands both reversed residual masks to full ambient
masks and returns every allocated scratch stack empty. -/
theorem expand_resources {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834 = (List.ofFn E).reverse)
    (hu : a.stacks 835 = (List.ofFn U).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : Data), ticks ≤ 300*(B+n+1)+1 ∧
      Trace (compiled expandCommand 338 857) ticks
        (a.withPC (some (compiled expandCommand 338 857).entry)) (b.withPC none) ∧
      b.stacks 858 = List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857 = List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠857 → i≠858 → b.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace (compiled expandCommand 338 857) prefixSteps
          (a.withPC (some (compiled expandCommand 338 857).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+300*(B+n+1)+1 := by
  obtain ⟨ticks,rfE,rfU,ht,htrace⟩ := expandCommand_eval a H E U B hm he hu hb
  refine ⟨ticks+1,_,by omega,compiled_halt_trace htrace 338 857,?_,?_,?_,?_,?_⟩
  · simp [expandResult_stack]
  · simp [expandResult_stack]
  · intro i hi
    have h857 : i≠857 := by intro h; subst i; norm_num [scratch,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hi
    have h858 : i≠858 := by intro h; subst i; norm_num [scratch,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hi
    simp [expandResult_stack,h857,h858,hi]
  · intro i hi h857 h858
    simp [expandResult_stack,hi,h857,h858]
  · have hmass : dataBits (a.withPC (some (compiled expandCommand 338 857).entry)) ≤896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hp htrace i
    have hbound := StructuredSpace.local_stack_bound (compiled expandCommand 338 857)
      hmass prefixSteps intermediate (hp.trans (show ticks+1≤300*(B+n+1)+1 by omega)) htrace i
    omega



theorem callerRegister_injective : Function.Injective callerRegister := Fin.castLE_injective (by decide)

/-- The actual shared-ABI mask expansion is directly composable and restores
the same boundary word bound, since the retained high mask already has length n. -/
theorem expandCaller_eval {n : ℕ} (a : CallerData) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834 = (List.ofFn E).reverse)
    (hu : a.stacks 835 = (List.ofFn U).reverse)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : CallerData), ticks ≤ 300*(B+n+1)+1 ∧ Eval expandCaller ticks a b ∧
      b.stacks 858 = List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857 = List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠857 → i≠858 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  obtain ⟨ticks,b,ht,htrace,hE,hU,hs,hframe,_⟩ :=
    expand_resources (projectState callerRegister id a) H E U B hm he hu hb
  have hcall := eval_call_from_state (compiled expandCommand 338 857) callerRegister id a
    callerRegister_injective Function.injective_id htrace
  let out := embedState callerRegister id a b
  have hout : ∀ i, out.stacks i=b.stacks i := fun i =>
    embedState_stack callerRegister id a b Function.injective_id i
  refine ⟨ticks,out,ht,hcall,(hout 858).trans hE,(hout 857).trans hU,
    fun i hi => (hout i).trans (hs i hi),
    fun i hi h857 h858 => (hout i).trans (hframe i hi h857 h858),?_⟩
  have hn : n≤B := by
    have h:=hb 338
    simpa [hm,HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using h
  intro i
  rw [hout]
  by_cases h857 : i=857
  · subst i; simpa [hU] using hn
  · by_cases h858 : i=858
    · subst i; simpa [hE] using hn
    · by_cases hi : i∈scratch
      · simp [hs i hi]
      · rw [hframe i hi h857 h858]
        exact hb i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

end Good


end NativeValidity

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem clearWord_eval (src : Fin 896) (a : State 40 896) :
    Eval (clearWord src) (2 * (a.stacks src).length + 3) a (clearState src a) := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  exact .call _ (by simpa [clearState, StackRoutines.clearResult, StackRoutines.clearStacks,
    StructuredProgram.State.withPC, StackRoutines.clearProgram, Nat.add_assoc] using hh)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
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

/-- Extend a command-prefix certificate through the compiled halt transition. -/
theorem PrefixBound.withHalt {command : Code} {steps B : ℕ} {a b : Data}
    (h : PrefixBound command steps a B) (he : Eval command steps a b) :
    PrefixBound command (steps+1) a B :=
  ⟨StructuredSpace.compiled_halt_stack_bound he 838 838 h.bound⟩

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

namespace PairStart

theorem encoded_outer {m : ℕ} (E U : Finset (Fin m)) :
    (DifferencePairs.encodePair E U).map Option.isSome=List.ofFn (fun i => decide (i∈E)) := by
  rw [DifferencePairs.encodePair,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  by_cases hi : i∈E <;> simp [hi]

theorem encoded_inner {m : ℕ} (E U : Finset (Fin m)) (hU : U⊆E) :
    (DifferencePairs.encodePair E U).map (fun x => x.getD false)=
      List.ofFn (fun i => decide (i∈U)) := by
  rw [DifferencePairs.encodePair,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  by_cases hi : i∈E
  · simp [hi]
  · have hu : i∉U := fun h => hi (hU h)
    simp [hi,hu]

theorem expanded_support_word {n : ℕ} (H : Finset (Fin n))
    (E : Finset (Fin (n-H.card))) :
    List.ofFn (HighIncidenceProgram.freeFill H (fun i => decide (i∈E)))=
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits
        ⟨E.image (fun i => (HighIncidenceProgram.freeOrder H i).val)⟩ := by
  apply congrArg List.ofFn
  funext i
  exact HighIncidenceProgram.freeFill_support H E i

theorem command_run {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=(List.ofFn E).reverse)
    (hu : a.stacks 835=(List.ofFn U).reverse)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval command steps a b ∧
      b.stacks 851=[] ∧
      b.stacks 858=List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857=List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i∈PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 →
        b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps+1 ≤ 300*(B+n+1)+2*B+5 := by
  let start := clearState 851 a
  have hb : ∀ i, (start.stacks i).length ≤ B := by
    intro i
    by_cases hi : i=851
    · subst i
      simp [start,clearState]
    · simpa [start,clearState,hi] using ha i
  have hf (i : Fin 896) (hi : i≠851) : start.stacks i=a.stacks i := by
    simp [start,clearState,hi]
  obtain ⟨steps,b,ht,hr,hE,hU,hs,hframe,hbound⟩ :=
    PairNativeSetup.expandCaller_eval start H E U B
      ((hf 338 (by decide)).trans hm) ((hf 834 (by decide)).trans he)
      ((hf 835 (by decide)).trans hu) hb
  refine ⟨_,b,(clearWord_eval 851 a).seq hr,?_,hE,hU,hs,?_,hbound,?_⟩
  · rw [hframe 851 (by decide) (by decide) (by decide)]
    simp [start,clearState]
  · intro i hscratch h851 h857 h858
    exact (hframe i hscratch h857 h858).trans (hf i h851)
  · have h851 := ha 851
    omega

/-- This instance starts from the exact masks emitted by the ternary pair
DFS. Its outputs are the transported supports used by the actual native
factor correction and head predicate; no high coordinate enters either set. -/
theorem support_command_run {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E) (B : ℕ)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval command steps a b ∧ b.stacks 851=[] ∧
      b.stacks 858=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits
        ⟨E.image (fun i => (HighIncidenceProgram.freeOrder H i).val)⟩ ∧
      b.stacks 857=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits
        ⟨U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)⟩ ∧
      (∀ i∈PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 →
        b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps+1 ≤ 300*(B+n+1)+2*B+5 := by
  rw [encoded_outer] at he
  rw [encoded_inner E U hU] at hu
  simpa only [expanded_support_word] using
    command_run a H (fun i => decide (i∈E)) (fun i => decide (i∈U)) B hm he hu ha

end PairStart

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

namespace PairAccumulatorMeaning

theorem zero {r Q n d : ℕ} (q : Factor.Spec r Q n d) (a : Data)
    (hz : a.stacks 851=[]) : PairAccumulatorMeaning q 0 a := by
  refine ⟨[],?_,Good.nil,?_⟩
  · exact hz
  · rw [rawValue_nil,map_zero]

end PairAccumulatorMeaning

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairCommit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The signed finite-difference term is committed to the actual node word.
The pair product and the node sum use the same stored dictionaries as their
validity and readout witnesses. Marker readout remains additive. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram
open TruncatedRingProgram QueryProgram QueryTupleState

namespace NodeAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : NodeAccumulatorMeaning q value a) (hf : b.stacks 850=a.stacks 850) :
    NodeAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end NodeAccumulatorMeaning

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The actual pair start supplies the only four facts absent from the
common physical data. -/
theorem CommonReady.toReady {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H E U : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a : State 40 896}
    (h : CommonReady q node H high P a)
    (hE : a.stacks 858=List.ofFn (fun v : Fin n => decide (v∈E)))
    (hU : a.stacks 857=List.ofFn (fun v : Fin n => decide (v∈U)))
    (hfree : Disjoint E H) (hsub : U⊆E) : QueryReady q node H high E U P a :=
  {h with outer := hE, inner := hU, outerFree := hfree, innerSubset := hsub}

theorem CommonReady.frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a b : State 40 896}
    (h : CommonReady q node H high P a) (hf : ∀ i∈commonPorts, b.stacks i=a.stacks i) :
    CommonReady q node H high P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf 128 (by decide)).trans h.ambient
    theta := (hf 78 (by decide)).trans h.theta
    modulus := (hf 194 (by decide)).trans h.modulus
    table := (hf 201 (by decide)).trans h.table
    width := (hf 202 (by decide)).trans h.width
    scalarZero := (hf 203 (by decide)).trans h.scalarZero
    degree := (hf 204 (by decide)).trans h.degree
    one := (hf 207 (by decide)).trans h.one
    minus := (hf 211 (by decide)).trans h.minus
    precision := (hf 212 (by decide)).trans h.precision
    order := (hf 243 (by decide)).trans h.order
    zero := (hf 280 (by decide)).trans h.zero
    code := (hf 281 (by decide)).trans h.code
    clauses := (hf 700 (by decide)).trans h.clauses
    rows := (hf 701 (by decide)).trans h.rows
    rowCount := (hf 704 (by decide)).trans h.rowCount
    markedIndex := (hf 705 (by decide)).trans h.markedIndex
    markedFlag := (hf 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf 708 (by decide))).trans h.indexWidth
    highMask := (hf 702 (by decide)).trans h.highMask
    highBits := (hf 703 (by decide)).trans h.highBits
    colors := (hf 130 (by decide)).trans h.colors
    nodes := (hf 131 (by decide)).trans h.nodes
    typeWidth := (hf 132 (by decide)).trans h.typeWidth
    positive := (hf 710 (by decide)).trans h.positive
    negative := (hf 711 (by decide)).trans h.negative
    sourceWidth := (hf 140 (by decide)).trans h.sourceWidth
    power := (hf 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf 138 (by decide)).trans h.radius
    offset := (hf 139 (by decide)).trans h.offset
    metadata := (hf 135 (by decide)).trans h.metadata
    plans := (hf 136 (by decide)).trans h.plans
    inverses := (hf 713 (by decide)).trans h.inverses
    negatives := (hf 714 (by decide)).trans h.negatives
    differences := (hf 715 (by decide)).trans h.differences
    ringWidth := (hf 717 (by decide)).trans h.ringWidth
    rowWidth := (hf 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈commonPorts := by
      simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf _ hm]
    exact h.cacheCaps p hp
  · rw [hf 128 (by decide)]
    exact h.ambientCap
  · rw [hf 207 (by decide)]
    exact h.oneCap

/-- The pair expander changes only its masks, cleared accumulator and private
scratch, all disjoint from the common source data. -/
theorem CommonReady.pair_frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {P : ℕ} {a b : State 40 896}
    (h : CommonReady q node H high P a)
    (hf : ∀ i, i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 →
      b.stacks i=a.stacks i) : CommonReady q node H high P b := by
  apply h.frame
  intro i hi
  have hp : ∀ j∈commonPorts,
      j∉PairNativeSetup.scratch ∧ j≠851 ∧ j≠857 ∧ j≠858 := by
    simp [commonPorts,PairNativeSetup.scratch]
  exact hf i (hp i hi).1 (hp i hi).2.1 (hp i hi).2.2.1 (hp i hi).2.2.2

/-- A generated residual support contains only ambient free coordinates. -/
theorem expanded_disjoint {n : ℕ} (H : Finset (Fin n)) (E : Finset (Fin (n-H.card))) :
    Disjoint (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) H := by
  rw [Finset.disjoint_left]
  intro v hv hH
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  exact (HighIncidenceProgram.freeOrder H i).property hH

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

private theorem start_masters {source : ProducedSource} {a b : State 40 896}
    (hm : SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : ∀ i,i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 → b.stacks i=a.stacks i) :
    SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  have hn : SignatureHeadLoader.lowStacks i∉PairNativeSetup.scratch ∧
      SignatureHeadLoader.lowStacks i≠851 ∧ SignatureHeadLoader.lowStacks i≠857 ∧
      SignatureHeadLoader.lowStacks i≠858 := by
    simp only [SignatureHeadLoader.masters,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (hf _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans (hm.stored i hi)

/-- The actual paid pair start preserves the node sum and source witness,
resets851, and installs precisely the ambient images of the emitted masks. -/
theorem start_run {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin : State 40 896} (total : Truncated (q.p.model.O q.p.t) q.J)
    (a : State 40 896) (hi : Invariant q node H high P F source origin total a)
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (hb : ∀ i,(a.stacks i).length ≤ F) :
    ∃ steps b, Eval QueryExecution.PairStart.command steps a b ∧
      Invariant q node H high P F source origin total b ∧
      QueryReady q node H high
        (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
        (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P b ∧
      PairAccumulatorMeaning q 0 b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧ steps+1 ≤ 300*(F+n+1)+2*F+5 := by
  obtain ⟨steps,b,hEval,h851,hE,hU',_hs,hframe,hbound,htime⟩ :=
    QueryExecution.PairStart.support_command_run a H E U hU F hm he hu hb
  have hc := hi.common.pair_frame hframe
  have hnode := hi.accumulator.frame (hframe 850 (by decide) (by decide) (by decide) (by decide))
  have hf : ∀ i ∈ framePorts,b.stacks i=origin.stacks i := by
    intro i him
    have hp : ∀ j ∈ framePorts,j∉PairNativeSetup.scratch ∧ j≠851 ∧ j≠857 ∧ j≠858 := by
      simp [framePorts,PairNativeSetup.scratch]
    exact (hframe i (hp i him).1 (hp i him).2.1 (hp i him).2.2.1 (hp i him).2.2.2).trans
      (hi.frame i him)
  refine ⟨steps,b,hEval,⟨hc,hnode,fun i _=>hbound i,start_masters hi.masters hframe,hf⟩,
    hc.toReady hE hU' (expanded_disjoint H E) (Finset.image_subset_image hU),
    PairAccumulatorMeaning.zero q b h851,?_,hbound,htime⟩
  intro j
  fin_cases j <;> exact hframe _ (by decide) (by decide) (by decide) (by decide)

/-- The full tuple provider restores its real query masters. The node word
and outer cursor words consequently retain their exact meaning. -/
theorem Invariant.query_frame {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a b : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (hf : QueryMasterFrame a b) (hbound : ∀ i,(b.stacks i).length ≤ F)
    (h649 : b.stacks 649=a.stacks 649) :
    Invariant q node H high P F source origin total b := by
  refine ⟨h.common.frame ?_,h.accumulator.frame (hf.word 850 (by decide)),
    (fun i _=>hbound i),source_frame_of_queryFrame source.masters a b h.masters hf,?_⟩
  · intro i hi
    have hm : ∀ j ∈ commonPorts,j ∈ masterPorts := by simp [commonPorts,masterPorts]
    exact hf.word i (hm i hi)
  · intro i hi
    have hm : ∀ j ∈ framePorts,j=649 ∨ j ∈ masterPorts := by
      intro j hj
      simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rcases hm i hi with rfl|hm
    · exact h649.trans (h.frame 649 hi)
    · exact (hf.word i hm).trans (h.frame i hi)

/-- One complete callback of the fixed program: actual mask expansion,
the complete attained-tuple DFS, and the actual signed dense commit. -/
theorem callback_run_oai (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (origin a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
    (hi : Invariant q s.input.node H high M F s origin total a)
    (hm : origin.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : origin.stacks 649=List.replicate s.base true)
    (E U : Finset (Fin (s.input.n-H.card))) (hU : U⊆E)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (hb : ∀ i,(a.stacks i).length ≤ F) :
    ∃ steps b, Eval QueryStreamProgram.pairCallback steps a b ∧
      Invariant q s.input.node H high M F s origin
        (total+(-1)^(E.card-U.card)*pairValue s q H high owner head facts E U) b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧
      steps ≤ callbackBudget s q (s.input.n-H.card) F S Z B height ∧
      QueryExecution.PrefixBound QueryStreamProgram.pairCallback (steps+1) a
        (callbackSpace s q (s.input.n-H.card) F B) := by
  obtain ⟨ns,b,hs,hi',hquery,hzero,hcontrol,hb',hts⟩ := start_run total a hi E U hU
    ((hi.frame 338 (by decide)).trans hm) he hu hb
  have hz : b.stacks 649=List.replicate s.base true :=
    (hi'.frame 649 (by decide)).trans haddress
  obtain ⟨nt,c,ht,_htrace,hqc,hacc,hc,hbase,hmasters,htt,hpt⟩ :=
    SignatureTupleRun.run_resources s q H
      (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
      (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) high owner head facts caps cap
      hheads 0 b hb' hi'.masters hz hquery hzero
  have hi'' := hi'.query_frame hmasters hc (hbase.trans hz.symm)
  have hec : c.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse :=
    (hmasters.word 834 (by decide)).trans ((hcontrol 2).trans he)
  have huc : c.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse :=
    (hmasters.word 835 (by decide)).trans ((hcontrol 3).trans hu)
  have hpv : PairAccumulatorMeaning q (pairValue s q H high owner head facts E U) c := by
    simpa only [pairValue,zero_add] using hacc
  obtain ⟨nc,e,hcommit,hIe,hce,hebound,htc,hpc⟩ := commit_run total
    (pairValue s q H high owner head facts E U) c hi'' E U hU hqc hec huc hpv hc caps.multiply
  have hall : Eval QueryStreamProgram.pairCallback (ns+(nt+nc)) a e := hs.seq (ht.seq hcommit)
  let D := callbackSpace s q (s.input.n-H.card) F B
  have hsBound : 896*F+ns ≤ D := by
    have hn : ns ≤ startBudget s.input.n F := by unfold startBudget; omega
    exact (by omega : 896*F+ns ≤ 896*F+startBudget s.input.n F+commitBudget q (s.input.n-H.card) F).trans
      (Nat.le_max_right _ _)
  have hps : QueryExecution.PrefixBound QueryExecution.PairStart.command ns a D :=
    (QueryExecution.prefix_local _ ns F a hb).mono hsBound
  have hpt' : QueryExecution.PrefixBound SignatureTupleComplete.command nt b D := by
    constructor
    intro elapsed cfg hp htrace i
    exact (hpt elapsed cfg (by omega) htrace i).trans (Nat.le_max_left _ _)
  have hpc' : QueryExecution.PrefixBound QueryAssembler.commitPair nc c D := by
    constructor
    intro elapsed cfg hp htrace i
    exact (hpc.bound elapsed cfg (by omega) htrace i).trans
      ((by omega : 896*F+commitBudget q (s.input.n-H.card) F ≤         896*F+startBudget s.input.n F+commitBudget q (s.input.n-H.card) F).trans (Nat.le_max_right _ _))
  have hprefix := QueryExecution.prefix_seq hs (ht.seq hcommit) hps
    (QueryExecution.prefix_seq ht hcommit hpt' hpc')
  refine ⟨ns+(nt+nc),e,hall,hIe,?_,hebound,?_,⟨?_⟩⟩
  · intro j
    have hmj : QueryStreamProgram.pairPorts.stack j ∈ masterPorts := by fin_cases j <;> decide
    exact (hce j).trans ((hmasters.word _ hmj).trans (hcontrol j))
  · unfold callbackBudget startBudget
    omega
  · exact (hprefix.withHalt hall).bound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run_oai
