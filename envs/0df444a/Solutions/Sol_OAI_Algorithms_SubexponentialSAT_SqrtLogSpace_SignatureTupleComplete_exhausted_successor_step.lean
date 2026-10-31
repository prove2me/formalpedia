-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:55:25.040161+00:00
-- url     : https://prove2.me/submissions/228d44df-53aa-4c6d-ba1a-67448ad0678e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_ascend_native_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

/-- Every off-counter caller stack is preserved, including cleared scratch. -/
theorem incrementResult_stacks {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    (incrementResult p d).stacks =
      Function.update d.stacks p.counter (ripple true (d.stacks p.counter)) := by
  funext i
  by_cases hc : i = p.counter
  · subst i
    simp
  · by_cases hi : i = p.scratch
    · subst i
      simp [hc, hs]
    · rw [Function.update_of_ne hc]
      exact install_other_stack p d _ _ _ _ _ i hc hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
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

theorem trace_prefix_bound_cons {α : Type*} {step : α → Option α}
    {a b : α} {steps : ℕ} {P : α → Prop}
    (hs : step a = some b) (ha : P a)
    (htail : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle hp
  cases hp with
  | refl => exact ha
  | cons hs' ht =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst b
      exact htail _ _ (by omega) ht


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

theorem conditional_false_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = false) (heval : StructuredCalls.Eval no steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled no inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled no inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.ite test yes no) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.ite test yes no) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.ite test yes no) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := steps)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry no (fun q => embed (some (.inr q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q)))

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

theorem returned_frame {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hi : Protected i)
    (hn : ∀ p ∈ outs,i≠p.2) : (returned reg hs ins outs a b).stacks i=a.stacks i := by
  have hno : ∀ p ∈ outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  exact (finish_frame _ _ _ _ (protected_not_workPorts hs hi) hno).trans
    ((embedState_stack_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; exact protected_ne_work hs hi j hj.symm)).trans
      (prepared_frame hs ins a i hi))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem headResult_frame (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h650 : i≠650) (h651 : i≠651) :
    (headResult a n rows low W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) headInputs headOutputs a _ i hi
  intro p hp
  simp only [headOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl <;> assumption

theorem factorResult_frame (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h671 : i≠671) :
    (factorResult a A N rows W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) factorInputs factorOutputs a _ i hi
  intro p hp
  simp only [factorOutputs,List.mem_singleton] at hp
  subst p
  exact h671

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem countResult_frame (a : Data) (i : Fin 768) (hi : Protected i) (h652 : i≠652) :
    (countResult a).stacks i=a.stacks i := by
  apply returned_frame countRegs (by decide) countInputs countOutputs a _ i hi
  intro p hp
  simp only [countOutputs,List.mem_singleton] at hp
  subst p
  exact h652

theorem scatterResult_frame (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ)
    (i : Fin 768) (hi : Protected i) (h670 : i≠670) :
    (scatterResult a regs n js).stacks i=a.stacks i := by
  apply returned_frame scatterRegs (by decide) scatterInputs scatterOutputs a _ i hi
  intro p hp
  simp only [scatterOutputs,List.mem_singleton] at hp
  subst p
  exact h670

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete head-selection stage. All three objects consumed by the
matrix/bucket phase are computed from runtime masters by fixed programs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem preparedHead_frame (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) (i : Fin 768)
    (hi : Protected i) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
    (preparedHead a regs n N rows low W z).stacks i=a.stacks i := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ hi h671,
    scatterResult_frame _ _ _ _ _ hi h670,countResult_frame _ _ hi h652]
  exact headResult_frame _ _ _ _ _ _ _ hi h650 h651

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- Every persistent protected source except the head outputs and matrix
output668 is retained by the local loader. -/
theorem localResult_frame (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (hi : Protected i)
    (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h668 : i≠668)
    (h669 : i≠669) (h670 : i≠670) (h671 : i≠671) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks i=a.stacks i := by
  unfold localResult
  simp only [clearState,Function.update_of_ne h669]
  rw [returned_frame shiftRegs (by decide) shiftInputs shiftOutputs _ _ i hi
    (by simpa [shiftOutputs] using h668)]
  rw [returned_frame id (by decide) matrixInputs rawOutputs _ _ i hi
    (by simpa [rawOutputs] using h669)]
  exact preparedHead_frame a rp n N rows low W z i hi h650 h651 h652 h670 h671

theorem localResult_masters (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    MasterFrame a (localResult a rp rm rs n N W z rows low raw shifted) := by
  constructor
  intro i hi
  simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    exact localResult_frame a rp rm rs n N W z rows low raw shifted _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exportedState_raw (a : State 16 896) : (exportedState a).stacks 846=[] := by
  simp [exportedState,clearMany_stacks]

theorem exportedState_frame (a : State 16 896) (i : Fin 896)
    (hi : i≠659 ∧ i≠668 ∧ i≠669 ∧ i≠846 ∧ i≠847) :
    (exportedState a).stacks i=a.stacks i := by
  simp only [exportedState,clearMany_stacks,List.mem_cons,
    List.not_mem_nil,hi.2.1,hi.2.2.1,hi.2.2.2.1,or_self]
  rw [copyState_frame _ _ _ _ hi.2.2.2.2]
  simp [clearState,hi.1]

theorem addressStateFrom_value (src : Fin 896) (a : State 16 896)
    (hs : src∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks 649=a.stacks src := by
  simp only [addressStateFrom,copyState,StackRoutines.copyStacks,Function.update_self,
    clearMany_stacks, hs, show (649:Fin 896)∈[649,659,846,847] by decide,
    ite_false, ite_true, if_true, List.append_nil]

theorem addressStateFrom_frame (src : Fin 896) (a : State 16 896) (i : Fin 896)
    (hi : i∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks i=a.stacks i := by
  have h649 : i≠649 := by intro h; subst i; simp at hi
  rw [addressStateFrom,copyState_frame _ _ _ _ h649,clearMany_stacks]
  simp only [hi, ite_false]

theorem lowResultFrom_low (src : Fin 896) (a : State 16 896) (b : Data) (i : Fin 768)
    (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (exportedState (lowResultFrom src a b)).stacks (lowStacks i)=b.stacks i := by
  have hlow (j : Fin 768) (hj : i≠j) : lowStacks i≠lowStacks j :=
    fun h => hj (lowStacks.injective h)
  have hhigh (j : Fin 896) (hj : 768 ≤ j.val) : lowStacks i≠j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=j.val at hv
    have := i.isLt
    omega
  rw [exportedState_frame _ _ ⟨hlow 659 h659,hlow 668 h668,hlow 669 h669,
    hhigh 846 (by decide),hhigh 847 (by decide)⟩]
  exact embedState_stack id lowStacks _ b lowStacks.injective i


theorem lowResultFrom_frame (src : Fin 896) (a : State 16 896) (b : Data)
    (i : Fin 896) (hhigh : 768 ≤ i.val)
    (hi : i∉([846,847] : List (Fin 896))) :
    (exportedState (lowResultFrom src a b)).stacks i=a.stacks i := by
  have hn (j : Fin 896) (hj : j.val<768) : i≠j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h846 : i≠846 := by intro h; subst i; simp at hi
  have h847 : i≠847 := by intro h; subst i; simp at hi
  rw [exportedState_frame _ i ⟨hn 659 (by decide),hn 668 (by decide),
    hn 669 (by decide),h846,h847⟩]
  unfold lowResultFrom
  rw [embedState_stack_frame id lowStacks _ b i (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega)]
  apply addressStateFrom_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨hn 649 (by decide),hn 659 (by decide),h846,h847⟩


theorem leafInputFrom_masters (src : Fin 896) (frame : State 40 896) (base : Data)
    (hf : MasterFrame base (projectState leafRegs lowStacks frame)) :
    MasterFrame base (leafInputFrom src frame) := by
  constructor
  intro i hi
  have hnot : lowStacks i∉([649,659,846,847] : List (Fin 896)) := by
    simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (addressStateFrom_frame src (projectState leafRegs id frame) (lowStacks i) hnot).trans
    (hf.stored i hi)

/-- Retained source equality composes between concrete call boundaries. -/
theorem MasterFrame.trans {a b c : Data} (hab : MasterFrame a b) (hbc : MasterFrame b c) :
    MasterFrame a c := ⟨fun i hi => (hbc.stored i hi).trans (hab.stored i hi)⟩

theorem leafOutputFrom_masters (src : Fin 896) (frame : State 40 896) (base b : Data)
    (hf : MasterFrame base b) :
    MasterFrame base (projectState leafRegs lowStacks (leafOutputFrom src frame b)) := by
  constructor
  intro i hi
  have hne : i≠659 ∧ i≠668 ∧ i≠669 := by
    simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (embedState_stack leafRegs id frame _ Function.injective_id (lowStacks i)).trans
    ((lowResultFrom_low src (projectState leafRegs id frame) b i hne.1 hne.2.1 hne.2.2).trans
      (hf.stored i hi))

theorem leafOutputFrom_raw_empty (src : Fin 896) (frame : State 40 896) (b : Data) :
    (leafOutputFrom src frame b).stacks 846=[] :=
  (embedState_stack leafRegs id frame _ Function.injective_id 846).trans (exportedState_raw _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem retainedState_frame (a : Data) (i : Fin 768)
    (h659 : i≠659) (h710 : i≠710) (h711 : i≠711) (h712 : i≠712) :
    (retainedState a).stacks i=a.stacks i := by
  rw [retainedState,copyMany_frame]
  · simp [clearMany_stacks,retainedPorts,h659]
  · simp [retainedCopies,h710,h711,h712]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem addressState_frame (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) (i : Fin 768)
    (hi : Protected i) (h648 : i≠648) (h649 : i≠649) :
    (addressState a regs r t).stacks i=a.stacks i := by
  apply returned_frame addressRegs (by decide) addressInputs addressOutputs a _ i hi
  intro p hp
  simp only [addressOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · exact h648
  · exact h649

theorem countedState_frame (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool))
    (i : Fin 768) (hi : Protected i) (h647 : i≠647) :
    (countedState a regs records).stacks i=a.stacks i := by
  apply returned_frame rowCountRegs (by decide) rowCountInputs rowCountOutputs a _ i hi
  intro p hp
  simp only [rowCountOutputs,List.mem_singleton] at hp
  subst p
  exact h647

theorem bootState_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) :
    (bootState a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  rcases hne with ⟨h640,h641,h642,h643,h647,h648,h649⟩
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ i hi,
    countedState_frame _ _ _ _ hi h647,addressState_frame _ _ _ _ _ hi h648 h649]
  intro p hp
  simp only [cacheOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact h640
  · exact h641
  · exact h642
  · exact h643

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Initialization of one node's physical Cartesian head loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem nodeStart_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768))) :
    (nodeStart a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  have h659 : i≠659 := hi.2
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  obtain ⟨h640,h641,h642,h643,h647,h648,h649,h660,h665,h710,h711,h712⟩ := hne
  simp only [nodeStart,tupleInitialized,Function.update_of_ne h665,Function.update_of_ne h660]
  rw [retainedState_frame _ i h659 h710 h711 h712]
  apply bootState_frame a ra rd rc r t records height R width words i hi
  simp [h640,h641,h642,h643,h647,h648,h649]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native entry cache is the actual output of the paid node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open RowSelectionProgram

theorem start_low (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) : (start s a ra rd rc words).stacks i=a.stacks i := by
  apply nodeStart_frame
  · constructor
    · left; exact hi
    · intro h; have hh := congrArg Fin.val h; simp [temporary] at hh; omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The physical shift word is retained exactly from the source bank. Its
word-length cap can therefore be fixed independently of the caller frame. -/
theorem native_offset_word (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (b : Data) (hf : MasterFrame (Native.start s a ra rd rc words) b) :
    b.stacks 141=a.stacks 141 :=
  (hf.stored 141 (by decide)).trans (Native.start_low s a ra rd rc words 141 (by decide))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem popWordState_src (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks src = tail :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem popWordState_dst (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks dst = word :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem popWordState_outside (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (popWordState src dst h a word tail).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

theorem restoreCursorState_words (a : State 40 896) (candidate remaining frames : List Bool) :
    (restoreCursorState a candidate remaining frames).stacks (tupleStacks 2) = candidate ∧
      (restoreCursorState a candidate remaining frames).stacks (tupleStacks 7) = remaining ∧
      (restoreCursorState a candidate remaining frames).stacks (tupleStacks 0) = frames := by
  constructor
  · exact popWordState_dst _ _ _ _ _ _
  constructor
  · unfold restoreCursorState
    rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide), popWordState_dst]
  · exact popWordState_src _ _ _ _ _ _

theorem ascendLevelState_words (a : State 40 896) (remaining address : ℕ)
    (hr : a.stacks (tupleStacks 6) = List.replicate remaining true)
    (ha : a.stacks (tupleStacks 9) = List.replicate (address + 1) true) :
    (ascendLevelState a).stacks (tupleStacks 6) = List.replicate (remaining + 1) true ∧
      (ascendLevelState a).stacks (tupleStacks 9) = List.replicate address true ∧
      (ascendLevelState a).regs controllerPorts.leaf = false := by
  have h69 : tupleStacks 6 ≠ tupleStacks 9 := by decide
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    hr, ha, List.replicate_succ, controllerPorts, h69, Ne.symm h69]

theorem clearWordsState_stacks (ports : List (Fin 896)) (a : State 40 896)
    (i : Fin 896) :
    (clearWordsState ports a).stacks i = if i ∈ ports then [] else a.stacks i := by
  induction ports generalizing a with
  | nil => simp [clearWordsState]
  | cons src rest ih =>
    rw [clearWordsState, ih]
    by_cases hr : i ∈ rest
    · simp [hr]
    · by_cases hi : i = src
      · subst i
        simp [hr, clearState]
      · simp [hr, hi, clearState]

theorem dropRepresentativeState_stacks (a : State 40 896) (word reps : List Bool) :
    (dropRepresentativeState a word reps).stacks (tupleStacks 1) = reps ∧
      (dropRepresentativeState a word reps).stacks (tupleStacks 4) = [] := by
  constructor
  · change Function.update
      (popWordState (tupleStacks 1) (tupleStacks 4) (by decide) a word reps).stacks
      (tupleStacks 4) [] (tupleStacks 1) = reps
    rw [Function.update_of_ne (by decide : tupleStacks 1 ≠ tupleStacks 4)]
    exact popWordState_src _ _ _ _ _ _
  · simp [dropRepresentativeState, clearState]

theorem testParentState_flag (a : State 40 896) :
    (testParentState a).regs controllerPorts.active =
      decide (a.stacks (tupleStacks 0) ≠ []) := by
  cases hs : a.stacks (tupleStacks 0) <;>
    simp [testParentState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hs]

theorem testAvailable_eval (a : State 40 896) (hs : a.stacks remainingPorts.scratch = []) :
    Eval testAvailableCommand (8 * (a.stacks remainingPorts.counter).length + 8) a
      (testAvailableState a) := by
  have ht := Eval.seq (CounterForPrograms.test_eval remainingPorts a hs)
    (Eval.base (StructuredProgram.Eval.atom
      (.copy controllerPorts.available (remainingPorts.register 2)) _))
  simpa only [testAvailableCommand, testAvailableState, Nat.add_assoc] using ht

theorem testAvailableState_flag (a : State 40 896) :
    (testAvailableState a).regs controllerPorts.available =
      !(CounterPrograms.isZero (a.stacks remainingPorts.counter)) :=
  CounterForPrograms.testResult_flag remainingPorts a

theorem popWordState_register_frame (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (popWordState src dst h a word tail).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

section Frames

open ExecCNFTupleEnumeration SignatureTupleProgram

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem cursorFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      cursorFrame (h depth) rep.val.val ++ cursorFrames h key depth ancestors := by
  simp only [cursorFrames, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatten_cons]
  rfl

theorem cursorFrames_pop (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    cursorFrames h key (depth + 1) ancestors =
      cursorFrame (h depth) (ancestors (Fin.last depth)).val.val ++
        cursorFrames h key depth (Fin.init ancestors) := by
  simpa only [Fin.snoc_init_self] using
    cursorFrames_snoc h key depth (Fin.init ancestors) (ancestors (Fin.last depth))

theorem cursorFrame_length (width candidate : ℕ) :
    (cursorFrame width candidate).length = 4 * width + 4 := by
  simp [cursorFrame]
  omega

end Frames

section NativeFrames

open ExecCNFTupleEnumeration SignatureTupleProgram StructuredCalls

private theorem restore_outside (a : StructuredProgram.State 40 896)
    (candidate remaining frames : List Bool) (i : Fin 896)
    (hf : i ≠ tupleStacks 0) (hc : i ≠ tupleStacks 2) (hr : i ≠ tupleStacks 7) :
    (restoreCursorState a candidate remaining frames).stacks i = a.stacks i := by
  unfold restoreCursorState
  rw [popWordState_outside _ _ _ _ _ _ _ hf hc,
    popWordState_outside _ _ _ _ _ _ _ hf hr]

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- Dropping the just-finished representative and restoring the two saved
cursor words gives exactly `Fin.init`, before the paid parent increment. -/
theorem returnFrames_state (depth : ℕ) (ancestors : Prefix (Representatives key) (depth + 1))
    (a : StructuredProgram.State 40 896) :
    let word := fixedBits (h depth) (ancestors (Fin.last depth)).val.val
    let remaining := fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val)
    let reps := representativeFrames h key depth (Fin.init ancestors)
    let frames := cursorFrames h key depth (Fin.init ancestors)
    let b := restoreCursorState (dropRepresentativeState a word reps) word remaining frames
    b.stacks (tupleStacks 0) = frames ∧ b.stacks (tupleStacks 1) = reps ∧
    b.stacks (tupleStacks 2) = word ∧ b.stacks (tupleStacks 7) = remaining ∧
    b.stacks (tupleStacks 4) = [] := by
  dsimp only
  have hs := restoreCursorState_words
    (dropRepresentativeState a
      (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
      (representativeFrames h key depth (Fin.init ancestors)))
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val))
    (cursorFrames h key depth (Fin.init ancestors))
  refine ⟨hs.2.2, ?_, hs.1, hs.2.1, ?_⟩
  · rw [restore_outside _ _ _ _ (tupleStacks 1) (by decide) (by decide) (by decide)]
    exact (dropRepresentativeState_stacks _ _ _).1
  · rw [restore_outside _ _ _ _ (tupleStacks 4) (by decide) (by decide) (by decide)]
    exact (dropRepresentativeState_stacks _ _ _).2

end NativeFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

theorem testAvailableState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (testAvailableState a).stacks = a.stacks :=
  CounterForPrograms.testResult_stacks remainingPorts a hs

/-- Exhaustion never runs the candidate scanner. In particular the binary
fuel word can be zero even when it retains leading zero cells. -/
theorem probe_exhausted_eval (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = [])
    (hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true) :
    Eval (probeWith candidateCall) (8 * (a.stacks remainingPorts.counter).length + 9)
      a (testAvailableState a) := by
  have hf : (testAvailableState a).regs controllerPorts.available = false := by
    rw [testAvailableState_flag, hzero]
    rfl
  have he : Eval (probeWith candidateCall)
      (8 * (a.stacks remainingPorts.counter).length + 8 + (0 + 1))
      a (testAvailableState a) :=
    (testAvailable_eval a hs).seq (Eval.ite_false hf (Eval.base (.skip _)))
  simpa only [probeWith, Nat.add_assoc] using he

/-- No physical tape outside the two counters and their decrement scratch is
changed by advancement. The increment scratch is restored as well. -/
theorem advanceState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hc : i ≠ candidatePorts.counter) (hr : i ≠ remainingPorts.counter)
    (ht : i ≠ remainingPorts.scratch) :
    (advanceState a).stacks i = a.stacks i := by
  change (CounterForPrograms.nextState remainingPorts
    (Counters.incrementResult candidatePorts a)).stacks i = a.stacks i
  rw [← CounterForPrograms.nextState_outside remainingPorts _ i hr ht]
  rw [Counters.incrementResult_stacks candidatePorts a hs, Function.update_of_ne hc]

theorem CursorWords.remaining_value {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - c := by
  rw [hw.remaining]
  apply ExecCNFTupleEnumeration.fixedBits_value
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

theorem CursorWords.available {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.isZero (a.stacks remainingPorts.counter) = decide (c = 2 ^ h) := by
  have hv := hw.remaining_value
  have hr := hw.range
  by_cases he : c = 2 ^ h
  · simp only [he, decide_true]
    apply (CounterPrograms.isZero_eq_true_iff _).mpr
    rw [hv, he, Nat.sub_self]
  · simp only [he, decide_false]
    apply (CounterPrograms.isZero_eq_false_iff _).mpr
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureRescanBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Physical effects of one full-signature probe

The input readiness facts describe actual words. The native predicate itself
supplies the run; its returned freshness is the first-occurrence predicate for
the complete integer signature.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open AttainedSignatureProgram.Rescan

theorem test_available_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (ha : j ≠ controllerPorts.available) :
    (testAvailableState a).regs j = a.regs j := by
  have h2 : j ≠ remainingPorts.register 2 := by
    intro he
    have hv := congrArg Fin.val he
    change j.val = 2 at hv
    omega
  simp only [testAvailableState, CounterForPrograms.testResult,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne ha, Function.update_of_ne h2]
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  change i.val = j.val at hv
  omega

theorem exhausted_probe_space (a : State 40 896) (frameBound : ℕ)
    (hs : a.stacks remainingPorts.scratch = [])
    (hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    Trace (compiled (probeWith candidateCall) 0 0)
        (8 * (a.stacks remainingPorts.counter).length + 10)
        (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry))
        ((testAvailableState a).withPC none) ∧
      ∀ prefixSteps intermediate,
        prefixSteps ≤ 8 * (a.stacks remainingPorts.counter).length + 10 →
        Trace (compiled (probeWith candidateCall) 0 0) prefixSteps
          (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * frameBound + 8 * (a.stacks remainingPorts.counter).length + 10 := by
  constructor
  · exact compiled_halt_trace (probe_exhausted_eval a hs hzero) 0 0
  · have hb := StructuredSpace.local_stack_bound (compiled (probeWith candidateCall) 0 0)
      (a := a.withPC (some (compiled (probeWith candidateCall) 0 0).entry))
      (steps := 8 * (a.stacks remainingPorts.counter).length + 10)
      (StreamResources.dataBits_le_mul _ hframe)
    simpa only [Nat.add_assoc] using hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

theorem advanceCandidateState_outside (a : State 40 896)
    (hs : a.stacks candidatePorts.scratch = []) (i : Fin 896)
    (hk : i ≠ tupleStacks 3) (hc : i ≠ candidatePorts.counter)
    (hr : i ≠ remainingPorts.counter) (ht : i ≠ remainingPorts.scratch) :
    (advanceCandidateState a).stacks i = a.stacks i := by
  change Function.update (advanceState a).stacks (tupleStacks 3) [] i = a.stacks i
  rw [Function.update_of_ne hk, advanceState_outside a hs i hc hr ht]


/-- The presence test does not change any stack, and cleanup leaves both
persistent prefix banks intact. -/
theorem checkedReturnState_stack (a : State 40 896) (i : Fin 896) :
    (rootAscendState a).stacks i = if i ∈ currentHeadPorts then [] else a.stacks i :=
  clearWordsState_stacks currentHeadPorts a i

section ParentReturn

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem cursorFrames_nonempty (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    cursorFrames h key (depth + 1) ancestors ≠ [] := by
  intro he
  have hl := congrArg List.length he
  rw [cursorFrames_pop, List.length_append, cursorFrame_length, List.length_nil] at hl
  omega

theorem checkedReturnState_active (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors) :
    (rootAscendState a).regs controllerPorts.active = true := by
  rw [rootAscendState, testParentState_flag, clearWordsState_stacks,
    ite_eq_right (by decide), hf]
  exact decide_eq_true (cursorFrames_nonempty h key depth ancestors)

theorem parentWordsState_fields (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) :
    (parentWordsState h key depth ancestors a).stacks (tupleStacks 0) =
        cursorFrames h key depth (Fin.init ancestors) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 1) =
        representativeFrames h key depth (Fin.init ancestors) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 2) =
        ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 7) =
        ExecCNFTupleEnumeration.fixedBits (h depth + 1)
          (2 ^ h depth - (ancestors (Fin.last depth)).val.val) ∧
      (parentWordsState h key depth ancestors a).stacks (tupleStacks 4) = [] :=
  returnFrames_state h key depth ancestors (rootAscendState a)


theorem parentWordsState_outside (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (i : Fin 896)
    (h0 : i ≠ tupleStacks 0) (h1 : i ≠ tupleStacks 1) (h2 : i ≠ tupleStacks 2)
    (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (parentWordsState h key depth ancestors a).stacks i = (rootAscendState a).stacks i := by
  unfold parentWordsState restoreCursorState
  rw [popWordState_outside _ _ _ _ _ _ _ h0 h2,
    popWordState_outside _ _ _ _ _ _ _ h0 h7]
  change Function.update (popWordState _ _ _ _ _ _).stacks (tupleStacks 4) [] i = _
  rw [Function.update_of_ne h4, popWordState_outside _ _ _ _ _ _ _ h1 h4]

theorem parentWordsState_register (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (parentWordsState h key depth ancestors a).regs j = (rootAscendState a).regs j := by
  unfold parentWordsState restoreCursorState
  rw [popWordState_register_frame _ _ _ _ _ _ j h0 h1,
    popWordState_register_frame _ _ _ _ _ _ j h0 h1]
  change readRegs (popWordState _ _ _ _ _ _).regs 0 1 none j = _
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1,
    popWordState_register_frame _ _ _ _ _ _ j h0 h1]

theorem ascendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (ascendLevelState a).stacks i = a.stacks i := by
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem ascendLevelState_active (a : State 40 896) :
    (ascendLevelState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  simp [ascendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    controllerPorts]

/-- The parent address and unary remaining-head word are reconstructed by
one paid ascent; no saved matrix or whole assignment table is retained. -/
theorem parent_return_ancestor_storage (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896)
    (ha : AncestorStorage h key levels base (depth + 1) ancestors a) :
    AncestorStorage h key levels base depth (Fin.init ancestors)
      (parentReturnState h key depth ancestors a) := by
  have hf := parentWordsState_fields h key depth ancestors a
  have hh : (parentWordsState h key depth ancestors a).stacks (tupleStacks 6) =
      List.replicate (levels - (depth + 1)) true := by
    rw [parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_right (by decide)]
    exact ha.heads
  have hz : (parentWordsState h key depth ancestors a).stacks (tupleStacks 9) =
      List.replicate (base + depth + 1) true := by
    rw [parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_right (by decide), ha.address]
    simp [Nat.add_assoc]
  have hl := ascendLevelState_words (parentWordsState h key depth ancestors a)
    (levels - (depth + 1)) (base + depth) hh hz
  refine ⟨by have := ha.depth_le; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [parentReturnState, hl.1]
    have hd := ha.depth_le
    congr 1
    omega
  · exact hl.2.1
  · rw [parentReturnState, ascendLevelState_active,
      parentWordsState_register _ _ _ _ _ _ (by decide) (by decide)]
    exact checkedReturnState_active h key depth ancestors a ha.cursors

theorem parent_return_cursor (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) :
    CursorWords (parentReturnState h key depth ancestors a) (h depth)
      (ancestors (Fin.last depth)).val.val := by
  have hf := parentWordsState_fields h key depth ancestors a
  have hcan : (parentReturnState h key depth ancestors a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val := by
    rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.2.1
  have hrem : (parentReturnState h key depth ancestors a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (h depth + 1)
        (2 ^ h depth - (ancestors (Fin.last depth)).val.val) := by
    rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.2.2.1
  refine ⟨(ancestors (Fin.last depth)).val.isLt.le, ?_, ?_, fun _ => hcan, hrem, ?_, ?_⟩
  · rw [hcan]
    exact ExecCNFTupleEnumeration.fixedBits_value _ _ (ancestors (Fin.last depth)).val.isLt
  · rw [hcan, ExecCNFTupleEnumeration.fixedBits_length]
    omega
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide),
      parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_left (by decide)]
  · rw [parentReturnState, ascendLevelState_outside _ _ (by decide) (by decide),
      parentWordsState_outside _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checkedReturnState_stack, ite_eq_left (by decide)]

end ParentReturn


theorem copyPredecessor_cursor (a : State 40 896) (h candidate : ℕ)
    (hw : CursorWords a h candidate) :
    CursorWords (copyState 651 (tupleStacks 8) a) h candidate := by
  have hf (i : Fin 896) (hi : i ≠ tupleStacks 8) :
      (copyState 651 (tupleStacks 8) a).stacks i = a.stacks i := by
    simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne hi]
  refine ⟨hw.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf _ (by decide)]; exact hw.value
  · rw [hf _ (by decide)]; exact hw.width
  · intro hc; rw [hf _ (by decide)]; exact hw.exact hc
  · rw [hf _ (by decide)]; exact hw.remaining
  · rw [hf _ (by decide)]; exact hw.incrementScratch
  · rw [hf _ (by decide)]; exact hw.decrementScratch

theorem parentReturnState_outside_tuple (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) :
    (parentReturnState h key depth ancestors a).stacks i = a.stacks i := by
  have hc : i ∉ currentHeadPorts := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨hi 2, hi 3, hi 4, hi 5, hi 7, hi 8, hi 10, hi 11⟩
  rw [parentReturnState, ascendLevelState_outside _ _ (hi 6) (hi 9),
    parentWordsState_outside _ _ _ _ _ _ (hi 0) (hi 1) (hi 2) (hi 4) (hi 7),
    checkedReturnState_stack, ite_eq_right hc]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleBranchSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix composition for the actual exhausted and leaf branches of the
attained-signature controller. The component executions are the installed
probe, visitor and ascent commands, and every caller stack is covered. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative

/-- An exhausted cursor takes the available=false branch, ascends, and
halts without allocating another word or invoking the leaf visitor. -/
theorem exhausted_body_prefix_bound (load visit : Cmd 40 896)
    (a b c : State 40 896) (np na D : ℕ)
    (hl : a.regs controllerPorts.leaf = false)
    (ha : b.regs controllerPorts.available = false)
    (hp : Eval (probeWith candidateCall) np a b)
    (hasc : Eval (ascendWith load) na b c)
    (hps : ∀ p q, p ≤ np → Trace (compiled (probeWith candidateCall) 0 0) p
      (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D)
    (has : ∀ p q, p ≤ na → Trace (compiled (ascendWith load) 0 0) p
      (b.withPC (some (compiled (ascendWith load) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D) :
    ∀ p q, p ≤ np + na + 3 →
      Trace (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines load candidateCall visit)) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D := by
  let freshBranch : Cmd 40 896 :=
    .ite controllerPorts.fresh (descendWith load) advanceCandidateCommand
  let availableBranch : Cmd 40 896 :=
    .ite controllerPorts.available freshBranch (ascendWith load)
  have hae : Eval availableBranch (na + 1) b c := .ite_false ha hasc
  have haspace := StructuredSpace.conditional_false_stack_bound
    (yes := freshBranch) ha hasc 0 0 has
    (compiled availableBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hseq := hp.seq hae
  have hsseq := StructuredSpace.sequence_stack_bound hp hae 0 0 hps haspace
    (compiled (.seq (probeWith candidateCall) availableBranch) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he : Eval (body controllerPorts (assembleRoutines load candidateCall visit))
      (np + (na + 1) + 1) a c := .ite_false hl hseq
  have hwhole := StructuredSpace.conditional_false_stack_bound
    (yes := .seq visit (ascendWith load)) hl hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hhalt := StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole
  intro p q hpq hq i
  exact hhalt p q (by omega) hq i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem result_high_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
    (result s z frame rp rm rs raw shifted).stacks i=frame.stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id i).trans
    (SignatureHeadLoader.lowResultFrom_frame headAddress _ _ i hi hne)

theorem result_low (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom headAddress frame)
        rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id (SignatureHeadLoader.lowStacks i)).trans
    (SignatureHeadLoader.lowResultFrom_low headAddress _ _ i h659 h668 h669)

theorem result_raw_empty (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 846=[] :=
  SignatureHeadLoader.leafOutputFrom_raw_empty headAddress frame _

/-- The source words and caches retain their exact values across the loader. -/
theorem result_masters (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (base : Data)
    (hf : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (result s z frame rp rm rs raw shifted)) := by
  apply SignatureHeadLoader.leafOutputFrom_masters
  exact (SignatureHeadLoader.leafInputFrom_masters headAddress frame base hf).trans
    (SignatureHeadLoader.localResult_masters ..)

section Storage
open SignatureTupleDFS SignatureTupleTraversal


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega

theorem parent_return_masters (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth+1)) (a : State 40 896) (base : Data)
    (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (parentReturnState h key depth ancestors a)) := by
  constructor
  intro i hi
  exact (parentReturnState_outside_tuple h key depth ancestors a
    (SignatureHeadLoader.lowStacks i) (low_outside_tuple i)).trans (hm.stored i hi)

/-- Reloading changes the current matrix, while the restored bounded
candidate and remaining-assignment words retain their exact values. -/
theorem result_cursor_words (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (h c : ℕ) (hw : CursorWords frame h c) :
    CursorWords (result s z frame rp rm rs raw shifted) h c := by
  have hc := result_high_frame s z frame rp rm rs raw shifted
    candidatePorts.counter (by decide) (by decide)
  have hr := result_high_frame s z frame rp rm rs raw shifted
    remainingPorts.counter (by decide) (by decide)
  have hs := result_high_frame s z frame rp rm rs raw shifted
    remainingPorts.scratch (by decide) (by decide)
  refine ⟨hw.range,?_,?_,?_,?_,?_,?_⟩
  · rw [hc]; exact hw.value
  · rw [hc]; exact hw.width
  · intro hn; rw [hc]; exact hw.exact hn
  · rw [hr]; exact hw.remaining
  · exact result_raw_empty ..
  · rw [hs]; exact hw.decrementScratch


/-- The native loader leaves its requested physical address on low649.
This is needed when a later pair restarts the same tuple traversal. -/
theorem result_address649 (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 649=frame.stacks headAddress := by
  change (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks 649)=_
  rw [result_low s z frame rp rm rs raw shifted 649 (by decide) (by decide) (by decide)]
  rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ 649
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact SignatureHeadLoader.addressStateFrom_value headAddress _ (by decide)


/-- Restoring the predecessor and advancing a resumed cursor leave the
freshly loaded parent address on low649. -/
theorem resume_loaded_address649 (a : State 40 896) (h c : ℕ)
    (hw : CursorWords a h c) :
    (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)).stacks 649=a.stacks 649 := by
  have hc := copyPredecessor_cursor a h c hw
  rw [advanceCandidateState_outside _ hc.incrementScratch 649
    (by decide) (by decide) (by decide) (by decide)]
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (by decide : (649:Fin 896)≠tupleStacks 8)]


end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
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

namespace ProducedSource

theorem headSize_le (s : ProducedSource) (depth : ℕ) : s.headSize depth ≤ s.input.n :=
  Bounds.selectedHeads_length ..

theorem source_offset (s : ProducedSource) (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    a.stacks 141=s.source.stacks 141 :=
  SignatureHeadLoader.native_offset_word s.input s.source s.addressRegisters s.dimensionRegisters
    s.cacheRegisters s.cacheWords _ hm

end ProducedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

/-- The concrete loader retains every persistent query word, including the
finite-ring caches that are not part of its own eighteen input masters. -/
theorem result_persistent (s : Native.Inputs) (z : ℕ) (a : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : PersistentPort i) :
    (result s z a rp rm rs raw shifted).stacks i=a.stacks i := by
  by_cases hlow : i.val < 768
  · let j : Fin 768 := ⟨i.val,hlow⟩
    have he : i=SignatureHeadLoader.lowStacks j := Fin.ext rfl
    have hne (q : Fin 768)
        (hm : SignatureHeadLoader.lowStacks q∈([649,650,651,652,659,668,669,670,671] : List (Fin 896))) :
        j≠q := by
      intro hj
      apply hi.head
      simpa only [he,hj] using hm
    have hj : Protected j := ⟨hi.outsideWork,hne 659 (by decide)⟩
    rw [he,result_low s z a rp rm rs raw shifted j
      (hne 659 (by decide)) (hne 668 (by decide))
      (hne 669 (by decide))]
    rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ j hj
      (hne 650 (by decide)) (hne 651 (by decide))
      (hne 652 (by decide)) (hne 668 (by decide))
      (hne 669 (by decide)) (hne 670 (by decide))
      (hne 671 (by decide))]
    have ha : i∉([649,659,846,847] : List (Fin 896)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨fun h => hi.head (by simp [h]),fun h => hi.head (by simp [h]),hi.tuple 10,hi.tuple 11⟩
    rw [he] at ha
    exact SignatureHeadLoader.addressStateFrom_frame 845 _ (SignatureHeadLoader.lowStacks j) ha
  · apply result_high_frame
    · omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hi.tuple 10,hi.tuple 11⟩

theorem resume_persistent (a : State 40 896) (h c : ℕ) (hw : CursorWords a h c)
    (i : Fin 896) (hi : PersistentPort i) :
    (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)).stacks i=a.stacks i := by
  have hc := copyPredecessor_cursor a h c hw
  rw [advanceCandidateState_outside _ hc.incrementScratch i
    (hi.tuple 3) (hi.tuple 2) (hi.tuple 7) (hi.tuple 5)]
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (hi.tuple 8)]


private theorem low_not_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  omega

private theorem resume_masters (s : ProducedSource) (a : State 40 896) (h c : ℕ)
    (hw : CursorWords a h c)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a))) := by
  constructor
  intro i hi
  have hc := copyPredecessor_cursor a h c hw
  change (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)).stacks
    (SignatureHeadLoader.lowStacks i)=_
  rw [advanceCandidateState_outside _ hc.incrementScratch _
    (low_not_tuple i 3) (low_not_tuple i 2) (low_not_tuple i 7) (low_not_tuple i 5)]
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (low_not_tuple i 8)]
  exact hm.stored i hi

/-- A nonroot return restores its attained parent, reconstructs only that
parent's matrix and advances its saved cursor once. -/
theorem ascend_parent (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (depth : Fin s.input.r) (ancestors : Prefix (Representatives s.key) (depth.val+1))
    (a : State 40 896)
    (ha : AncestorStorage s.headSize s.key s.input.r s.base (depth.val+1) ancestors a)
    (hb : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    ∃ n b, Eval (ascendWith loadHead) n a b ∧
      ScanBoundary s F depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) b ∧
      n+1 ≤ runEnvelope s.bound F+69*F+100 ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (ascendWith loadHead) 0 0) p
        (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hW := s.source_offset a hm
  obtain ⟨rp,rm,rs,raw,shifted,n,he,ht,hbound,hscan,hready,hraw,hshift,hprefix⟩ :=
    ascend_native_run s.headSize s.key s.input.r s.base depth ancestors s.input s.source
      s.ready s.bound s.bounded s.rows s.addressRegisters s.dimensionRegisters s.cacheRegisters
      s.cacheWords s.cache a hm ha F s.bound s.input.n hb
      (by simpa only [hW] using s.bounded 141) cap.output (fun d _ => s.headSize_le d) cap.frames rfl
  let parent := parentReturnState s.headSize s.key depth.val ancestors a
  let loaded := result s.input (s.base+depth.val) parent rp rm rs raw shifted
  let finish := advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) loaded)
  have hw := result_cursor_words s.input (s.base+depth.val) parent rp rm rs raw shifted _ _
    (parent_return_cursor s.headSize s.key depth.val ancestors a)
  have hloadedMasters : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks loaded) :=
    result_masters s.input (s.base+depth.val) parent rp rm rs raw shifted s.masters
      (parent_return_masters s.headSize s.key depth.val ancestors a s.masters hm)
  have hnext : ScanBoundary s F depth (Fin.init ancestors)
      ((ancestors (Fin.last depth.val)).val.val+1) finish := by
    refine ⟨hscan,hbound,resume_masters s loaded _ _ hw hloadedMasters,?_,?_⟩
    · constructor
      refine ⟨raw,shifted,hraw,?_,?_⟩
      · simpa only [hW] using hshift
      · intro hc
        simpa only [hW] using hready hc
    · rw [resume_loaded_address649 loaded _ _ hw,result_address649]
      exact (parent_return_ancestor_storage s.headSize s.key s.input.r s.base depth.val ancestors a ha).address
  refine ⟨n,finish,he,hnext,ht,?_,?_⟩
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    rw [resume_persistent loaded _ _ hw i hi,result_persistent _ _ _ _ _ _ _ _ i hi]
    exact parentReturnState_outside_tuple s.headSize s.key depth.val ancestors a i hi.tuple

/-- An exhausted nonroot generator performs the actual availability test
and paid parent return. It does not call the predecessor scanner. -/
theorem exhausted_successor_step_oai (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r) (hd : depth.val + 1 < s.input.r)
    (ancestors : Prefix (Representatives s.key) (depth.val+1)) (a : State 40 896)
    (ha : ScanBoundary s F ⟨depth.val+1,hd⟩ ancestors (2^s.headSize (depth.val+1)) a) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      ScanBoundary s F depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=true := by
    rw [ha.toCursorWords.available]
    simp
  let b := testAvailableState a
  have hstacks := testAvailableState_stacks a ha.decrementScratch
  have hb : WordBound F b := by
    intro i
    change ((testAvailableState a).stacks i).length ≤ F
    rw [hstacks]
    exact ha.bound i
  have hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
    constructor
    intro i hi
    exact (congrFun hstacks _).trans (ha.masters.stored i hi)
  have hanc : AncestorStorage s.headSize s.key s.input.r s.base (depth.val+1) ancestors b := by
    refine ⟨ha.depth_le,?_,?_,?_,?_,?_⟩
    · exact (congrFun hstacks _).trans ha.cursors
    · exact (congrFun hstacks _).trans ha.representatives
    · exact (congrFun hstacks _).trans ha.heads
    · exact (congrFun hstacks _).trans ha.address
    · exact (SignatureRescanBridge.test_available_register_frame a controllerPorts.active
        (by decide) (by decide)).trans ha.active
  obtain ⟨na,c,hasc,hnext,hta,hspacea,hframea⟩ := ascend_parent s F cap depth ancestors b hanc hb hm
  have hp := probe_exhausted_eval a ha.decrementScratch hzero
  have hav : b.regs controllerPorts.available=false := by rw [testAvailableState_flag,hzero]; rfl
  have hit : Iteration controllerPorts (assembleRoutines loadHead candidateCall visit)
      ((8*(a.stacks remainingPorts.counter).length+9)+na+2) a c :=
    .exhausted ha.leaf hp hav hasc
  refine ⟨_,c,hit,hnext,?_,?_,?_⟩
  · have hcounter := ha.bound remainingPorts.counter
    unfold eventPolynomial
    omega
  · apply SignatureTupleBranchSpace.exhausted_body_prefix_bound loadHead visit a b c _ na
      (prefixEnvelope s F) ha.leaf hav hp hasc
    · intro p q hpq hq i
      have hcounter := ha.bound remainingPorts.counter
      exact ((SignatureRescanBridge.exhausted_probe_space a F ha.decrementScratch hzero ha.bound).2
        p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)
    · intro p q hpq hq i
      exact hspacea p q (by omega) hq i

  · intro i hi
    exact (hframea i hi).trans (congrFun hstacks i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step_oai
