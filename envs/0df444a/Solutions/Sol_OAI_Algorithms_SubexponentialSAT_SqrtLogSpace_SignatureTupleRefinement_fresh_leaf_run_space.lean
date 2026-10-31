-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:58:35.60452+00:00
-- url     : https://prove2.me/submissions/59736923-a5e7-47df-8345-d8d55088f7ea

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureRescanBridge_probe_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_probe_endpoint_bound
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

theorem conditional_true_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = true) (heval : StructuredCalls.Eval yes steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled yes inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled yes inputStack outputStack).entry)) intermediate →
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
    (b := a.withPC (some (StructuredCalls.entry yes (fun q => embed (some (.inl q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q)))

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

private theorem pushFrame_cycle (bit v present : Bool) (word frames : List Bool) :
    Trace pushFrameProgram 5
      (ParserProgram.cfg (some 2) v present (bit :: word) frames)
      (ParserProgram.cfg (some 2) true true word (true :: bit :: frames)) := by
  refine .cons (b := ParserProgram.cfg (some 3) bit true word frames) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr, readRegs]
  refine .cons (b := ParserProgram.cfg (some 4) bit true word frames) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  refine .cons (b := ParserProgram.cfg (some 5) bit true word (bit :: frames)) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  refine .cons (b := ParserProgram.cfg (some 6) true true word (bit :: frames)) ?_ ?_
  · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
  exact .cons (by simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]) (.refl _)

private theorem pushFrame_loop (word saved frames : List Bool) (v present : Bool) :
    Trace pushFrameProgram (5 * word.length + 3)
      (ParserProgram.cfg (some 2) v present word (Encoding.frame saved ++ frames))
      (ParserProgram.cfg none false false []
        (Encoding.frame (word.reverse ++ saved) ++ frames)) := by
  induction word generalizing saved v present with
  | nil =>
      refine .cons (b := ParserProgram.cfg (some 3) false false []
        (Encoding.frame saved ++ frames)) ?_ ?_
      · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr, readRegs]
      refine .cons (b := ParserProgram.cfg (some 7) false false []
        (Encoding.frame saved ++ frames)) ?_ ?_
      · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
      exact .cons (by simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]) (.refl _)
  | cons bit word ih =>
      have ht := (pushFrame_cycle bit v present word
        (Encoding.frame saved ++ frames)).trans (ih (bit :: saved) true true)
      have htime : 5 + (5 * word.length + 3) = 5 * (word.length + 1) + 3 := by omega
      simpa only [List.length_cons, htime, Encoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append,
        List.nil_append] using ht

/-- Exact fixed-table suspension, including initialization and halt. -/
theorem pushFrame_trace (word frames : List Bool) (v present : Bool) :
    Trace pushFrameProgram (5 * word.length + 5)
      (ParserProgram.cfg (some 0) v present word frames)
      (ParserProgram.cfg none false false [] (Encoding.frame word.reverse ++ frames)) := by
  have ht := pushFrame_loop word [] frames false present
  have ht' : Trace pushFrameProgram (5 * word.length + 3 + 1 + 1)
      (ParserProgram.cfg (some 0) v present word frames)
      (ParserProgram.cfg none false false [] (Encoding.frame word.reverse ++ frames)) := by
    refine .cons (b := ParserProgram.cfg (some 1) false present word frames) ?_ ?_
    · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
    refine .cons (b := ParserProgram.cfg (some 2) false present word (false :: frames)) ?_ ?_
    · simp [step, pushFrameProgram, ParserProgram.cfg, execInstr]
    simpa [Encoding.frame] using ht
  simpa only [Nat.add_assoc] using ht'

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ he => congrArg g he) g a
  · exact Function.extend_apply' _ _ _ h

private theorem word_embed_self (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) :
    embedState frameRegisters (wordPorts src dst h) a
      (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)) = a := by
  apply CounterForPrograms.data_ext
  · have hr : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).regs =
        a.regs ∘ frameRegisters := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend frameRegisters _ a.regs = a.regs
    rw [hr, extend_restrict_eq]
  · have hs : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).stacks =
        a.stacks ∘ wordPorts src dst h := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend (wordPorts src dst h) _ a.stacks = a.stacks
    rw [hs, extend_restrict_eq]

theorem pushWord_eval (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    Eval (pushWordCommand src dst h) (5 * (a.stacks src).length + 5) a
      (pushWordState src dst h a) := by
  have ht := eval_call_lifted pushFrameProgram frameRegisters (wordPorts src dst h) a
    frameRegisters.injective (wordPorts src dst h).injective
    (a := frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst))
    (b := frameState false false [] (Encoding.frame (a.stacks src).reverse ++ a.stacks dst))
    (pushFrame_trace (a.stacks src) (a.stacks dst) (a.regs 0) (a.regs 1))
  rw [word_embed_self] at ht
  exact ht

theorem pushWordState_src (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks src = [] :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem pushWordState_dst (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks dst =
      Encoding.frame (a.stacks src).reverse ++ a.stacks dst :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem pushWordState_outside (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (pushWordState src dst h a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

theorem saveCursor_eval (a : State 40 896) :
    Eval saveCursorCommand
      (5 * (a.stacks (tupleStacks 2)).length + 5 * (a.stacks (tupleStacks 7)).length + 10)
      a (saveCursorState a) := by
  have ht := Eval.seq (pushWord_eval (tupleStacks 2) (tupleStacks 0) (by decide) a)
    (pushWord_eval (tupleStacks 7) (tupleStacks 0) (by decide) _)
  have hw := pushWordState_outside (tupleStacks 2) (tupleStacks 0) (by decide) a
    (tupleStacks 7) (by decide) (by decide)
  change Eval saveCursorCommand _ a (saveCursorState a) at ht
  rw [hw] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem saveCursorState_words (a : State 40 896) :
    (saveCursorState a).stacks (tupleStacks 2) = [] ∧
      (saveCursorState a).stacks (tupleStacks 7) = [] ∧
      (saveCursorState a).stacks (tupleStacks 0) =
        Encoding.frame (a.stacks (tupleStacks 7)).reverse ++
          Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 0) := by
  constructor
  · unfold saveCursorState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide), pushWordState_src]
  constructor
  · exact pushWordState_src _ _ _ _
  · unfold saveCursorState
    rw [pushWordState_dst, pushWordState_dst,
      pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    exact List.append_assoc _ _ _ |>.symm

theorem recordRepresentative_eval (a : State 40 896)
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = []) :
    Eval recordRepresentativeCommand (12 * (a.stacks (tupleStacks 2)).length + 10) a
      (recordRepresentativeState a) := by
  have hc := copyWord_eval (tupleStacks 2) (tupleStacks 4) (tupleStacks 5)
    (by decide) (by decide) (by decide) a ht
  have hh := Eval.seq hc (pushWord_eval (tupleStacks 4) (tupleStacks 1) (by decide) _)
  have hw : (copyState (tupleStacks 2) (tupleStacks 4) a).stacks (tupleStacks 4) =
      a.stacks (tupleStacks 2) := by simp [copyState, hp]
  change Eval recordRepresentativeCommand _ a (recordRepresentativeState a) at hh
  rw [hw] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem recordRepresentativeState_words (a : State 40 896)
    (hp : a.stacks (tupleStacks 4) = []) :
    (recordRepresentativeState a).stacks (tupleStacks 1) =
        Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 1) ∧
      (recordRepresentativeState a).stacks (tupleStacks 2) = a.stacks (tupleStacks 2) ∧
      (recordRepresentativeState a).stacks (tupleStacks 4) = [] := by
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_dst]
    simp [copyState, StackRoutines.copyStacks, hp]
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    simp [copyState, StackRoutines.copyStacks]
  · exact pushWordState_src _ _ _ _

theorem descendLevel_eval (a : State 40 896) :
    Eval descendLevelCommand 5 a (descendLevelState a) :=
  .base (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))))

theorem descendLevelState_words (a : State 40 896) (remaining address : ℕ)
    (hr : a.stacks (tupleStacks 6) = List.replicate (remaining + 1) true)
    (ha : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendLevelState a).stacks (tupleStacks 6) = List.replicate remaining true ∧
      (descendLevelState a).stacks (tupleStacks 9) = List.replicate (address + 1) true ∧
      (descendLevelState a).regs controllerPorts.leaf = decide (remaining = 0) := by
  have h69 : tupleStacks 6 ≠ tupleStacks 9 := by decide
  cases remaining <;>
    simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hr, ha, List.replicate_succ, controllerPorts, h69, Ne.symm h69]

theorem clearWord_eval (src : Fin 896) (a : State 40 896) :
    Eval (clearWord src) (2 * (a.stacks src).length + 3) a (clearState src a) := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  exact .call _ (by simpa [clearState, StackRoutines.clearResult, StackRoutines.clearStacks,
    StructuredProgram.State.withPC, StackRoutines.clearProgram, Nat.add_assoc] using hh)

theorem clearWords_eval (ports : List (Fin 896)) (a : State 40 896) :
    Eval (clearWords ports) (clearWordsTime ports a) a (clearWordsState ports a) := by
  induction ports generalizing a with
  | nil => exact .base (.skip _)
  | cons src rest ih => exact .seq (clearWord_eval src a) (ih _)

theorem testAvailableState_flag (a : State 40 896) :
    (testAvailableState a).regs controllerPorts.available =
      !(CounterPrograms.isZero (a.stacks remainingPorts.counter)) :=
  CounterForPrograms.testResult_flag remainingPorts a

theorem clearWordsState_register_frame (ports : List (Fin 896))
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (clearWordsState ports a).regs i = a.regs i := by
  induction ports generalizing a with
  | nil => rfl
  | cons src rest ih =>
    rw [clearWordsState, ih]
    exact StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1

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

section NativeFrames

open ExecCNFTupleEnumeration SignatureTupleProgram StructuredCalls

private theorem record_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem retainFrames_eval (width candidate : ℕ) (a : StructuredProgram.State 40 896)
    (hc : a.stacks (tupleStacks 2) = fixedBits width candidate)
    (hn : a.stacks (tupleStacks 7) = fixedBits (width + 1) (2 ^ width - candidate))
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = []) :
    Eval (.seq recordRepresentativeCommand saveCursorCommand) (22 * width + 25) a
      (saveCursorState (recordRepresentativeState a)) := by
  have he := (recordRepresentative_eval a hp ht).seq
    (saveCursor_eval (recordRepresentativeState a))
  rw [(recordRepresentativeState_words a hp).2.1,
    record_outside a (tupleStacks 7) (by decide) (by decide), hc, hn] at he
  simp only [fixedBits_length] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  omega

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

theorem initializeFreshState_word (a : State 40 896) :
    (initializeFreshState a).stacks (rescanStacks 22) = [false] := by
  simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, clearState]

theorem rescan_embed_controller (frame : State 40 896) (callee : State 16 24)
    (j : Fin 40) (hj : 16 ≤ j.val) :
    (embedState rescanRegisters rescanStacks frame callee).regs j = frame.regs j := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  dsimp [rescanRegisters] at hv
  omega

theorem candidateOutput_flag (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val) :
    (candidateOutput frame regs W rows h candidate).regs j = frame.regs j :=
  rescan_embed_controller _ _ j hj

theorem candidateOutput_fresh (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) :
    (candidateOutput frame regs W rows h candidate).stacks (rescanStacks 22) =
      [!(AttainedSignatures.duplicateScan
        (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate)] := by
  rw [candidateOutput, embedState_stack _ _ _ _ rescanStacks.injective]
  rfl


theorem testAvailableState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (testAvailableState a).stacks = a.stacks :=
  CounterForPrograms.testResult_stacks remainingPorts a hs

theorem initializeFreshState_controller (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (initializeFreshState a).regs j = a.regs j := by
  simp only [initializeFreshState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    execInstr, Function.update_of_ne h0]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

theorem probePostState_flags (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W rows h candidate).regs controllerPorts.available = true ∧
      (probePostState a out W rows h candidate).regs controllerPorts.fresh =
        !(AttainedSignatures.duplicateScan
          (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) := by
  have hw := candidateOutput_fresh (probePreState a) out W rows h candidate
  simp only [rescanStacks_fresh] at hw
  have hav : (candidateOutput (probePreState a) out W rows h candidate).regs
      controllerPorts.available = true := by
    rw [candidateOutput_flag _ _ _ _ _ _ _ (by decide)]
    rw [probePreState, initializeFreshState_controller _ _ (by decide) (by decide)]
    rw [testAvailableState_flag, hnonzero]
    rfl
  constructor
  · simpa [probePostState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hw, controllerPorts] using hav
  · simp [probePostState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hw, controllerPorts]


theorem initializeFreshState_stacks (a : State 40 896) :
    (initializeFreshState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  funext i
  by_cases hi : i = rescanStacks 22
  · subst i
    rw [Function.update_self, initializeFreshState_word]
  · simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, clearState]

theorem probePreState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePreState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  rw [probePreState, initializeFreshState_stacks, testAvailableState_stacks a hs]

/-- Preparing a candidate changes only the latch word. The whole fixed local
input projection is then the one used in the proved native rescan theorem. -/
theorem CandidateReady.probe_projection {a : State 40 896} {W : List Bool}
    {rows : List (List (List Bool))} {h : ℕ} {candidate : Fin (2 ^ h)}
    (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    projectState rescanRegisters rescanStacks (probePreState a) =
      AttainedSignatureProgram.Rescan.workState
        ((probePreState a).regs ∘ rescanRegisters) W rows
        (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change (probePreState a).stacks (rescanStacks i) = _
  rw [probePreState_stacks a hs]
  have hf (j : Fin 24) (hj : j ≠ 22) : rescanStacks j ≠ rescanStacks 22 :=
    fun he => hj (rescanStacks.injective he)
  by_cases h22 : i = 22
  · subst i
    rw [Function.update_self]
    rfl
  rw [Function.update_of_ne (hf i h22)]
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  by_cases h16 : i = 16
  · subst i; exact ready.current
  by_cases h17 : i = 17
  · subst i; exact ready.saved
  by_cases h18 : i = 18
  · subst i; exact ready.predecessor
  rw [ready.scratch i h0 h15 h16 h17 h18 h22]
  fin_cases i <;> simp_all

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

theorem probe_stacks (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePostState a out W rows h candidate).stacks =
      Function.update (Function.update a.stacks (rescanStacks 17)
        (naturalKey W rows h candidate)) (rescanStacks 22)
        [!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)] := by
  classical
  let pre := probePreState a
  let initial := workState (pre.regs ∘ rescanRegisters) W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) []
    (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] []
  let key := naturalKey W rows h candidate
  let fresh := !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)
  have hz : ExecCNFTupleEnumeration.fixedBits h 0 = List.replicate h false :=
    ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
      (by simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))])
  have hlocal : (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      key (List.replicate h false) [] fresh [] []).stacks =
      Function.update (Function.update initial.stacks 17 key) 22 [fresh] := by
    dsimp [initial]
    rw [hz]
    funext i
    fin_cases i <;> simp [workState]
  have hemb : Function.extend rescanStacks initial.stacks pre.stacks = pre.stacks := by
    change (embedState rescanRegisters rescanStacks pre initial).stacks = pre.stacks
    have hi : projectState rescanRegisters rescanStacks pre = initial := ready.probe_projection hs
    rw [← hi, embedState_project _ _ _ rescanRegisters.injective rescanStacks.injective]
  change Function.extend rescanStacks _ pre.stacks = _
  rw [hlocal, ProgramLinking.extend_update rescanStacks.injective,
    ProgramLinking.extend_update rescanStacks.injective, hemb]
  change Function.update (Function.update (probePreState a).stacks (rescanStacks 17) key)
    (rescanStacks 22) [fresh] = _
  rw [probePreState_stacks a hs]
  funext j
  by_cases h17 : j = rescanStacks 17
  · subst j
    simp only [Function.update_self, Function.update_of_ne
      (by decide : rescanStacks 17 ≠ rescanStacks 22)]
    rfl
  · by_cases h22 : j = rescanStacks 22
    · subst j; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne h17, Function.update_of_ne h22]

theorem probe_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (j : Fin 896)
    (hk : j ≠ rescanStacks 17) (hf : j ≠ rescanStacks 22) :
    (probePostState a out W rows h candidate).stacks j = a.stacks j := by
  rw [probe_stacks a out W rows h candidate ready hs]
  rw [Function.update_of_ne hf, Function.update_of_ne hk]

theorem probe_preserves_cursor (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (cursor : CursorWords a h candidate) :
    CursorWords (probePostState a out W rows h candidate) h candidate := by
  have hc := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.counter (by decide) (by decide)
  have hr := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.counter (by decide) (by decide)
  have hcs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.scratch (by decide) (by decide)
  have hrs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.scratch (by decide) (by decide)
  exact ⟨cursor.range, hc ▸ cursor.value, hc ▸ cursor.width,
    fun hi => hc.trans (cursor.exact hi), hr.trans cursor.remaining,
    hcs.trans cursor.incrementScratch, hrs.trans cursor.decrementScratch⟩

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

theorem probe_register_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val)
    (ha : j ≠ controllerPorts.available) (hf : j ≠ controllerPorts.fresh) :
    (probePostState a out W rows h candidate).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro he; subst j; norm_num at hj
  change readRegs (candidateOutput (probePreState a) out W rows h candidate).regs
    controllerPorts.fresh 0 _ j = _
  rw [StackRoutines.readRegs_frame _ _ _ _ _ hf h0,
    candidateOutput_flag _ _ _ _ _ _ _ hj]
  rw [probePreState, initializeFreshState_controller _ _ h0 h1]
  exact test_available_register_frame a j (by omega) ha

theorem probe_control_flags (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h))
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false) :
    (probePostState a out W rows h candidate).regs controllerPorts.active =
        a.regs controllerPorts.active ∧
      (probePostState a out W rows h candidate).regs controllerPorts.leaf =
        a.regs controllerPorts.leaf ∧
      (probePostState a out W rows h candidate).regs controllerPorts.available = true ∧
      (probePostState a out W rows h candidate).regs controllerPorts.fresh =
        !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate) :=
  ⟨probe_register_frame a out W rows h candidate _ (by decide) (by decide) (by decide),
    probe_register_frame a out W rows h candidate _ (by decide) (by decide) (by decide),
    probePostState_flags a out W rows h candidate hnonzero⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

theorem recordRepresentative_outside (a : State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

theorem retainedState_outside (a : State 40 896) (i : Fin 896)
    (h0 : i ≠ tupleStacks 0) (h1 : i ≠ tupleStacks 1)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (retainedState a).stacks i = a.stacks i := by
  unfold retainedState saveCursorState
  rw [pushWordState_outside _ _ _ _ _ h7 h0,
    pushWordState_outside _ _ _ _ _ h2 h0, recordRepresentative_outside a i h1 h4]

theorem descendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (descendLevelState a).stacks i = a.stacks i := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem descendClearState_leaf (a : State 40 896) (address : ℕ)
    (hr : a.stacks (tupleStacks 6) = [true])
    (hz : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendClearState a).regs controllerPorts.leaf = true := by
  have hw := descendLevelState_words (retainedState a) 0 address
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz)
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide)]
  exact hw.2.2

theorem seq_reassociate {first second third : Cmd 40 896} {n : ℕ} {a b : State 40 896}
    (he : Eval (.seq (.seq first second) third) n a b) :
    Eval (.seq first (.seq second third)) n a b := by
  cases he with
  | seq hab hc =>
    cases hab with
    | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)

/-- The last fresh representative reaches an actual leaf only after its
cursor is saved and all eight current-head tapes have been cleared. -/
theorem descend_leaf_eval (loadHead : Cmd 40 896) (a : State 40 896)
    (width candidate address : ℕ)
    (hc : a.stacks (tupleStacks 2) = ExecCNFTupleEnumeration.fixedBits width candidate)
    (hn : a.stacks (tupleStacks 7) =
      ExecCNFTupleEnumeration.fixedBits (width + 1) (2 ^ width - candidate))
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hr : a.stacks (tupleStacks 6) = [true])
    (hz : a.stacks (tupleStacks 9) = List.replicate address true) :
    Eval (descendWith loadHead)
      (22 * width + 31 + clearWordsTime currentHeadPorts (descendLevelState (retainedState a)))
      a (descendClearState a) := by
  have hf := retainFrames_eval width candidate a hc hn hp ht
  have hl := descendLevel_eval (retainedState a)
  have hclear := clearWords_eval currentHeadPorts (descendLevelState (retainedState a))
  have hbranch : Eval (.ite controllerPorts.leaf (.base .skip)
      (.seq loadHead resetGeneratorCommand)) 1 (descendClearState a) (descendClearState a) :=
    .ite_true (descendClearState_leaf a address hr hz) (.base (.skip _))
  have he := seq_reassociate (hf.seq (hl.seq (hclear.seq hbranch)))
  change Eval (descendWith loadHead) _ a (descendClearState a) at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  omega


theorem clearWordsTime_le_on (ports : List (Fin 896)) (a : State 40 896) (B : ℕ)
    (hb : ∀ i ∈ ports, (a.stacks i).length ≤ B) :
    clearWordsTime ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => simp [clearWordsTime]
  | cons src rest ih =>
    have hsrc := hb src (by simp)
    have hrest : ∀ i ∈ rest, ((clearState src a).stacks i).length ≤ B := by
      intro i hi
      by_cases he : i = src
      · subst i
        simp [clearState]
      · simpa [clearState, he] using hb i (by simp [hi])
    have htail := ih (clearState src a) hrest
    simp only [clearWordsTime, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Recording a representative grows only the two persistent frame banks.
The tapes cleared on descent remain bounded by their original word cap. -/
theorem descend_current_bound (a : State 40 896) (F : ℕ)
    (hp : a.stacks (tupleStacks 4) = []) (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ i ∈ currentHeadPorts, ((descendLevelState (retainedState a)).stacks i).length ≤ F := by
  have hwords := saveCursorState_words (recordRepresentativeState a)
  have hpayload : (retainedState a).stacks (tupleStacks 4) = [] := by
    unfold retainedState saveCursorState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide),
      pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    exact (recordRepresentativeState_words a hp).2.2
  intro i hi
  have hports : i ≠ tupleStacks 0 ∧ i ≠ tupleStacks 1 ∧
      i ≠ tupleStacks 6 ∧ i ≠ tupleStacks 9 := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [descendLevelState_outside _ _ hports.2.2.1 hports.2.2.2]
  by_cases h2 : i = tupleStacks 2
  · subst i
    rw [show (retainedState a).stacks (tupleStacks 2) = [] from hwords.1]
    simp
  · by_cases h7 : i = tupleStacks 7
    · subst i
      rw [show (retainedState a).stacks (tupleStacks 7) = [] from hwords.2.1]
      simp
    · by_cases h4 : i = tupleStacks 4
      · subst i
        rw [hpayload]
        simp
      · rw [retainedState_outside a i hports.1 hports.2.1 h2 h4 h7]
        exact hframe i

/-- Descent stores only one bounded representative and cursor. Its local
prefix bound counts all caller stacks and does not use the rescan's time. -/
theorem descend_leaf_stack_bound (loadHead : Cmd 40 896) (a : State 40 896)
    (width F : ℕ) (hp : a.stacks (tupleStacks 4) = [])
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ 22 * width + 32 +
        clearWordsTime currentHeadPorts (descendLevelState (retainedState a)) →
      Trace (compiled (descendWith loadHead) 0 0) prefixSteps
        (a.withPC (some (compiled (descendWith loadHead) 0 0).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        896 * F + 22 * width + 8 * (2 * F + 3) + 32 := by
  have hc := clearWordsTime_le_on currentHeadPorts _ F (descend_current_bound a F hp hframe)
  change clearWordsTime currentHeadPorts _ ≤ 8 * (2 * F + 3) at hc
  have hb := StructuredSpace.local_stack_bound (compiled (descendWith loadHead) 0 0)
    (a := a.withPC (some (compiled (descendWith loadHead) 0 0).entry))
    (steps := 22 * width + 8 * (2 * F + 3) + 32)
    (StreamResources.dataBits_le_mul _ hframe)
  intro p q hp hq i
  exact (hb p q (by omega) hq i).trans (by omega)

/-- The fresh final-head branch has the same uniform prefix cap as a losing
candidate: the rescan uses its own bound, while frame storage and cleanup
are charged by their polynomial local execution time. -/
theorem fresh_leaf_run_space_oai (loadHead visit : Cmd 40 896) (a : State 40 896)
    (W : List Bool) (rows : List (List (List Bool))) (h B F address : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hw : CursorWords a h candidate.val)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hleaf : a.regs controllerPorts.leaf = false)
    (hfresh : Bool.not (AttainedSignatures.duplicateScan
      (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate) = true)
    (hpayload : a.stacks (tupleStacks 4) = [])
    (hheads : a.stacks (tupleStacks 6) = [true])
    (haddress : a.stacks (tupleStacks 9) = List.replicate address true)
    (hframe : ∀ i, (a.stacks i).length ≤ F) (hpositive : 1 ≤ F) (hcursor : h + 1 ≤ F)
    (hkey : AttainedSignatureProgram.Rescan.keyBound W h rows.length B ≤ F)
    (hspace : AttainedSignatureProgram.Rescan.spaceBudget W rows h B ≤ F) :
    ∃ n out,
      Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit)) n a
        (descendClearState (probePostState a out W rows h candidate)) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
          prefixSteps (a.withPC (some (compiled
            (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ (candidate.val + 1) *
        (AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 64 * F + 100) := by
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false := by
    rw [hw.available]
    simp only [Nat.ne_of_lt candidate.isLt, decide_false]
  obtain ⟨np, hnp, out, hp, hpSpace⟩ := SignatureRescanBridge.probe_run_space
    a W rows h B F hlen hwidth candidate ready hw.decrementScratch hzero hframe
  let b := probePostState a out W rows h candidate
  have hb := probe_endpoint_bound a out W rows h B F candidate ready hw.decrementScratch
    hlen hwidth hframe hpositive hkey
  have hwords := SignatureRescanBridge.probe_preserves_cursor a out W rows h candidate ready hw
  have hflags := SignatureRescanBridge.probe_control_flags a out W rows h candidate hzero
  have hbranch : b.regs controllerPorts.fresh = true := hflags.2.2.2.trans hfresh
  have hf (i : Fin 896) (hk : i ≠ rescanStacks 17) (hl : i ≠ rescanStacks 22) :
      b.stacks i = a.stacks i :=
    SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready hw.decrementScratch i hk hl
  have hbp : b.stacks (tupleStacks 4) = [] := by
    rw [hf _ (by decide) (by decide)]; exact hpayload
  have hbr : b.stacks (tupleStacks 6) = [true] := by
    rw [hf _ (by decide) (by decide)]; exact hheads
  have hbz : b.stacks (tupleStacks 9) = List.replicate address true := by
    rw [hf _ (by decide) (by decide)]; exact haddress
  have hd := descend_leaf_eval loadHead b h candidate address
    (hwords.exact candidate.isLt) hwords.remaining hbp hwords.decrementScratch hbr hbz
  let nd := 22 * h + 31 + clearWordsTime currentHeadPorts (descendLevelState (retainedState b))
  have hclear := clearWordsTime_le_on currentHeadPorts _ F (descend_current_bound b F hbp hb)
  change clearWordsTime currentHeadPorts _ ≤ 8 * (2 * F + 3) at hclear
  have hnd : nd ≤ 38 * F + 55 := by dsimp only [nd]; omega
  have hps : ∀ p q, p ≤ np → Trace (compiled (probeWith candidateCall) 0 0) p
      (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ 2000 * (F + 1) := by
    intro p q hpn hq i
    have hs := hpSpace p q (by omega) hq i
    have hr := hframe remainingPorts.counter
    have hf' := hframe (rescanStacks 22)
    omega
  have hds : ∀ p q, p ≤ nd → Trace (compiled (descendWith loadHead) 0 0) p
      (b.withPC (some (compiled (descendWith loadHead) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ 2000 * (F + 1) := by
    have hh := descend_leaf_stack_bound loadHead b h F hbp hb
    intro p q hpn hq i
    exact (hh p q (by dsimp only [nd] at hpn; omega) hq i).trans (by omega)
  let freshBranch : Cmd 40 896 := .ite controllerPorts.fresh (descendWith loadHead) advanceCandidateCommand
  let availableBranch : Cmd 40 896 := .ite controllerPorts.available freshBranch (ascendWith loadHead)
  have hfe : Eval freshBranch (nd + 1) b (descendClearState b) := .ite_true hbranch hd
  have hfs := StructuredSpace.conditional_true_stack_bound
    (no := advanceCandidateCommand) hbranch hd 0 0 hds
    (compiled freshBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have haveval : Eval availableBranch (nd + 1 + 1) b (descendClearState b) :=
    .ite_true hflags.2.2.1 hfe
  have havspace := StructuredSpace.conditional_true_stack_bound
    (no := ascendWith loadHead) hflags.2.2.1 hfe 0 0 hfs
    (compiled availableBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hseq := hp.seq haveval
  have hsseq := StructuredSpace.sequence_stack_bound hp haveval 0 0 hps havspace
    (compiled (.seq (probeWith candidateCall) availableBranch) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he : Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit))
      (np + (nd + 1 + 1) + 1) a (descendClearState b) := .ite_false hleaf hseq
  have hwhole := StructuredSpace.conditional_false_stack_bound
    (yes := .seq visit (ascendWith loadHead)) hleaf hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  refine ⟨_, out, he, StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole, ?_⟩
  have hr := hframe remainingPorts.counter
  have hf' := hframe (rescanStacks 22)
  have hm : 64 * F + 100 ≤ (candidate.val + 1) * (64 * F + 100) := by
    simpa only [one_mul] using
      (Nat.mul_le_mul_right (64 * F + 100) (show 1 ≤ candidate.val + 1 by omega))
  calc
    _ ≤ (candidate.val + 1) * AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        (64 * F + 100) := by omega
    _ ≤ (candidate.val + 1) * AttainedSignatureProgram.Rescan.polynomialBudget W rows h B +
        (candidate.val + 1) * (64 * F + 100) := Nat.add_le_add_left hm _
    _ = _ := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space_oai
