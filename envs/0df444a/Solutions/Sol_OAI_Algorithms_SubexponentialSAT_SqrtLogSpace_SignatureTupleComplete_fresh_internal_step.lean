-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:55:48.545348+00:00
-- url     : https://prove2.me/submissions/74a1e2f2-994f-41c5-850e-1cf1327394c3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureRescanBridge_probe_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_scan_kernel
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_descend_native_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_scanner_caps_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_probe_endpoint_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem duplicateScan_eq_true_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = true ↔ ∃ j < bound, key j = key candidate := by
  induction bound with
  | zero => simp [duplicateScan]
  | succ bound ih =>
    simp only [duplicateScan, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨j, hj, he⟩ | he)
      · exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
      · exact ⟨bound, Nat.lt_succ_self _, he⟩
    · rintro ⟨j, hj, he⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact Or.inl ⟨j, hj, he⟩
      · exact Or.inr he

theorem duplicateScan_eq_false_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = false ↔ ∀ j < bound, key j ≠ key candidate := by
  rw [← Bool.not_eq_true, duplicateScan_eq_true_iff]
  simp

theorem rescan_emits_iff [DecidableEq κ] (key : ℕ → κ) (i : Fin N) :
    duplicateScan key i i = false ↔ ∀ j : Fin N, j < i → key j ≠ key i := by
  rw [duplicateScan_eq_false_iff]
  constructor
  · intro h j hj
    exact h j hj
  · intro h j hj
    exact h ⟨j, hj.trans i.isLt⟩ hj

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedWords_length {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) : xs.length=ys.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => simpa using ih

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedMatrix_rowWidth {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (width : ℕ) (hw : ∀ row∈xs, row.length=width) :
    ∀ row∈ys, row.length=width := by
  induction h with
  | nil => simp
  | @cons a y xs ys hy hys ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (shiftedWords_length hy).symm.trans (hw a (by simp))
      · exact ih (fun a ha => hw a (by simp [ha])) z hz

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramCompatibility
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem matrixRel_dimensions {Rel : ℕ → ℕ → Pair → Prop} {B D : ℕ} {js : List ℕ}
    {rows : List (List Pair)} (h : MatrixRel Rel B D js rows) :
    rows.length=D ∧ ∀ row ∈ rows, row.length=js.length := by
  refine ⟨?_,?_⟩
  · simpa [MatrixRel] using h.length_eq.symm
  · intro row hr
    have aux : ∀ (is : List ℕ) (rs : List (List Pair)),
        List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
          is rs → ∀ row ∈ rs, row.length=js.length := by
      intro is rs hs
      induction hs with
      | nil => simp
      | cons hi ht ih =>
        intro row hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hi.length_eq.symm
        · exact ih row hr
    exact aux _ _ h row hr

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

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

/-- The physical shifted rows retain every incidence and the exact emitted
column order, including empty matrices and empty heads. -/
theorem shiftedMatrix_typed (W : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (B D : ℕ)
    (js : List ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys) :
    ∃ c : Fin D → Fin js.length → List Bool,
      ys = List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i, ∃ p, Rel j.val (js.get i) p ∧
        LayoutMatrixProgram.pairLength p ≤ B ∧ BucketProgram.shiftedWord W p (c j i) := by
  obtain ⟨hlen, hrow⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hylen : ys.length = D := hy.length_eq.symm.trans hlen
  have hyrow : ∀ row ∈ ys, row.length = js.length :=
    BucketProgram.shiftedMatrix_rowWidth hy js.length hrow
  let rowAt (j : Fin D) : List (List Bool) := ys.get ⟨j.val, by omega⟩
  have hrowAt (j : Fin D) : (rowAt j).length = js.length :=
    hyrow _ (List.get_mem _ _)
  let c (j : Fin D) (i : Fin js.length) : List Bool :=
    (rowAt j).get ⟨i.val, by rw [hrowAt]; exact i.isLt⟩
  refine ⟨c, ?_, ?_⟩
  · apply List.ext_get
    · simp [hylen]
    · intro j hj hj'
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      apply List.ext_get
      · simp [← hrowAt ⟨j, by simpa using hj'⟩, rowAt]
      · intro i hi hi'
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        rfl
  · intro j i
    have hjraw : j.val < raw.length := by omega
    have hjrange : j.val < (List.range D).length := by simp
    have hrawrow := hr.get hjrange hjraw
    simp only [List.get_eq_getElem, List.getElem_range] at hrawrow
    have hshiftrow := hy.get hjraw (by omega)
    have hiraw : i.val < (raw.get ⟨j.val,hjraw⟩).length := by
      change i.val < (raw[j.val]'hjraw).length
      rw [← hrawrow.length_eq]
      exact i.isLt
    have hiy : i.val < (ys.get ⟨j.val,by omega⟩).length := by
      exact (hrowAt j).symm ▸ i.isLt
    have hp := hrawrow.get i.isLt hiraw
    have hs := hshiftrow.get hiraw hiy
    exact ⟨_, hp.1, hp.2, hs⟩


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

theorem testAvailableState_flag (a : State 40 896) :
    (testAvailableState a).regs controllerPorts.available =
      !(CounterPrograms.isZero (a.stacks remainingPorts.counter)) :=
  CounterForPrograms.testResult_flag remainingPorts a

/-- Generic frame operations preserve every controller flag. -/
theorem pushWordState_register_frame (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (pushWordState src dst h a).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm

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

section Frames

open ExecCNFTupleEnumeration SignatureTupleProgram

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem representativeWords_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeWords h key (depth + 1) (Fin.snoc ancestors rep) =
      representativeWords h key depth ancestors ++ [fixedBits (h depth) rep.val.val] := by
  simp only [representativeWords, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append]
  rfl

theorem representativeFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      Encoding.frame (fixedBits (h depth) rep.val.val).reverse ++
        representativeFrames h key depth ancestors := by
  simp [representativeFrames, representativeWords_snoc, suspendedFrames, List.reverse_append]

theorem cursorFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      cursorFrame (h depth) rep.val.val ++ cursorFrames h key depth ancestors := by
  simp only [cursorFrames, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatten_cons]
  rfl

end Frames

section KeyEncoding

/-- The byte-key rescan's actual fresh bit is exactly the first-occurrence
predicate of the stable mathematical full signature. -/
theorem actual_fresh_iff_model {n : ℕ} {A B : Type*} [DecidableEq A]
    (actual : ℕ → A) (model : Fin n → B)
    (hkernel : ∀ i j : Fin n, actual i = actual j ↔ model i = model j)
    (candidate : Fin n) :
    (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      ∀ j, j < candidate → model j ≠ model candidate := by
  have hb : (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      AttainedSignatures.duplicateScan actual candidate candidate = false := by
    cases AttainedSignatures.duplicateScan actual candidate candidate <;> decide
  rw [hb, AttainedSignatures.rescan_emits_iff]
  constructor
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mpr he)
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mp he)

end KeyEncoding

section NativeFrames

open ExecCNFTupleEnumeration SignatureTupleProgram StructuredCalls

private theorem record_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

private theorem save_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hf : i ≠ tupleStacks 0) (hc : i ≠ tupleStacks 2) (hr : i ≠ tupleStacks 7) :
    (saveCursorState a).stacks i = a.stacks i := by
  unfold saveCursorState
  rw [pushWordState_outside _ _ _ _ _ hr hf, pushWordState_outside _ _ _ _ _ hc hf]

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- The actual record-then-save commands install precisely the dependent
child prefix in both persistent banks and empty their consumed words. -/
theorem retainFrames_state (depth : ℕ) (ancestors : Prefix (Representatives key) depth)
    (rep : Representatives key depth) (a : StructuredProgram.State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key depth ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key depth ancestors)
    (hc : a.stacks (tupleStacks 2) = fixedBits (h depth) rep.val.val)
    (hn : a.stacks (tupleStacks 7) = fixedBits (h depth + 1) (2 ^ h depth - rep.val.val))
    (hp : a.stacks (tupleStacks 4) = []) :
    let b := saveCursorState (recordRepresentativeState a)
    b.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 2) = [] ∧ b.stacks (tupleStacks 7) = [] ∧
    b.stacks (tupleStacks 4) = [] := by
  dsimp only
  have hs := saveCursorState_words (recordRepresentativeState a)
  have hrec := recordRepresentativeState_words a hp
  refine ⟨?_, ?_, hs.1, hs.2.1, ?_⟩
  · rw [hs.2.2, hrec.2.1, record_outside a (tupleStacks 7) (by decide) (by decide),
      record_outside a (tupleStacks 0) (by decide) (by decide), hc, hn, hf,
      cursorFrames_snoc, cursorFrame]
  · rw [save_outside _ (tupleStacks 1) (by decide) (by decide) (by decide),
      hrec.1, hc, hr, representativeFrames_snoc]
  · rw [save_outside _ (tupleStacks 4) (by decide) (by decide) (by decide), hrec.2.2]

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

theorem retainedState_register (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) : (retainedState a).regs j = a.regs j := by
  unfold retainedState saveCursorState recordRepresentativeState
  rw [pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

theorem descendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (descendLevelState a).stacks i = a.stacks i := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem descendLevelState_active (a : State 40 896) :
    (descendLevelState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    controllerPorts]

theorem descendClearState_stack (a : State 40 896) (i : Fin 896)
    (hi : i ∉ currentHeadPorts) :
    (descendClearState a).stacks i = (descendLevelState (retainedState a)).stacks i := by
  rw [descendClearState, clearWordsState_stacks, ite_eq_right hi]

theorem descendClearState_active (a : State 40 896) :
    (descendClearState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide),
    descendLevelState_active, retainedState_register _ _ (by decide) (by decide)]


/-- Current-head cleanup does not erase the newly attained child prefix or
its unary depth/address words. This also covers internal children. -/
theorem descend_ancestor_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (hd : depth < levels)
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4) = []) :
    AncestorStorage h key levels base (depth + 1) (Fin.snoc ancestors rep) (descendClearState a) := by
  have hf := retainFrames_state h key depth ancestors rep a
    ha.cursors ha.representatives (hw.exact rep.val.isLt) hw.remaining hp
  have heq : levels - depth = levels - (depth + 1) + 1 := by omega
  have hr : (retainedState a).stacks (tupleStacks 6) =
      List.replicate (levels - (depth + 1) + 1) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      ha.heads, heq]
  have hz : (retainedState a).stacks (tupleStacks 9) = List.replicate (base + depth) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha.address
  have hl := descendLevelState_words (retainedState a) (levels - (depth + 1)) (base + depth) hr hz
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [descendClearState_stack _ _ (by decide), hl.1]
  · rw [descendClearState_stack _ _ (by decide), hl.2.1]
    simp [Nat.add_assoc]
  · rw [descendClearState_active]
    exact ha.active

theorem resetState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (resetState a).stacks i = a.stacks i := by
  change (initialFuelState (copyState 651 (tupleStacks 4)
    (copyState 651 (tupleStacks 2) a))).stacks i = a.stacks i
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts _ _ _ _ _ _ i h4 h7]
  simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne h4, Function.update_of_ne h2]

theorem resetGeneratorState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7)
    (h8 : i ≠ tupleStacks 8) :
    (resetGeneratorState a).stacks i = a.stacks i := by
  change Function.update (resetState a).stacks (tupleStacks 8)
    ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) i = a.stacks i
  rw [Function.update_of_ne h8, resetState_outside a i h2 h4 h7]

theorem descendClearState_outside_tuple (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) : (descendClearState a).stacks i = a.stacks i := by
  have hc : i ∉ currentHeadPorts := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨hi 2, hi 3, hi 4, hi 5, hi 7, hi 8, hi 10, hi 11⟩
  rw [descendClearState_stack a i hc, descendLevelState_outside _ _ (hi 6) (hi 9),
    retainedState_outside _ _ (hi 0) (hi 1) (hi 2) (hi 4) (hi 7)]

theorem fresh_descent_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) (hf : i ≠ rescanStacks 22) :
    (descendClearState (probePostState a out W rows h candidate)).stacks i = a.stacks i := by
  rw [descendClearState_outside_tuple _ i hi]
  exact SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready hs i (hi 3) hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
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


/-- All raw incidence rows are present in the scanner, with polynomial
coefficient word lengths. No coordinate grid is materialized. -/
theorem shifted_rows_bounds (s : Native.Inputs) (z L : ℕ) (W : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hW : W.length≤L)
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    shifted.length=s.D ∧
      (∀ row∈shifted, row.length=(selectedHeads s.n s.rows s.low z).length) ∧
      ∀ row∈shifted, ∀ x∈row, x.length≤3*(s.columnLength+L)+1 := by
  obtain ⟨c,hc,hentry⟩ := SignatureHeadLoader.shiftedMatrix_typed W s.relation
    s.columnLength s.D (selectedHeads s.n s.rows s.low z) raw shifted hr hy
  subst shifted
  refine ⟨by simp, ?_, ?_⟩
  · intro row hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    simp
  · intro row hrow x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨pair,_,hpair,hshift⟩ := hentry j i
    have hlength := hshift.2
    unfold LayoutMatrixProgram.pairLength at hpair
    omega

section Storage
open SignatureTupleDFS SignatureTupleTraversal


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega

private theorem master_not_latch (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i≠rescanStacks 22 := by
  intro he
  have hv := congrArg Fin.val he
  have heq : i=(362 : Fin 768) := Fin.ext hv
  subst i
  exact (by decide : (362 : Fin 768)∉SignatureHeadLoader.masters) hi

/-- The actual probe and attained descent preserve every loader source word
and native cache; only bounded cursor frames and the scanner latch change. -/
theorem fresh_descent_masters (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2^h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch=[])
    (base : Data) (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (descendClearState (probePostState a out W rows h candidate))) := by
  constructor
  intro i hi
  exact (fresh_descent_stack_frame a out W rows h candidate ready hs
    (SignatureHeadLoader.lowStacks i) (low_outside_tuple i) (master_not_latch i hi)).trans
    (hm.stored i hi)


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

theorem reset_result_address649 (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (resetGeneratorState (result s z frame rp rm rs raw shifted)).stacks 649=frame.stacks headAddress := by
  rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
  exact result_address649 ..


/-- The source compiler's conditional and sequence rules compose one
actual fresh probe and actual descent on a single bounded-prefix run. -/
theorem fresh_body_prefix_bound (load visit : Cmd 40 896)
    (a b c : State 40 896) (np nd D : ℕ)
    (hl : a.regs controllerPorts.leaf=false)
    (ha : b.regs controllerPorts.available=true) (hf : b.regs controllerPorts.fresh=true)
    (hp : Eval (probeWith candidateCall) np a b)
    (hd : Eval (descendWith load) nd b c)
    (hps : ∀ p q, p≤np → Trace (compiled (probeWith candidateCall) 0 0) p
      (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) q →
      ∀ i,(q.stacks i).length≤D)
    (hds : ∀ p q, p≤nd → Trace (compiled (descendWith load) 0 0) p
      (b.withPC (some (compiled (descendWith load) 0 0).entry)) q →
      ∀ i,(q.stacks i).length≤D) :
    ∀ p q, p≤np+nd+4 →
      Trace (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines load candidateCall visit)) 0 0).entry)) q →
      ∀ i,(q.stacks i).length≤D := by
  let freshBranch : Cmd 40 896 := .ite controllerPorts.fresh (descendWith load) advanceCandidateCommand
  let availableBranch : Cmd 40 896 := .ite controllerPorts.available freshBranch (ascendWith load)
  have hfe : Eval freshBranch (nd+1) b c := .ite_true hf hd
  have hfs := StructuredSpace.conditional_true_stack_bound
    (no := advanceCandidateCommand) hf hd 0 0 hds
    (compiled freshBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have haveval : Eval availableBranch (nd+1+1) b c := .ite_true ha hfe
  have havspace := StructuredSpace.conditional_true_stack_bound
    (no := ascendWith load) ha hfe 0 0 hfs
    (compiled availableBranch 0 0) (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hseq := hp.seq haveval
  have hsseq := StructuredSpace.sequence_stack_bound hp haveval 0 0 hps havspace
    (compiled (.seq (probeWith candidateCall) availableBranch) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he : Eval (body controllerPorts (assembleRoutines load candidateCall visit))
      (np+(nd+1+1)+1) a c := .ite_false hl hseq
  have hwhole := StructuredSpace.conditional_false_stack_bound
    (yes := .seq visit (ascendWith load)) hl hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hhalt := StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole
  intro p q hpq hq i
  exact hhalt p q (by omega) hq i


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

theorem PersistentPort.not_fresh {i : Fin 896} (h : PersistentPort i) : i≠rescanStacks 22 := by
  intro he
  have hp := h.outsideWork
  have hv := congrArg Fin.val he
  change i.val=362 at hv
  rcases hp with hp|hp <;> omega

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

theorem reset_persistent (a : State 40 896) (i : Fin 896) (hi : PersistentPort i) :
    (resetGeneratorState a).stacks i=a.stacks i :=
  resetGeneratorState_outside a i (hi.tuple 2) (hi.tuple 4) (hi.tuple 7) (hi.tuple 8)

private theorem master_not_fresh (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i≠rescanStacks 22 := by
  simp only [SignatureHeadLoader.masters,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

private theorem low_not_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  omega

theorem reset_masters (s : ProducedSource) (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks (resetGeneratorState a)) := by
  constructor
  intro i hi
  exact (resetGeneratorState_outside a (SignatureHeadLoader.lowStacks i)
    (low_not_tuple i 2) (low_not_tuple i 4) (low_not_tuple i 7) (low_not_tuple i 8)).trans
    (hm.stored i hi)

private theorem probe_ancestors (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (candidate : Fin (2^h depth))
    (a : State 40 896) (out : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) candidate.val)
    (ready : CandidateReady a W rows (h depth) candidate) :
    AncestorStorage h key levels base depth ancestors
      (probePostState a out W rows (h depth) candidate) := by
  have frame (i : Fin 896) (hk : i≠rescanStacks 17) (hl : i≠rescanStacks 22) :=
    SignatureRescanBridge.probe_stack_frame a out W rows (h depth) candidate ready
      hw.decrementScratch i hk hl
  refine ⟨ha.depth_le,?_,?_,?_,?_,?_⟩
  · exact (frame _ (by decide) (by decide)).trans ha.cursors
  · exact (frame _ (by decide) (by decide)).trans ha.representatives
  · exact (frame _ (by decide) (by decide)).trans ha.heads
  · exact (frame _ (by decide) (by decide)).trans ha.address
  · exact (SignatureRescanBridge.probe_register_frame a out W rows (h depth) candidate
      controllerPorts.active (by decide) (by decide) (by decide)).trans ha.active

theorem candidate_descent_cost (candidate P S R F np nd fuel latch : ℕ)
    (hp : P ≤ S) (hf : fuel ≤ F) (hl : latch ≤ F)
    (hprobe : np ≤ (candidate+1)*P+8*fuel+2*latch+16)
    (hdesc : nd+1 ≤ R+100*F+100) :
    np+nd+3+1 ≤ (candidate+1)*(S+R+200*F+200) := by
  have hpc := Nat.mul_le_mul_left (candidate+1) hp
  have hm : R+200*F+200 ≤ (candidate+1)*(R+200*F+200) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (R+200*F+200)
      (show 1 ≤ candidate+1 by omega)
  calc
    _ ≤ (candidate+1)*S+(R+200*F+200) := by omega
    _ ≤ (candidate+1)*S+(candidate+1)*(R+200*F+200) := Nat.add_le_add_left hm _
    _=(candidate+1)*(S+R+200*F+200) := by ring


/-- A fresh nonfinal head runs the actual predicate and native child reload,
then starts that child's bounded zero cursor. The retained path contains only
first occurrences, never the raw Cartesian product of head assignments. -/
theorem fresh_internal_step_oai (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val)
    (rep : Representatives s.key depth.val) (a : State 40 896)
    (ha : ScanBoundary s F depth ancestors rep.val.val a) (hd : depth.val + 1 < s.input.r) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      ScanBoundary s F ⟨depth.val+1,hd⟩ (Fin.snoc ancestors rep) 0 b ∧
      n+1 ≤ (rep.val.val+1)*eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  obtain ⟨raw,shifted,hr,hy,hready⟩ := ha.matrix.data
  have ready := hready rep.val.isLt
  let C := 3*(s.input.columnLength+s.bound)+1
  have hshape := shifted_rows_bounds s.input (s.base+depth.val) s.bound
    (s.source.stacks 141) raw shifted (s.bounded 141) hr hy
  have hbud := scanner_caps_polynomial s.input s.source s.bound (s.base+depth.val)
    s.ready s.bounded (s.source.stacks 141) (s.bounded 141) raw shifted hr hy
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=false := by
    rw [ha.toCursorWords.available]
    simp only [Nat.ne_of_lt rep.val.isLt,decide_false]
  obtain ⟨np,hnp,out,hprobe,hprobeSpace⟩ := SignatureRescanBridge.probe_run_space a
    (s.source.stacks 141) shifted (s.headSize depth.val) C F hshape.2.1 hshape.2.2
    rep.val ready ha.decrementScratch hzero ha.bound
  let b := probePostState a out (s.source.stacks 141) shifted (s.headSize depth.val) rep.val
  have hb := probe_endpoint_bound a out (s.source.stacks 141) shifted (s.headSize depth.val)
    C F rep.val ready ha.decrementScratch hshape.2.1 hshape.2.2 ha.bound cap.positive
    (hbud.2.2.trans cap.scanner)
  have hcursor := SignatureRescanBridge.probe_preserves_cursor a out (s.source.stacks 141)
    shifted (s.headSize depth.val) rep.val ready ha.toCursorWords
  have hanc := probe_ancestors s.headSize s.key s.input.r s.base depth.val ancestors rep.val
    a out (s.source.stacks 141) shifted ha.toAncestorStorage ha.toCursorWords ready
  have frame (i : Fin 896) (hk : i≠rescanStacks 17) (hl : i≠rescanStacks 22) : b.stacks i=a.stacks i :=
    SignatureRescanBridge.probe_stack_frame a out (s.source.stacks 141) shifted
      (s.headSize depth.val) rep.val ready ha.decrementScratch i hk hl
  have hmasters : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
    constructor
    intro i hi
    exact (frame _ (low_not_tuple i 3) (master_not_fresh i hi)).trans (ha.masters.stored i hi)
  have hW : b.stacks 141=s.source.stacks 141 := (frame 141 (by decide) (by decide)).trans ready.offset
  have hp : b.stacks (tupleStacks 4)=[] := (frame _ (by decide) (by decide)).trans ha.payload
  obtain ⟨rp,rm,rs,childRaw,childShifted,nd,hdesc,hdt,hend,hscan,hchildReady,hraw,hshift,hdescSpace⟩ :=
    descend_native_run s.headSize s.key s.input.r s.base depth.val ancestors rep hd s.input
      s.source s.ready s.bound s.bounded s.rows s.addressRegisters s.dimensionRegisters
      s.cacheRegisters s.cacheWords s.cache b hmasters hanc hcursor hp F s.bound s.input.n hb
      (by simpa only [hW] using s.bounded 141) cap.output (fun d _ => s.headSize_le d) cap.frames rfl
  let finish := resetGeneratorState (result s.input (s.base+(depth.val+1))
    (descendClearState b) rp rm rs childRaw childShifted)
  have hflags := SignatureRescanBridge.probe_control_flags a out (s.source.stacks 141)
    shifted (s.headSize depth.val) rep.val hzero
  have hfresh : b.regs controllerPorts.fresh=true := by
    rw [hflags.2.2.2]
    exact (actual_fresh_iff_model _ _ (scan_kernel s depth.val raw shifted hr hy) rep.val).mpr rep.property
  have hnext : ScanBoundary s F ⟨depth.val+1,hd⟩ (Fin.snoc ancestors rep) 0 finish := by
    refine ⟨hscan,hend,?_,?_,?_⟩
    · apply reset_masters
      apply result_masters
      exact fresh_descent_masters a out (s.source.stacks 141) shifted (s.headSize depth.val)
        rep.val ready ha.decrementScratch s.masters ha.masters
    · constructor
      refine ⟨childRaw,childShifted,hraw,?_,?_⟩
      · simpa only [hW] using hshift
      · intro hc
        simpa only [hW] using hchildReady
    · rw [reset_result_address649]
      exact (descend_ancestor_storage s.headSize s.key s.input.r s.base depth.val ancestors rep b
        depth.isLt hanc hcursor hp).address
  have hit : Iteration controllerPorts (assembleRoutines loadHead candidateCall visit)
      (np+nd+3) a finish := .fresh ha.leaf hprobe hflags.2.2.1 hfresh hdesc
  refine ⟨_,finish,hit,hnext,?_,?_,?_⟩
  · exact candidate_descent_cost rep.val.val _ _ _ F np nd _ _ hbud.1
      (ha.bound remainingPorts.counter) (ha.bound (rescanStacks 22)) hnp hdt
  · apply fresh_body_prefix_bound loadHead visit a b finish np nd (prefixEnvelope s F)
      ha.leaf hflags.2.2.1 hfresh hprobe hdesc
    · intro p q hp hq i
      have hs : AttainedSignatureProgram.Rescan.spaceBudget (s.source.stacks 141)
          shifted (s.headSize depth.val) C ≤ F := hbud.2.1.trans cap.scanner
      have hcounter := ha.bound remainingPorts.counter
      have hlatch := ha.bound (rescanStacks 22)
      exact (hprobeSpace p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)
    · intro p q hp hq i
      exact (hdescSpace p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    rw [reset_persistent _ i hi,result_persistent _ _ _ _ _ _ _ _ i hi]
    exact fresh_descent_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
      rep.val ready ha.decrementScratch i hi.tuple hi.not_fresh

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step_oai
