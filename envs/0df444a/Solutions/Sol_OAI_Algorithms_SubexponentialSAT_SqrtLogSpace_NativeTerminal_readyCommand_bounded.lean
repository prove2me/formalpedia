-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:22:37.657873+00:00
-- url     : https://prove2.me/submissions/fe56ac0e-26e0-4dfa-827d-b646d425f354

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S111
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeTerminal_power_bounded
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

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSBoundarySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical storage at the depth-first controller boundary.

Only framed formula bodies occur on the pending stack. The mathematical depth
is a proof index and is not serialized. Both children, the current formula,
the declared-variable word, and the two count words are charged simultaneously.
These bounds apply to the actual fixed frontier and accumulator routines after
injective port relocation. The final DFS must still establish its boundary
invariant and bounds for the concrete selector, splitter, and leaf commands.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

open BitProgram StructuredCalls

/-- Actual cleanup never increases any stack, at any prefix. No bound on
elapsed time is needed: its finite table contains only pop, branch and halt. -/
theorem clearProgram_stack_length_le {r s steps : ℕ}
    (src : Fin s) (value present : Fin r) {a b : Cfg r s 3}
    (htrace : Trace (StackRoutines.clearProgram src value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
  have hstep {a b : Cfg r s 3}
      (hs : step (StackRoutines.clearProgram src value present) a = some b) :
      ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
    cases hpc : a.pc with
    | none => simp [step, hpc] at hs
    | some label =>
        simp only [step, hpc, Option.map, Option.some.injEq] at hs
        rw [← hs]
        intro i
        fin_cases label
        · by_cases hi : i = src
          · subst i
            simp [execInstr]
          · simp [execInstr, hi]
        · simp [execInstr]
        · simp [execInstr]
  induction htrace with
  | refl => exact fun _ => le_rfl
  | cons hs ht ih => exact fun i => (ih i).trans (hstep hs i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

namespace BoundedEval
variable {command first second yes no : Code} {t u B : ℕ} {a b c : Data}

theorem final_bound (h : BoundedEval command t a b B) :
    ∀ i, (b.stacks i).length ≤ B :=
  h.space t _ le_rfl (compiled_trace h.eval 256 256)

theorem seq (h : BoundedEval first t a b B) (g : BoundedEval second u b c B) :
    BoundedEval (.seq first second) (t + u) a c B :=
  ⟨h.eval.seq g.eval, StructuredSpace.sequence_stack_bound h.eval g.eval 256 256 h.space g.space
    (compiled (.seq first second) 256 256) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 256 256)⟩

theorem ite_true {flag : Fin 80} (hf : a.regs flag = true)
    (h : BoundedEval yes t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_true hf h.eval, StructuredSpace.conditional_true_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

theorem ite_false {flag : Fin 80} (hf : a.regs flag = false)
    (h : BoundedEval no t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_false hf h.eval, StructuredSpace.conditional_false_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeaf
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual adapters for the streamed counting leaf. Both initial code rows
and newly generated rows use the canonical modulus word's exact width. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

/-- Clearing a port never enlarges any retained word, including before return. -/
theorem clearOutput_space (port : Fin 1220) {steps bound : ℕ}
    {a b : State 80 1220} (he : Eval (clearOutput port) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearOutput port) 256 256) prefixSteps
        (a.withPC (some (compiled (clearOutput port) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram port 72 73)
        (compiled (clearOutput port) 256 256) (siteAddress (clearOutput port))
        (exitAddress (clearOutput port)) (compiled_site (clearOutput port) 256 256) ht
      intro prefixSteps c _ hc i
      exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
        port 72 73 hc i).trans (ha i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEmptyClauseProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A preserving empty-clause test on the actual encoded leaf

The fixed program searches for the one-bit encoding of an empty clause.
The leaf on stack 9 and every other caller word are preserved.  Only the
five empty membership work ports and one empty copy port are used.
-/

namespace SubexponentialSAT.SubexpEmptyClauseProgram

open BitProgram StructuredCalls

theorem copyLeaf_eval (d : Data) (h : Ready d) :
    Eval copyLeaf (7 * (d.stacks 9).length + 5) d (copied d) := by
  have ht := ListRegisterProgram.copy_run (9 : Fin 10) 0 8 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h.2
  apply Eval.call
  simpa [copied, ListRegisterProgram.Run, StackRoutines.copyStacks, h.1 0 (by decide)] using ht

theorem loadQuery_eval (d : Data) : Eval loadQuery 2 d (queryLoaded d) := by
  exact .seq (.base (.atom _ _)) (.base (.atom _ _))

theorem clear_eval (i : Fin 10) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 d.regs d.stacks)

theorem resetWork_eval (d : Data) : Eval resetWork 7 d (resetResult d) := by
  let d0 := (StructuredProgram.Atom.copy 0 4).eval d
  let d1 := (StructuredProgram.Atom.set 1 false).eval d0
  let d2 := (StructuredProgram.Atom.set 2 false).eval d1
  let d3 := (StructuredProgram.Atom.set 3 false).eval d2
  let d4 := (StructuredProgram.Atom.set 4 false).eval d3
  let d5 := (StructuredProgram.Atom.set 5 false).eval d4
  let d6 := (StructuredProgram.Atom.set 6 false).eval d5
  have he : Eval resetWork 7 d d6 :=
    .seq (.base (.atom _ _)) (.seq (.base (.atom _ _))
      (.seq (.base (.atom _ _)) (.seq (.base (.atom _ _))
        (.seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))))))
  have hd : d6 = resetResult d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · rfl
  exact hd ▸ he

/-- A real membership search, including the preserving copy and all cleanup.
No clause-order, width, or nonempty-clause premise is needed. -/
theorem command_eval (records : List (List Bool)) (d : Data)
    (hbody : d.stacks 9 = Encoding.encodeList id records) (hr : Ready d) :
    ∃ t, t ≤ 100 * ((d.stacks 9).length + 1) ∧
      Eval command t d (result d (decide ([false] ∈ records))) := by
  let start := queryLoaded (copied d)
  have h0 : start.stacks 0 = Encoding.encodeList id records := by
    simp [start, queryLoaded, copied, hbody]
  have h1 : start.stacks 1 = [] := by
    simpa [start, queryLoaded, copied] using hr.1 1 (by decide)
  have h2 : start.stacks 2 = ([false] : List Bool).reverse := by
    simp [start, queryLoaded, copied, hr.1 2 (by decide)]
  have h3 : start.stacks 3 = [] := by
    simpa [start, queryLoaded, copied] using hr.1 3 (by decide)
  have h4 : start.stacks 4 = [] := by
    simpa [start, queryLoaded, copied] using hr.1 4 (by decide)
  obtain ⟨t, e, he, ht, hf, hlen, hout, hquery, hcopy, htmp, hframe, hregs⟩ :=
    SubexpScopeMembershipProgram.member_eval [false] records start h0 h1 h2 h3 h4
  let e0 := cleared 0 e
  let e1 := cleared 1 e0
  let e2 := cleared 2 e1
  have hl1 : e0.stacks 1 = [decide ([false] ∈ records)] := by
    simpa [e0, cleared] using hout
  have hl2 : e1.stacks 2 = [false] := by
    simpa [e1, e0, cleared, h2] using hquery
  have hc1 : Eval (clear 1) 5 e0 e1 := by
    simpa only [hl1, List.length_cons, List.length_nil] using clear_eval 1 e0
  have hc2 : Eval (clear 2) 5 e1 e2 := by
    simpa only [hl2, List.length_cons, List.length_nil] using clear_eval 2 e1
  have hstacks : e2.stacks = d.stacks := by
    funext i
    fin_cases i
    · simp [e2, e1, e0, cleared, hr.1 0 (by decide)]
    · simp [e2, e1, e0, cleared, hr.1 1 (by decide)]
    · simp [e2, e1, e0, cleared, hr.1 2 (by decide)]
    · simp [e2, e1, e0, cleared, hcopy, hr.1 3 (by decide)]
    · simp [e2, e1, e0, cleared, htmp, hr.1 4 (by decide)]
    · simp [e2, e1, e0, cleared, hframe 5 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 6 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 7 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 8 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 9 (by decide), start, queryLoaded, copied]
  have hend : resetResult e2 = result d (decide ([false] ∈ records)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hi0 : i = 0
      · subst i
        simpa [resetResult, result, e2, e1, e0, cleared, readRegs] using hf
      by_cases hi7 : i.val < 7
      · simp [ hi0, hi7]
      · have hi : 7 ≤ i.val := by omega
        have hi1 : i ≠ 1 := by intro hh; subst i; simp at hi
        have hi2 : i ≠ 0 := hi0
        simpa [resetResult, result, hi0, hi7, e2, e1, e0, cleared, readRegs,
          start, queryLoaded, copied, hi1, hi2] using hregs i hi
    · exact hstacks
  have hex := (copyLeaf_eval d hr).seq ((loadQuery_eval (copied d)).seq
    (he.seq ((clear_eval 0 e).seq (hc1.seq (hc2.seq (resetWork_eval e2))))))
  rw [hend] at hex
  refine ⟨(7 * (d.stacks 9).length + 5) + (2 + (t +
    ((2 * (e.stacks 0).length + 3) + (5 + (5 + 7))))), ?_, hex⟩
  simp only [List.length_cons, List.length_nil] at ht
  rw [← hbody] at ht hlen
  omega

theorem program_runsIn (records : List (List Bool)) (d : Data)
    (hbody : d.stacks 9 = Encoding.encodeList id records) (hr : Ready d) :
    RunsIn program (100 * ((d.stacks 9).length + 1) + 1)
      (d.withPC (some program.entry))
      ((result d (decide ([false] ∈ records))).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval records d hbody hr
  exact ⟨t + 1, by omega, compiled_halt_trace he 9 9⟩

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramTrivial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual classification of the two trivial leaf cases. The empty formula
and an empty clause are detected separately on the preserved encoded leaf. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Trivial

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (a : Data) (records : List (List Bool))
    (hbody : a.stacks 9 = Encoding.encodeList id records) (hready : SubexpEmptyClauseProgram.Ready a) :
    ∃ cost ≤ 100*((a.stacks 9).length+1)+2,
      Eval command cost a (result a records) := by
  obtain ⟨k,hk,he⟩ := SubexpEmptyClauseProgram.program_runsIn records a hbody hready
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.peek (9 : Fin 10) (7 : Fin 10) 8)
    (SubexpEmptyClauseProgram.result a (decide ([false] ∈ records))))
  have hresult : (StructuredProgram.Atom.peek (9 : Fin 10) (7 : Fin 10) 8).eval
      (SubexpEmptyClauseProgram.result a (decide ([false] ∈ records))) = result a records := by
    simp only [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,
      SubexpEmptyClauseProgram.result,result,hbody]
  rw [hresult] at hp
  exact ⟨k+1,by omega,(Eval.call _ he).seq hp⟩

theorem result_nonempty (a : Data) (records : List (List Bool)) :
    (result a records).regs 7 = decide (records ≠ []) := by
  cases records <;> simp [result,readRegs,Encoding.encodeList]

theorem result_empty_clause (a : Data) (records : List (List Bool)) :
    (result a records).regs 0 = decide ([false] ∈ records) := by
  simp [result,readRegs,SubexpEmptyClauseProgram.result]

theorem program_run (a : Data) (records : List (List Bool))
    (hbody : a.stacks 9 = Encoding.encodeList id records) (hready : SubexpEmptyClauseProgram.Ready a) :
    RunsIn program (100*((a.stacks 9).length+1)+3)
      (a.withPC (some program.entry)) ((result a records).withPC none) := by
  obtain ⟨k,hk,he⟩ := command_eval a records hbody hready
  exact ⟨k+1,by omega,compiled_halt_trace he 9 9⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Trivial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

theorem classifierStacks_low (i : Fin 10) (hi : i.val < 9) :
    classifierStacks i = Fin.castAdd 1210 i := by
  change Equiv.swap (9 : Fin 1220) 265 (Fin.castAdd 1210 i) = _
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hv : i.val = 9 := congrArg Fin.val h
    omega
  · intro h
    have hv : i.val = 265 := congrArg Fin.val h
    omega

theorem classifier_eval (a : Data) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records) (hready : Ready a) :
    ∃ steps, steps ≤ 100 * ((a.stacks 265).length + 1) + 3 ∧
      Eval classifier steps a (classified a records) := by
  have hb : (projectState (Fin.castAdd 70) classifierStacks a).stacks 9 =
      Encoding.encodeList id records := by simpa [projectState] using hbody
  have hr : SubexpEmptyClauseProgram.Ready
      (projectState (Fin.castAdd 70) classifierStacks a) := by
    constructor
    · intro i hi
      simpa [projectState, classifierStacks_low i (by omega)] using
        hready.1 (Fin.castAdd 1210 i) hi
    · simpa [projectState, classifierStacks_low 8 (by decide)] using hready.2
  obtain ⟨steps, hs, ht⟩ := SqrtLog.LeafProgram.Trivial.program_run _ records hb hr
  refine ⟨steps, ?_, eval_call_from_state _ _ _ a
    (Fin.castAdd_injective 10 70) classifierStacks.injective ht⟩
  simpa [projectState] using hs

theorem classified_stacks (a : Data) (records : List (List Bool)) :
    (classified a records).stacks = a.stacks := by
  funext i
  by_cases hi : ∃ j, classifierStacks j = i
  · obtain ⟨j, rfl⟩ := hi
    exact embedState_stack _ _ _ _ classifierStacks.injective j
  · exact embedState_stack_frame _ _ _ _ i hi

theorem classified_empty_clause (a : Data) (records : List (List Bool)) :
    (classified a records).regs 0 = decide ([false] ∈ records) := by
  exact (embedState_register _ _ _ _ (Fin.castAdd_injective 10 70) 0).trans
    (SqrtLog.LeafProgram.Trivial.result_empty_clause _ _)

theorem classified_nonempty (a : Data) (records : List (List Bool)) :
    (classified a records).regs 7 = decide (records ≠ []) := by
  exact (embedState_register _ _ _ _ (Fin.castAdd_injective 10 70) 7).trans
    (SqrtLog.LeafProgram.Trivial.result_nonempty _ _)

theorem prepared_frame (a : Data) (i : Fin 1220)
    (ho : i ≠ 263) (hw : i ≠ 268) (hs : i ≠ 269) :
    (prepared a).stacks i = a.stacks i := by
  simp [prepared, Native.clearOutputState, ho, hw, hs]

/-- Only the classifier's local body word contributes to its temporary bound.
The retained DFS frame is bounded by the same unchanged `bound`. -/
theorem classifier_space {steps bound : ℕ} {a b : Data}
    (he : Eval classifier steps a b) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records)
    (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 101 * (a.stacks 265).length + 103 ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled classifier 256 256) prefixSteps
        (a.withPC (some (compiled classifier 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  let localData := projectState (Fin.castAdd 70) classifierStacks a
  have hstacks : localData.stacks = (StructuredProgram.ioState (r := 10) (9 : Fin 10)
      (a.stacks 265)).stacks := by
    funext i
    by_cases hi : i = 9
    · subst i; simp [localData, projectState]
    · have hil : i.val < 9 := by
        have hil := i.isLt
        have hne : i.val ≠ 9 := fun h => hi (Fin.ext h)
        omega
      simp only [localData, projectState, Function.comp_apply, classifierStacks_low i hil,
        hi, ite_false]
      exact hlow (Fin.castAdd 1210 i) hil
  have hr : SubexpEmptyClauseProgram.Ready localData := by
    constructor
    · intro i hi
      rw [hstacks]
      have hne : i ≠ 9 := by intro h; have hv : i.val = 9 := congrArg Fin.val h; omega
      simp [hne]
    · rw [hstacks]; simp
  obtain ⟨t, ht, hrun⟩ := SqrtLog.LeafProgram.Trivial.program_run localData records
    (by simpa [localData, projectState] using hbody) hr
  have hsize : dataBits (localData.withPC
      (some SqrtLog.LeafProgram.Trivial.program.entry)) ≤ (a.stacks 265).length := by
    simp only [dataBits, stackBits, hstacks]
    have hlen : (fun i : Fin 10 => (if i = 9 then a.stacks 265 else []).length) =
        (fun i : Fin 10 => if i = 9 then (a.stacks 265).length else 0) := by
      funext i
      split_ifs <;> rfl
    rw [hlen]
    simp
  have hlocal : ∀ prefixSteps c, prefixSteps ≤ t →
      Trace SqrtLog.LeafProgram.Trivial.program prefixSteps
        (localData.withPC (some SqrtLog.LeafProgram.Trivial.program.entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro prefixSteps c hprefix htrace i
    have hg := StructuredSpace.local_stack_bound SqrtLog.LeafProgram.Trivial.program hsize
      prefixSteps c hprefix htrace i
    have hb : (localData.stacks 9).length = (a.stacks 265).length := by
      simp [localData, projectState]
    rw [hb] at ht
    omega
  have hcall := eval_call_from_state SqrtLog.LeafProgram.Trivial.program
    (Fin.castAdd 70) classifierStacks a (Fin.castAdd_injective 10 70)
    classifierStacks.injective hrun
  have hsteps : steps = t := StreamResources.eval_steps_eq 256 256 he hcall
  subst steps
  have hinit : ProgramLinking.embedCfg (Fin.castAdd 70) classifierStacks id none
      (a.withPC none) (localData.withPC (some SqrtLog.LeafProgram.Trivial.program.entry)) =
      a.withPC (some (ProgramLinking.liftProgram SqrtLog.LeafProgram.Trivial.program
        (Fin.castAdd 70) classifierStacks).entry) := by
    change (embedState (Fin.castAdd 70) classifierStacks a localData).withPC _ = _
    rw [show embedState (Fin.castAdd 70) classifierStacks a localData = a from
      embedState_project _ _ a (Fin.castAdd_injective 10 70) classifierStacks.injective]
    rfl
  have hglobal := StructuredSpace.liftProgram_stack_bound
    SqrtLog.LeafProgram.Trivial.program (Fin.castAdd 70) classifierStacks (a.withPC none)
    (Fin.castAdd_injective 10 70) classifierStacks.injective hrun hlocal hframe
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call p ht =>
      exact StructuredSpace.call_stack_bound _ (compiled classifier 256 256)
        (siteAddress classifier) (exitAddress classifier) (compiled_site classifier 256 256)
        ht hglobal


open DisjointReuse.DFSVisit

private theorem atom_bounded (op : StructuredProgram.Atom 80 1220) (a : Data) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound)
    (hb : ∀ i, ((op.eval a).stacks i).length ≤ bound) :
    BoundedEval (.base (.atom op)) 1 a (op.eval a) bound := by
  refine ⟨.base (.atom op a), ?_⟩
  intro prefixSteps c hp hc
  have hcases : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
  rcases hcases with rfl | rfl
  · cases hc
    exact ha
  · rw [trace_same_length_unique hc (compiled_trace (Eval.base (.atom op a)) 256 256)]
    exact hb

private theorem skip_bounded (a : Data) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    BoundedEval (.base .skip) 0 a a bound := by
  refine ⟨.base (.skip a), ?_⟩
  intro prefixSteps c hp hc
  have hz : prefixSteps = 0 := by omega
  subst prefixSteps
  cases hc
  exact ha

theorem zero_bounded (a : Data) (bound : ℕ) (houtput : a.stacks 263 = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound) (hbudget : 1 ≤ bound) :
    BoundedEval zero 2 a (zeroed a) bound := by
  have first := atom_bounded (.set 72 false) a bound hframe hframe
  have second := atom_bounded (.push 263 72) ((StructuredProgram.Atom.set 72 false).eval a)
    bound first.final_bound (by
      intro i
      by_cases hi : i = 263
      · subst i
        simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
          houtput] using hbudget
      · simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hi]
          using hframe i)
  exact first.seq second

/-- Dispatcher scratch cleanup is non-growing, including arbitrary old words. -/
theorem prepare_bounded (a : Data) (bound : ℕ)
    (hframe : ∀ i, (a.stacks i).length ≤ bound) :
    BoundedEval prepare
      (2 * (a.stacks 263).length + 2 * (a.stacks 268).length +
        2 * (a.stacks 269).length + 9) a (prepared a) bound := by
  have h1e := Native.clearOutput_eval 263 a
  have h1 : BoundedEval (Native.clearOutput 263) _ a _ bound :=
    ⟨h1e, Native.clearOutput_space 263 h1e hframe⟩
  have h2e := Native.clearOutput_eval 268 (Native.clearOutputState 263 a)
  have h2 : BoundedEval (Native.clearOutput 268) _ _ _ bound :=
    ⟨h2e, Native.clearOutput_space 268 h2e h1.final_bound⟩
  have h3e := Native.clearOutput_eval 269
    (Native.clearOutputState 268 (Native.clearOutputState 263 a))
  have h3 : BoundedEval (Native.clearOutput 269) _ _ _ bound :=
    ⟨h3e, Native.clearOutput_space 269 h3e h2.final_bound⟩
  have whole := h1.seq (h2.seq h3)
  convert whole using 1
  · rfl
  · simp [Native.clearOutputState]
    omega
  · rfl

/-- Every terminal branch retains one fixed bound across arbitrary DFS frames. -/
theorem command_bounded (a : Data) (n bound : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records)
    (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound) :
    ∃ steps, steps ≤ 100 * ((a.stacks 265).length + 1) + 11 * n + 22 ∧
      BoundedEval command steps a (result a n records) bound := by
  have hr : Ready a := ⟨fun i hi => hlow i (by omega), hlow 8 (by decide)⟩
  obtain ⟨steps, hs, hc⟩ := classifier_eval a records hbody hr
  have first : BoundedEval classifier steps a (classified a records) bound :=
    ⟨hc, classifier_space hc records hbody hlow hframe hclassifier⟩
  have hzero := classified_empty_clause a records
  have hnonempty := classified_nonempty a records
  by_cases hz : [false] ∈ records
  · refine ⟨steps + 3, by omega, ?_⟩
    rw [result, ite_eq_left hz]
    exact first.seq ((zero_bounded (classified a records) bound
      (by simpa [classified_stacks] using houtput) first.final_bound (by omega)).ite_true
        (by simpa [hz] using hzero))
  · by_cases hempty : records = []
    · have hp := power_bounded (classified a records) n bound
        (by simpa [classified_stacks] using hn)
        (by simpa [classified_stacks] using houtput)
        (by simpa [classified_stacks] using hwork)
        (by simpa [classified_stacks] using hscratch) first.final_bound hpower
      refine ⟨steps + (11 * n + 17 + 1 + 1), by omega, ?_⟩
      rw [result, ite_eq_right hz, ite_eq_left hempty]
      exact first.seq ((hp.ite_false (by simpa [hempty] using hnonempty)).ite_false
        (by simpa [hz] using hzero))
    · refine ⟨steps + 2, by omega, ?_⟩
      rw [result, ite_eq_right hz, ite_eq_right hempty]
      exact first.seq (((skip_bounded (classified a records) bound first.final_bound).ite_true
        (by simpa [hempty] using hnonempty)).ite_false (by simpa [hz] using hzero))

/-- The complete ready terminal command preserves the same DFS stack bound.
The two local budgets depend only on the body and ambient dimension. -/
theorem readyCommand_bounded_oai (a : Data) (n bound : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records)
    (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound) :
    ∃ steps, steps ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + 31 ∧
      BoundedEval readyCommand steps a (readyResult a n records) bound := by
  have first := prepare_bounded a bound hframe
  have hb := prepared_frame a 265 (by decide) (by decide) (by decide)
  have hh := prepared_frame a 258 (by decide) (by decide) (by decide)
  have hl : ∀ i : Fin 1220, i.val < 9 → (prepared a).stacks i = [] := by
    intro i hi
    rw [prepared_frame a i]
    · exact hlow i hi
    · intro h; have hv : i.val = 263 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 268 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 269 := congrArg Fin.val h; omega
  obtain ⟨steps, hs, second⟩ := command_bounded (prepared a) n bound records
    (hb.trans hbody) hl (hh.trans hn) (prepared_output a) (prepared_work a)
    (prepared_scratch a) first.final_bound (by simpa [hb] using hclassifier) hpower
  rw [hb] at hs
  have h263 := hframe 263
  have h268 := hframe 268
  have h269 := hframe 269
  exact ⟨_, by omega, first.seq second⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded_oai
