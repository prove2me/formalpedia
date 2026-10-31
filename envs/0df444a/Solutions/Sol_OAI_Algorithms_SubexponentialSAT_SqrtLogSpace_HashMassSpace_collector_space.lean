-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:43:22.003957+00:00
-- url     : https://prove2.me/submissions/6a5e2f5c-bb8e-48a8-aad2-9d60005a0be6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
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

/-- A loop induction combines its current body and remaining iterations by
maximum space; the number of completed iterations never multiplies the bound. -/
theorem while_true_stack_bound {r s L : ℕ} {body : StructuredCalls.Cmd r s}
    {test : Fin r} {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (htest : a.regs test = true)
    (hb : StructuredCalls.Eval body n a b)
    (hw : StructuredCalls.Eval (.while test body) m b c)
    (inputStack outputStack : Fin s)
    (hbody : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hwhile : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := n + m)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry body (embed ∘ some) (embed none)))) ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hbody 0 _ (Nat.zero_le n) (.refl _)
  · exact trace_prefix_bound_trans
      (StructuredCalls.eval_trace hb caller (embed ∘ some) (embed none)
        (fun q => hcode (some q)))
      (command_stack_bound hb inputStack outputStack hbody caller (embed ∘ some)
        (embed none) (fun q => hcode (some q)))
      (command_stack_bound hw inputStack outputStack hwhile caller embed exit hcode)

theorem while_false_stack_bound {r s L : ℕ} (body : StructuredCalls.Cmd r s)
    (test : Fin r) {bound : ℕ} (a : StructuredCalls.State r s)
    (htest : a.regs test = false) (hstart : ∀ i, (a.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := 0)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some exit)) ?_ hstart ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · intro prefixSteps intermediate hle hp
    have hz : prefixSteps = 0 := by omega
    subst prefixSteps
    cases hp
    exact hstart

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

namespace NativeRound

theorem StageSpace.seq {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : StageSpace first n a bound) (hsecond : StageSpace second m b bound) :
    StageSpace (.seq first second) (n + m) a bound := by
  exact ⟨StructuredSpace.sequence_stack_bound hf hs 778 777 hfirst.bound hsecond.bound
    _ _ _ (compiled_site _ 778 777)⟩

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- This adds two binary words with an actual execution of the fixed adder. -/
theorem command_eval (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 1, ∃ regs',
      Eval command n (data regs acc next) (data regs' (BinaryArithmetic.add acc next) []) := by
  let reset := Function.update regs 0 false
  obtain ⟨regs', n, hn, ht⟩ := BinaryPrograms.Add.littleEndian_run reset acc next
  have hs : (StructuredProgram.Atom.set 0 false).eval (data regs acc next) =
      data reset acc next := by
    rfl
  refine ⟨1 + n, by omega, regs', ?_⟩
  apply Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 0 false) _))
  rw [hs]
  apply Eval.call
  have hentry : BinaryPrograms.Add.littleEndianProgram.entry = 0 := rfl
  simpa [data, reset, BinaryArithmetic.add, StructuredProgram.State.withPC, hentry] using ht

theorem program_trace (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 2, ∃ regs',
      Trace program n ((data regs acc next).withPC (some program.entry))
        ((data regs' (BinaryArithmetic.add acc next) []).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := command_eval regs acc next
  exact ⟨n + 1, by omega, regs', compiled_halt_trace ht 1 0⟩

variable {r s : ℕ}

theorem invoke_eval (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 3, ∃ regs',
      Eval (invoke p) n (state p frame regs acc next)
        (state p frame regs' (BinaryArithmetic.add acc next) []) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs acc next
  exact ⟨n, by omega, regs', eval_call_lifted program p.register p.stack frame
    p.register_injective p.stack_injective ht⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

private theorem workPort_ne (i : Fin 891) (j : Fin 896) (hj : 320 ≤ j.val ∧ j.val ≤ 324) :
    workPort i ≠ j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [workPort] at hv
  split_ifs at hv <;> simp only at hv <;> omega

@[simp] theorem workspace_recordState (a : Data) (v pr f : Bool) (src payload : List Bool) :
    workspace (RecordPrograms.state recordPorts a v pr f src payload) = workspace a := by
  funext i
  have hs := workPort_ne i 320 (by decide)
  have hp := workPort_ne i 321 (by decide)
  simp [workspace, RecordPrograms.state, recordPorts, hs, hp]

private theorem mass_state_eq_self (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (hr : ∀ i, regs i = a.regs (massPorts.register i))
    (hs : ∀ i, (Mass.data regs acc next).stacks i = a.stacks (massPorts.stack i)) :
    Mass.state massPorts a regs acc next = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, massPorts.register j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_register massPorts.register massPorts.stack a (Mass.data regs acc next) massPorts.register_injective j).trans (hr j)
    · exact embedState_register_frame massPorts.register massPorts.stack a (Mass.data regs acc next) i h
  · funext i
    by_cases h : ∃ j, massPorts.stack j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_stack massPorts.register massPorts.stack a (Mass.data regs acc next) massPorts.stack_injective j).trans (hs j)
    · exact embedState_stack_frame massPorts.register massPorts.stack a (Mass.data regs acc next) i h

private theorem mass_stack_local (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 3) :
    (Mass.state massPorts a regs acc next).stacks (massPorts.stack i) =
      (Mass.data regs acc next).stacks i :=
  embedState_stack _ _ _ _ massPorts.stack_injective i

private theorem mass_stack_frame (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 896) (hi : i.val < 322 ∨ 324 < i.val) :
    (Mass.state massPorts a regs acc next).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  fin_cases j <;> simp [massPorts] at hh <;> omega

private theorem mass_reg_frame (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (Mass.state massPorts a regs acc next).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  simp [massPorts] at hh
  omega

@[simp] theorem workspace_mass_state (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool) :
    workspace (Mass.state massPorts a regs acc next) = workspace a := by
  funext i
  apply mass_stack_frame
  dsimp [workPort]
  split_ifs <;> simp <;> omega

/-- Consume one physically computed count word, without requiring a canonical
representation of that integer. -/
theorem add_count_eval (ready : (Fin 891 → List Bool) → Prop)
    (middle : Data) (tail acc word : List Bool)
    (hm : ready (workspace middle)) (hr : read middle = acc)
    (hc : middle.stacks 323 = word) (hs : middle.stacks 324 = []) :
    ∃ n next, n ≤ 16*(max acc.length word.length+1)+3 ∧
      Ready ready next ∧ read next = BinaryArithmetic.add acc word ∧
      Eval (Mass.invoke massPorts) n
        (RecordPrograms.state recordPorts middle false true false tail [])
        (RecordPrograms.state recordPorts next false true false tail []) := by
  let a := RecordPrograms.state recordPorts middle false true false tail []
  let regs := fun i => a.regs (massPorts.register i)
  have ha : Mass.state massPorts a regs acc word = a := by
    apply mass_state_eq_self _ _ _ _ (fun _ => rfl)
    intro i
    fin_cases i <;>
      simp [Mass.data, BinaryPrograms.Add.stackState, massPorts, a,
        RecordPrograms.state, recordPorts, read] at hr ⊢
    · exact hr.symm
    · exact hc.symm
    · exact hs
  obtain ⟨n, hn, regs', he⟩ := Mass.invoke_eval massPorts a regs acc word
  let b := Mass.state massPorts a regs' (BinaryArithmetic.add acc word) []
  have hb322 : b.stacks 322 = BinaryArithmetic.add acc word := mass_stack_local a regs' _ [] 0
  have hb323 : b.stacks 323 = [] := mass_stack_local a regs' _ [] 1
  have hb324 : b.stacks 324 = [] := mass_stack_local a regs' _ [] 2
  have hb320 : b.stacks 320 = tail := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb321 : b.stacks 321 = [] := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb16 : b.regs 16 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb17 : b.regs 17 = true := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb18 : b.regs 18 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hstate : RecordPrograms.state recordPorts b false true false tail [] = b :=
    RecordPrograms.state_eq_self recordPorts b _ _ _ _ _ hb16 hb17 hb18 hb320 hb321
  refine ⟨n,b,hn,⟨?_,hb323,hb324⟩,hb322,?_⟩
  · simpa [b,a] using hm
  · rw [hstate]
    simpa only [ha,b] using he


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! All-prefix storage for the actual marked-record collector. The parser and
native addition have polynomial local work. Expensive marked queries supply
their own actual prefix bound; their total runtime is never used as workspace. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashMassAdapter HashGreedyProgram.NativeRound

private theorem workPort_covers (i : Fin 896) (hi : i.val < 320 ∨ 324 < i.val) :
    ∃ j : Fin 891, workPort j = i := by
  rcases hi with hi | hi
  · refine ⟨⟨i.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [workPort, hi]
  · refine ⟨⟨i.val - 5, by omega⟩, ?_⟩
    apply Fin.ext
    have h : ¬i.val - 5 < 320 := by omega
    simp [workPort, h]
    omega

/-- All 896 words are charged, including the caller workspace and the unread
record tail. This also applies immediately after a query before its addition. -/
theorem state_stack_bound (ready : (Fin 891 → List Bool) → Prop) (L : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (base : HashMassAdapter.Data) (v pr f : Bool) (src payload : List Bool)
    (hb : ready (workspace base)) (hacc : (read base).length ≤ L)
    (hresult : (base.stacks 323).length ≤ L) (hscratch : (base.stacks 324).length ≤ L)
    (hsource : src.length ≤ L) (hpayload : payload.length ≤ L) :
    ∀ i, ((state recordPorts base v pr f src payload).stacks i).length ≤ L := by
  intro i
  by_cases h320 : i = 320
  · subst i
    simpa [state, recordPorts] using hsource
  by_cases h321 : i = 321
  · subst i
    simpa [state, recordPorts] using hpayload
  by_cases h322 : i = 322
  · subst i
    simpa [state, recordPorts, HashMassAdapter.read] using hacc
  by_cases h323 : i = 323
  · subst i
    simpa [state, recordPorts] using hresult
  by_cases h324 : i = 324
  · subst i
    simpa [state, recordPorts] using hscratch
  have hi : i.val < 320 ∨ 324 < i.val := by
    have : i.val ≠ 320 := fun h => h320 (Fin.ext h)
    have : i.val ≠ 321 := fun h => h321 (Fin.ext h)
    have : i.val ≠ 322 := fun h => h322 (Fin.ext h)
    have : i.val ≠ 323 := fun h => h323 (Fin.ext h)
    have : i.val ≠ 324 := fun h => h324 (Fin.ext h)
    omega
  obtain ⟨j, hj⟩ := workPort_covers i hi
  have h := hready (workspace base) hb j
  simpa [state, recordPorts, h320, h321, workspace, hj] using h

private theorem ready_state_bound (ready : (Fin 891 → List Bool) → Prop) (L : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (base : HashMassAdapter.Data) (v pr f : Bool) (src payload : List Bool)
    (hb : Ready ready base) (hacc : (read base).length ≤ L)
    (hsource : src.length ≤ L) (hpayload : payload.length ≤ L) :
    ∀ i, ((state recordPorts base v pr f src payload).stacks i).length ≤ L :=
  state_stack_bound ready L hready base v pr f src payload hb.workspace_ready hacc
    (by simp [hb.result_empty]) (by simp [hb.scratch_empty]) hsource hpayload

private theorem afterTag_bound (ready : (Fin 891 → List Bool) → Prop) (L : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (base : HashMassAdapter.Data) (records : List (List Bool)) (suffix : List Bool)
    (hb : Ready ready base) (hacc : (read base).length ≤ L)
    (hsource : (Encoding.encodeList id records ++ suffix).length ≤ L) :
    ∀ i, ((afterTag recordPorts base records suffix).stacks i).length ≤ L := by
  cases records with
  | nil =>
    apply ready_state_bound ready L hready base false true false suffix [] hb hacc
    · have h : 1 + suffix.length ≤ L := by simpa using hsource
      omega
    · simp
  | cons bits rest =>
    apply ready_state_bound ready L hready base true true false _ [] hb hacc
    · simp only [Encoding.encodeList, List.length_cons, List.length_append, id_eq] at hsource ⊢
      omega
    · simp

private theorem local_space {command : Code} {n budget L K : ℕ}
    {a : HashMassAdapter.Data} (hn : n ≤ budget) (hbudget : budget ≤ 20 * (L + 1) + 10)
    (hL : ∀ i, (a.stacks i).length ≤ L) :
    StageSpace command n a (max K (896 * L + 20 * (L + 1) + 10)) := by
  constructor
  intro k c hk ht i
  have h := StructuredSpace.local_stack_bound (compiled command 778 777)
    (StreamResources.dataBits_le_mul _ hL) k c (hk.trans hn) ht i
  have hm := Nat.le_max_right K (896 * L + 20 * (L + 1) + 10)
  omega

/-- Actual record-loop executions have a common prefix cap. The accumulator
allowance is its initial word length plus the sum of per-record width growth. -/
theorem loop_space (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 891 → List Bool) → Prop) (valid : List Bool → Prop) (L K : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits → Ready ready base →
      ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits → Ready ready base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    (records : List (List Bool)) (suffix : List Bool) (base : HashMassAdapter.Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : Ready ready base)
    (hacc : (read base).length + outputGrowth width records ≤ L)
    (hsource : (Encoding.encodeList id records ++ suffix).length ≤ L) :
    ∃ n next, Ready ready next ∧
      (read next).length ≤ (read base).length + outputGrowth width records ∧
      Eval (RecordPrograms.loop recordPorts (callback query)) n
        (afterTag recordPorts base records suffix) (state recordPorts next false true false suffix []) ∧
      StageSpace (RecordPrograms.loop recordPorts (callback query)) n
        (afterTag recordPorts base records suffix) (max K (896 * L + 20 * (L + 1) + 10)) := by
  let bound := max K (896 * L + 20 * (L + 1) + 10)
  have hLb : L ≤ bound := by dsimp [bound]; omega
  induction records generalizing base with
  | nil =>
    have he : Eval (RecordPrograms.loop recordPorts (callback query)) 1
        (afterTag recordPorts base [] suffix) (state recordPorts base false true false suffix []) :=
      Eval.while_false (by simp [afterTag])
    refine ⟨1, base, hb, by simp [outputGrowth], he, ?_⟩
    have hstart := afterTag_bound ready L hready base [] suffix hb (by simpa [outputGrowth] using hacc)
      hsource
    exact ⟨StructuredSpace.while_false_stack_bound _ _ _ (by simp [afterTag])
      (fun i => (hstart i).trans hLb) _ _ _ (compiled_site _ 778 777)⟩
  | cons bits rest ih =>
    let tail := Encoding.encodeList id rest ++ suffix
    have hv := hrecords bits (by simp)
    have hgrowth : (read base).length + (width bits + 1) + outputGrowth width rest ≤ L := by
      simpa [outputGrowth, Nat.add_assoc] using hacc
    have haccL : (read base).length ≤ L := by omega
    have hwidth : width bits ≤ L := by omega
    have hsource' : 2 * bits.length + (Encoding.encodeList id rest).length + 2 + suffix.length ≤ L := by
      simpa [List.length_append, Encoding.length_encodeList_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsource
    have htail : tail.length ≤ L := by simp only [tail, List.length_append]; omega
    have hbits : bits.length ≤ L := by omega
    obtain ⟨n, middle, _, hm, hr, _, hw, hs, hquery⟩ := hq bits tail base hv hb
    obtain ⟨na, next, hna, hnext, hread, hadd⟩ :=
      add_count_eval ready middle tail (read base) (middle.stacks 323) hm hr rfl hs
    have hlength : (read next).length ≤ (read base).length + width bits + 1 := by
      rw [hread]
      have hh := BinaryArithmetic.length_add (read base) (middle.stacks 323)
      omega
    have hnextAcc : (read next).length + outputGrowth width rest ≤ L := by omega
    obtain ⟨nt, final, hfinal, hfinalLength, hrest, hrestSpace⟩ :=
      ih next (fun b h => hrecords b (by simp [h])) hnext hnextAcc htail
    have hquerySpace : StageSpace query n
        (state recordPorts base false true false tail bits.reverse) bound := by
      constructor
      intro k c hk ht i
      exact ((hspace bits tail base n middle hv hb haccL htail hbits hwidth hquery).bound
        k c hk ht i).trans (Nat.le_max_left _ _)
    have hmiddleBound := state_stack_bound ready L hready middle false true false tail [] hm
      (by rw [hr]; exact haccL) (hw.trans hwidth) (by simp [hs]) htail (by simp)
    have haddSpace : StageSpace (Mass.invoke massPorts) na
        (state recordPorts middle false true false tail []) bound :=
      local_space hna (by omega) hmiddleBound
    have hcallback := hquery.seq hadd
    have hcallbackSpace := StageSpace.seq hquery hadd hquerySpace haddSpace
    have hreader : Eval (reader recordPorts) (6 * bits.length + 4)
        (afterTag recordPorts base (bits :: rest) suffix)
        (state recordPorts base false true false tail bits.reverse) := by
      simpa [afterTag, tail] using reader_eval recordPorts base bits tail [] true true false
    have hreaderSpace : StageSpace (reader recordPorts) (6 * bits.length + 4)
        (afterTag recordPorts base (bits :: rest) suffix) bound :=
      local_space le_rfl (by omega)
        (afterTag_bound ready L hready base (bits :: rest) suffix hb haccL hsource)
    have hpop : Eval
        (.ite recordPorts.found (atom (.set recordPorts.tag false))
          (atom (.pop recordPorts.source recordPorts.tag recordPorts.present))) 2
        (state recordPorts next false true false tail []) (afterTag recordPorts next rest suffix) := by
      apply Eval.ite_false (by simp)
      exact pop_list_eval recordPorts next rest suffix false true
    have hpopSpace : StageSpace
        (.ite recordPorts.found (atom (.set recordPorts.tag false))
          (atom (.pop recordPorts.source recordPorts.tag recordPorts.present)))
        2 (state recordPorts next false true false tail []) bound :=
      local_space le_rfl (by omega)
        (ready_state_bound ready L hready next false true false tail [] hnext
          (by omega) htail (by simp))
    have hbody := hreader.seq (hcallback.seq hpop)
    have hbodySpace := StageSpace.seq hreader (hcallback.seq hpop) hreaderSpace
      (StageSpace.seq hcallback hpop hcallbackSpace hpopSpace)
    refine ⟨(6 * bits.length + 4 + (n + na + 2)) + nt + 1, final, hfinal, ?_,
      Eval.while_true (by simp [afterTag]) hbody hrest, ?_⟩
    · simp only [outputGrowth, List.map_cons, List.sum_cons] at hfinalLength ⊢
      omega
    · exact ⟨StructuredSpace.while_true_stack_bound (by simp [afterTag]) hbody hrest 778 777
        hbodySpace.bound hrestSpace.bound _ _ _ (compiled_site _ 778 777)⟩

/-- Initial parser setup and the actual final halt preserve the uniform cap.
This exposes a source stage for composition into the concrete mass attempt. -/
theorem command_space (query : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 891 → List Bool) → Prop) (valid : List Bool → Prop) (L K : ℕ)
    (hready : ∀ frame, ready frame → ∀ i, (frame i).length ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits → Ready ready base →
      ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits → Ready ready base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    (records : List (List Bool)) (suffix : List Bool) (base : HashMassAdapter.Data)
    (hrecords : ∀ bits ∈ records, valid bits) (hb : Ready ready base)
    (hacc : (read base).length + outputGrowth width records ≤ L)
    (hsource : (Encoding.encodeList id records ++ suffix).length ≤ L) (v pr f : Bool) :
    ∃ n next, Ready ready next ∧
      (read next).length ≤ (read base).length + outputGrowth width records ∧
      Eval (HashMassAdapter.command query) n
        (state recordPorts base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state recordPorts next false true false suffix []) ∧
      StageSpace (HashMassAdapter.command query) (n + 1)
        (state recordPorts base v pr f (Encoding.encodeList id records ++ suffix) [])
        (max K (896 * L + 20 * (L + 1) + 10)) := by
  obtain ⟨n, next, hn, hlength, hloop, hloopSpace⟩ :=
    loop_space query count queryCost width ready valid L K hready hq hspace
      records suffix base hrecords hb hacc hsource
  have haccL : (read base).length ≤ L := by omega
  have hset := set_found_eval recordPorts base v pr f false
    (Encoding.encodeList id records ++ suffix) []
  have hpop := pop_list_eval recordPorts base records suffix v pr
  have hsetSpace : StageSpace (atom (.set recordPorts.found false)) 1
      (state recordPorts base v pr f (Encoding.encodeList id records ++ suffix) [])
      (max K (896 * L + 20 * (L + 1) + 10)) :=
    local_space le_rfl (by omega)
      (ready_state_bound ready L hready base v pr f _ [] hb haccL hsource (by simp))
  have hpopSpace : StageSpace
      (atom (.pop recordPorts.source recordPorts.tag recordPorts.present)) 1
      (state recordPorts base v pr false (Encoding.encodeList id records ++ suffix) [])
      (max K (896 * L + 20 * (L + 1) + 10)) :=
    local_space le_rfl (by omega)
      (ready_state_bound ready L hready base v pr false _ [] hb haccL hsource (by simp))
  have he := hset.seq (hpop.seq hloop)
  have hstage := StageSpace.seq hset (hpop.seq hloop) hsetSpace
    (StageSpace.seq hpop hloop hpopSpace hloopSpace)
  exact ⟨1 + (1 + n), next, hn, hlength, he,
    ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hstage.bound⟩⟩

/-- The actual compiled collector call inherits every prefix of its callee,
including the callee halt that is relocated to the caller's return jump. -/
theorem collector_space_oai (query : Code) (count queryCost width : List Bool → ℕ)
    (valid : List Bool → Prop) (a : HashMassAdapter.Data) (records : List (List Bool))
    (L K : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (hsource : a.stacks 320 = Encoding.encodeList id records)
    (h321 : a.stacks 321 = []) (h322 : a.stacks 322 = [])
    (h323 : a.stacks 323 = []) (h324 : a.stacks 324 = [])
    (hrecords : ∀ bits ∈ records, valid bits) (hgrowth : outputGrowth width records ≤ L)
    (hq : ∀ bits tail (base : HashMassAdapter.Data), valid bits →
      Ready (fun words => words = workspace a) base →
      ∃ n middle, n ≤ queryCost bits ∧ workspace middle = workspace a ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) = count bits ∧
        (middle.stacks 323).length ≤ width bits ∧ middle.stacks 324 = [] ∧
        Eval query n (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ bits tail base n middle, valid bits →
      Ready (fun words => words = workspace a) base →
      (read base).length ≤ L → tail.length ≤ L → bits.length ≤ L → width bits ≤ L →
      Eval query n (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query n (state recordPorts base false true false tail bits.reverse) K)
    {steps : ℕ} {b : HashMassAdapter.Data}
    (he : Eval (.call (HashMassAdapter.program query)) steps a b) :
    StageSpace (.call (HashMassAdapter.program query)) steps a
      (max K (896 * L + 20 * (L + 1) + 10)) := by
  have hready : ∀ frame, frame = workspace a → ∀ i, (frame i).length ≤ L := by
    intro frame hf i
    rw [hf]
    exact hL (workPort i)
  obtain ⟨n, next, _, _, ht, hstage⟩ := command_space query count queryCost width
    (fun words => words = workspace a) valid L K hready hq hspace records [] a hrecords
    ⟨rfl, h323, h324⟩ (by simpa [HashMassAdapter.read, h322] using hgrowth)
    (by simpa [← hsource] using hL 320) (a.regs 16) (a.regs 17) (a.regs 18)
  have hstart : state recordPorts a (a.regs 16) (a.regs 17) (a.regs 18)
      (Encoding.encodeList id records ++ []) [] = a := by
    apply state_eq_self recordPorts a _ _ _ _ _ rfl rfl rfl
    · simpa only [recordPorts, List.append_nil] using hsource
    · exact h321
  rw [hstart] at ht hstage
  have htrace := compiled_halt_trace ht 320 322
  have hcall : Eval (.call (HashMassAdapter.program query)) (n + 1) a
      (state recordPorts next false true false [] []) := Eval.call _ htrace
  have hsteps := StreamResources.eval_steps_eq 778 777 he hcall
  rw [hsteps]
  exact ⟨StructuredSpace.call_stack_bound (HashMassAdapter.program query)
    (compiled (.call (HashMassAdapter.program query)) 778 777)
    (siteAddress (.call (HashMassAdapter.program query)))
    (exitAddress (.call (HashMassAdapter.program query)))
    (compiled_site (.call (HashMassAdapter.program query)) 778 777) htrace hstage.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace.collector_space_oai
