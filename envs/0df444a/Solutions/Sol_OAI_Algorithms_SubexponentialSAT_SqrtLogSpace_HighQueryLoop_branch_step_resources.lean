-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:13:28.485866+00:00
-- url     : https://prove2.me/submissions/9832e2da-2ce0-4073-b757-ae74159f76b2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryLoop_add_rank
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryProgram_conditioned_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames_pairs_avoids
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compositional certificates for the tape footprint of compiled finite programs. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l R S L : ℕ}

theorem avoids_transferProgram (H : Fin s → Prop) (src dst : Fin s) (value present : Fin r)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsProgram H (StackRoutines.transferProgram src dst value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandStackTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! All-prefix resource transport for the existing exact-time tape replay.
The imported avoidance certificate excludes reads as well as writes, including
`peek`. Erasing hidden caller data is a proof construction only: the actual
instruction table and its measured number of steps remain unchanged. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

variable {r s l : ℕ}

/-- Hidden caller words are preserved at every prefix of this same replayed
execution, including prefixes within called finite instruction tables. -/
theorem eval_shadow_prefix_frame (H : Fin s → Prop) [DecidablePred H]
    {command : Cmd r s} (hc : AvoidsCmd H command) (input output : Fin s)
    {steps : ℕ} {a b : State r s}
    (he : Eval command steps (rebaseState H (fun _ => []) a) b)
    {prefixSteps : ℕ} {intermediate : Cfg r s (size command + 1)}
    (hle : prefixSteps ≤ steps + 1)
    (hprefix : Trace (compiled command input output) prefixSteps
      (a.withPC (some (compiled command input output).entry)) intermediate)
    (i : Fin s) (hi : H i) : intermediate.stacks i = a.stacks i := by
  have hstart : rebaseCfg H a.stacks
      ((rebaseState H (fun _ => []) a).withPC
        (some (compiled command input output).entry)) =
      a.withPC (some (compiled command input output).entry) := by
    rw [rebaseCfg_withPC, rebaseState_restore]
  rw [← hstart] at hprefix
  obtain ⟨source, _, rfl⟩ := trace_prefix_rebase H
    (avoids_compiled H command hc input output) a.stacks
    (compiled_halt_trace he input output) hle hprefix
  exact rebaseStacks_of_mem H a.stacks source.stacks i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
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

theorem copiedHighCounter_frame (a : Data) (i : Fin 896) (h330 : i≠330) (h792 : i≠792) :
    (copiedHighCounter a).stacks i=a.stacks i := by simp [copiedHighCounter,h330,h792]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Separate the retained caller envelope from each physical local input cap.
The local transient bound is never recycled as the next iteration's input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter

theorem lifted_call_bound {r s l R S : ℕ}
    (p : Program r s l) (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (a : State R S) (d e : State r s) (hproject : projectState reg stk a=d)
    (steps bound : ℕ) (ht : Trace p steps (d.withPC (some p.entry)) (e.withPC none))
    (hlocal : ∀ (q : ℕ) z, q ≤ steps → Trace p q (d.withPC (some p.entry)) z →
      ∀ i, (z.stacks i).length≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) (input output : Fin S) :
    ∀ (q : ℕ) z, q ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output) q
        (a.withPC (some (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have hstart : embedState reg stk a d=a := by rw [←hproject,embedState_project reg stk a hr hs]
  have he := eval_call_lifted p reg stk a hr hs ht
  rw [hstart] at he
  have hglobal := StructuredSpace.liftProgram_stack_bound p reg stk (a.withPC none) hr hs ht hlocal hb
  have hinit : ProgramLinking.embedCfg reg stk id none (a.withPC none) (d.withPC (some p.entry)) =
      a.withPC (some (ProgramLinking.liftProgram p reg stk).entry) := by
    change (embedState reg stk a d).withPC _ = _
    rw [hstart]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call routine ht =>
      exact StructuredSpace.call_stack_bound _ _ _ _ (compiled_site (.call (ProgramLinking.liftProgram p reg stk)) input output) ht hglobal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Footprints of the fixed storage and scan controllers used by the leaf. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s : ℕ}

theorem avoids_resetMany (H : Fin s → Prop) (ps : List (Fin 16)) :
    AvoidsCmd H (SubexpSetupStorage.resetMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨trivial,ih⟩

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem mem_scratchIndices (i : Fin 40) : i ∈ scratchIndices ↔
    i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36 := by
  simp only [scratchIndices, List.mem_filter, List.mem_ofFn, exists_eq,
    decide_eq_true_eq, true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    88 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩ := (mem_scratchIndices j).mp hj
  simp only [ports, h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeFinishReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete no-read/no-write certificates for the emitted-node tail.
These check the actual finite port maps and calls, including every peek;
the pending caller and accumulated count on320/322 are never inspected. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

theorem clearMany_avoids (H : Fin 896 → Prop) (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (NodeReadoutSpace.clearMany ports) := by
  induction ports with
  | nil => exact True.intro
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i 0 1 (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySelectorControlFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual query control commands exclude every read, peek and write in the
retained selector bank768..831. Calls into the original768-stack bank are
covered by their genuine port ranges, independently of their internal code. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

/-- Every actual instruction of a lifted lower-bank program is disjoint from
the persistent selector interval. -/
theorem lowProgram_avoids {r l : ℕ} (p : Program r 768 l)
    (register : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (ProgramLinking.liftProgram p register (Fin.castAdd 128)) := by
  apply avoids_liftProgram_of_range
  intro i hi
  change 768 ≤ i.val ∧ i.val < 832 at hi
  omega

theorem lowCommand_avoids {r : ℕ} (c : Cmd r 768) (input output : Fin 768)
    (register : Fin r → Fin 40) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (liftCommand c input output register (Fin.castAdd 128)) :=
  lowProgram_avoids (compiled c input output) register

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832))
    (hi : ∀ q ∈ inputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (ho : ∀ q ∈ outputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (hs : ∀ i, ¬ (768 ≤ (stack i).val ∧ (stack i).val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (isolated p register stack tmp ports inputs outputs) := by
  refine ⟨?_, avoids_liftProgram_of_range _ p register stack hs, ?_⟩
  · exact ⟨avoids_clearMany _ [tmp] (by simpa using ht),
      avoids_clearMany _ ports hp, avoids_resetMany _ workRegisters,
      avoids_copyMany _ tmp inputs ht hi⟩
  · refine ⟨avoids_clearMany _ (outputs.map Prod.snd) ?_,
      avoids_copyMany _ tmp outputs ht ho, avoids_clearMany _ ports hp,
      avoids_resetMany _ workRegisters⟩
    intro i h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (ho q hq).2

private theorem bankClear_avoids {r : ℕ} (tmp : Fin 896)
    (value present : Fin r) (ports : List (Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram _ tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram _ i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ (by decide)
      (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NativeLayoutLoad.command := by
  constructor
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      change ¬ (768 ≤ j.val ∧ j.val < 832)
      omega
  · exact lowCommand_avoids _ _ _ _

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨lowCommand_avoids _ _ _ _, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, lowCommand_avoids _ _ _ _⟩
  intro i hi
  simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeReadoutSpace.command := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      decide
    · have hs := NodeReadoutSpace.scratchPorts_low hi
      omega
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

/-- The exact paid scalar-cache copies are also used by the tuple-sum visitor. -/
theorem nodeAppendPrepare_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.command :=
  ⟨nodeAppendPrepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.finishNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ (768 ≤ (307 : Fin 896).val ∧ (307 : Fin 896).val < 832)
    decide
  · change ¬ (768 ≤ (301 : Fin 896).val ∧ (301 : Fin 896).val < 832)
    decide

theorem nodeFinish_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.command := ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

theorem reconstruction_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryReconstruction.command := ⟨handoff_avoids, lowCommand_avoids _ _ _ _⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The conditioned query also excludes the entire retained selector bank.
This accounts for arbitrary incumbent and remaining-round words in the
actual greedy callback's time quantifiers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 768 ≤ Fin.val i ∧ Fin.val i ≤ 831)

open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem lower_avoids {r l : ℕ} (p : Program r 768 l) (reg : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831)
      (ProgramLinking.liftProgram p reg SignatureHeadLoader.lowStacks) := by
  apply avoids_liftProgram_of_range
  intro i hi
  have hv := i.isLt
  change 768 ≤ i.val ∧ i.val ≤ 831 at hi
  omega


private theorem interval_convert {c : Cmd 40 896}
    (h : AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832) c) :
    AvoidsCmd H c := by simpa only [Nat.lt_succ_iff] using h


theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode :=
  lower_avoids SignatureHeadLoader.bootstrapProgram SignatureHeadLoader.leafRegs

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨interval_convert QuerySelectorControlFrames.beginNode_avoids,
    interval_convert QuerySelectorControlFrames.nativeLayoutLoad_avoids, bootstrap_avoids,
    interval_convert QuerySelectorControlFrames.setupCaller_avoids, pairs_avoids,
    interval_convert QuerySelectorControlFrames.nodeFinish_avoids⟩

theorem nodes_avoids : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨interval_convert QuerySelectorControlFrames.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

/-- The actual fixed conditioned query excludes the whole retained selector
bank, including every invoked table and every peek. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨interval_convert QuerySelectorControlFrames.prepareHigh_avoids, nodes_avoids,
    interval_convert QuerySelectorControlFrames.reconstruction_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete high-loop interfaces: the original ternary source count, exact
physical rank order, the fixed stream's durable frame, and its actual native
accumulator. The full loop still requires the actual stream semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

/-- Each fixed-high query counts free assignments without pruning original
clause violations; its optional marked violation is part of the source test. -/
theorem residual_count_le {n : ℕ} (H : Finset (Fin n)) (high : H → Bool)
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) :
    NodeSemantics.ternaryFixedHighCount H high hashes marked clause ≤ 2 ^ n := by
  classical
  calc
    _ ≤ ∑ _x : ResidualEmbedding.Free H → Bool, 1 :=
      Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = 2 ^ (n-H.card) := by simp [ResidualEmbedding.Free]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

/-- The rank function is the original source function in descending high-ID
order. Out-of-range proof indices contribute zero. -/
theorem rank_value_le {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) :
    rankValue H hashes marked clause rank ≤ 2 ^ n := by
  unfold rankValue
  split_ifs
  · exact residual_count_le H _ hashes marked clause
  · exact Nat.zero_le _

/-- Every instruction and compiled prefix of the fixed stream leaves the
whole durable selector/high-counter interval unchanged. -/
theorem stream_durable_frame {a b : Data} {steps : ℕ}
    (he : Eval QueryStreamProgram.command steps a b)
    (i : Fin 896) (hi : 768 ≤ i.val ∧ i.val ≤ 831) : b.stacks i = a.stacks i := by
  let H := fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831
  have hs := eval_rebase H QuerySelectorFrames.command_avoids he (fun _ => [])
  exact CommandStackTransport.eval_shadow_prefix_frame H QuerySelectorFrames.command_avoids
    330 323 hs (by omega) (compiled_halt_trace he 330 323) i hi

/-- The paid counter copy and real guard restoration preserve the live
accumulator, durable odometer, and both adder/counter scratch words. -/
theorem conditioned_durable_frame {a b : Data} {steps : ℕ}
    (he : Eval QueryStreamProgram.command steps (copiedHighCounter a) b)
    (i : Fin 896) (hi : i ∈ ([788,789,790,791] : List (Fin 896))) :
    (⟨Function.update b.regs 21 true,b.stacks⟩ : Data).stacks i = a.stacks i := by
  change b.stacks i = a.stacks i
  have hr : 768 ≤ i.val ∧ i.val ≤ 831 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  rw [stream_durable_frame he i hr]
  apply copiedHighCounter_frame
  · intro h
    subst i
    simp at hi
  · intro h
    subst i
    simp at hi

/-- The native adder's three local words have a fixed polynomial prefix cap.
Arbitrarily retained caller words enter only through the outside maximum. -/
theorem mass_prefix_at (a b : Data) (steps width B : ℕ) (input output : Fin 896)
    (he : Eval (Mass.invoke highPorts.mass) steps a b)
    (hacc : (a.stacks 788).length ≤ width) (hnext : (a.stacks 323).length ≤ width)
    (hscratch : a.stacks 791 = []) (hB : ∀ i, (a.stacks i).length ≤ B) :
    ∀ t z, t ≤ steps+1 → Trace (compiled (Mass.invoke highPorts.mass) input output) t
      (a.withPC (some (compiled (Mass.invoke highPorts.mass) input output).entry)) z →
      ∀ i, (z.stacks i).length ≤ max (20*(width+1)) B := by
  let regs := fun i => a.regs (highPorts.mass.register i)
  let localStart := Mass.data regs (a.stacks 788) (a.stacks 323)
  have hproject : projectState highPorts.mass.register highPorts.mass.stack a = localStart := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [highPorts, BinaryPrograms.Add.stackState, hscratch]
  obtain ⟨localSteps,hsteps,rf,ht⟩ := Mass.program_trace regs (a.stacks 788) (a.stacks 323)
  have htime : localSteps ≤ 16*(width+1)+2 := by
    have hm := max_le hacc hnext
    omega
  have hi : dataBits (localStart.withPC (some Mass.program.entry)) ≤ 3*width := by
    apply StreamResources.dataBits_le_mul
    intro i
    fin_cases i <;> simp [localStart, Mass.data, BinaryPrograms.Add.stackState, hacc, hnext]
  have hlocal : ∀ t z, t ≤ localSteps → Trace Mass.program t
      (localStart.withPC (some Mass.program.entry)) z →
      ∀ i, (z.stacks i).length ≤ max (20*(width+1)) B := by
    intro t z htle hz i
    have hb := StructuredSpace.local_stack_bound Mass.program
      (steps:=16*(width+1)+2) hi t z (htle.trans htime) hz i
    exact hb.trans ((show 3*width+(16*(width+1)+2) ≤ 20*(width+1) by omega).trans
      (Nat.le_max_left _ _))
  have hlocalTrace : Trace Mass.program localSteps
      ((projectState highPorts.mass.register highPorts.mass.stack a).withPC
        (some Mass.program.entry))
      ((Mass.data rf (BinaryArithmetic.add (a.stacks 788) (a.stacks 323)) []).withPC none) := by
    rw [hproject]
    exact ht
  have hcall := eval_call_from_state Mass.program highPorts.mass.register highPorts.mass.stack a
    highPorts.mass.register_injective highPorts.mass.stack_injective hlocalTrace
  have hp := HighQuerySpace.lifted_call_bound Mass.program highPorts.mass.register
    highPorts.mass.stack highPorts.mass.register_injective highPorts.mass.stack_injective
    a localStart _ hproject localSteps (max (20*(width+1)) B) ht hlocal
    (fun i => (hB i).trans (Nat.le_max_right _ _)) input output
  have hsame : steps = localSteps := StreamResources.eval_steps_eq input output he hcall
  simpa only [hsame] using StructuredSpace.compiled_halt_stack_bound hcall input output hp

open HashGreedyProgram.NativeRound

/-- This composes one actual fixed conditioned-stream execution with its paid
counter copy, guard restoration and native addition. The exact stream answer
is still an explicit per-run fact to be supplied by the stream proof. The
compact endpoint bound is independent of the transient prefix envelope. -/
theorem branch_step_resources_oai {n : ℕ} (H : Finset (Fin n))
    (hashes : List (SparseRow (Fin n) (ZMod 3))) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (rank : ℕ) (hr : rank < 2 ^ H.card)
    (a middle : Data) (querySteps L B D K : ℕ)
    (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
    (hs : StageSpace QueryStreamProgram.command querySteps (copiedHighCounter a) K)
    (hacc : BinaryArithmetic.toNat (a.stacks 788) =
      rankSum (rankValue H hashes marked clause) 0 rank)
    (hlen : (a.stacks 788).length ≤ n+1)
    (hnext : middle.stacks 323 = countWord (rankValue H hashes marked clause rank))
    (htmp : a.stacks 791 = [])
    (hD : ∀ i, (a.stacks i).length ≤ D)
    (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
    (h789 : (a.stacks 789).length ≤ L)
    (hwidth : n+1 ≤ B)
    (hboundary : ∀ i, i ≠ 788 → i ≠ 323 → i ≠ 791 → (middle.stacks i).length ≤ B) :
    ∃ steps b, Eval HighQueryProgram.branch steps a b ∧
      steps ≤ querySteps + 11*L + 16*(n+2) + 15 ∧
      BinaryArithmetic.toNat (b.stacks 788) =
        rankSum (rankValue H hashes marked clause) 0 (rank+1) ∧
      (b.stacks 788).length ≤ n+1 ∧ b.stacks 323=[] ∧ b.stacks 791=[] ∧
      b.stacks 789=a.stacks 789 ∧ b.stacks 790=a.stacks 790 ∧
      b.regs 21=true ∧ (∀ i, (b.stacks i).length ≤ B) ∧
      StageSpace HighQueryProgram.branch (steps+1) a (max (max D K) (20*(n+2))) := by
  let c : Data := ⟨Function.update middle.regs 21 true,middle.stacks⟩
  have hcacc : c.stacks 788=a.stacks 788 := conditioned_durable_frame he 788 (by simp)
  have hctmp : c.stacks 791=[] := (conditioned_durable_frame he 791 (by simp)).trans htmp
  have hclen : (c.stacks 788).length ≤ n+1 := by rw [hcacc]; exact hlen
  have hcnext : c.stacks 323=countWord (rankValue H hashes marked clause rank) := hnext
  obtain ⟨addSteps,rf,haddTime,hadd,hzero,htemp,houtlen,hvalue,hframe⟩ :=
    add_rank H hashes marked clause rank hr c (by rw [hcacc]; exact hacc) hclen hcnext hctmp
  let b := Mass.state highPorts.mass c rf
    (BinaryArithmetic.add (c.stacks 788) (c.stacks 323)) []
  obtain ⟨hconditioned,hconditionedTime,hconditionedSpace⟩ :=
    HighQueryProgram.conditioned_resources a middle querySteps L D K he hs hD h330 h792 h789
  have hcb : ∀ i, (c.stacks i).length ≤ max D K := by
    intro i
    exact hconditionedSpace.bound _ _ (Nat.le_succ _)
      (compiled_trace hconditioned 778 777) i
  have hcwidth : (c.stacks 323).length ≤ n+1 := by
    rw [hcnext]
    exact countWord_length_le (rank_value_le H hashes marked clause rank)
  have hmassSpace : StageSpace (Mass.invoke highPorts.mass) addSteps c
      (max (max D K) (20*(n+2))) := by
    constructor
    intro t z ht hz i
    have hb := mass_prefix_at c b addSteps (n+1) (max D K) 778 777 hadd
      hclen hcwidth hctmp hcb t z (ht.trans (Nat.le_succ _)) hz i
    simpa only [Nat.add_assoc,Nat.max_comm] using hb
  have hcondSpace : StageSpace HighQueryProgram.conditioned (copyHighCost a+(querySteps+1)) a
      (max (max D K) (20*(n+2))) :=
    ⟨fun t z ht hz i => (hconditionedSpace.bound t z (ht.trans (Nat.le_succ _)) hz i).trans
      (Nat.le_max_left _ _)⟩
  have hwhole : Eval HighQueryProgram.branch (copyHighCost a+(querySteps+1)+addSteps) a b :=
    hconditioned.seq hadd
  have hwholeSpace := StageSpace.seq hconditioned hadd hcondSpace hmassSpace
  refine ⟨_,b,hwhole,by omega,hvalue,houtlen,hzero,htemp,?_,?_,?_,?_,?_⟩
  · exact (hframe 789 (by decide) (by decide) (by decide)).trans
      (conditioned_durable_frame he 789 (by simp))
  · exact (hframe 790 (by decide) (by decide) (by decide)).trans
      (conditioned_durable_frame he 790 (by simp))
  · change (Mass.state highPorts.mass c rf _ []).regs 21=true
    unfold Mass.state
    rw [embedState_register_frame]
    · simp [c]
    · rintro ⟨i,hi⟩
      have hv := congrArg Fin.val hi
      simp only [highPorts, Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hv
      have hlt := i.isLt
      omega
  · intro i
    by_cases hi : i=788
    · subst i
      exact houtlen.trans hwidth
    · by_cases hj : i=323
      · subst i
        rw [show b.stacks 323=[] from hzero]
        exact Nat.zero_le _
      · by_cases hk : i=791
        · subst i
          rw [show b.stacks 791=[] from htemp]
          exact Nat.zero_le _
        · rw [hframe i hi hj hk]
          exact hboundary i hi hj hk
  · exact ⟨StructuredSpace.compiled_halt_stack_bound hwhole 778 777 hwholeSpace.bound⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources_oai
