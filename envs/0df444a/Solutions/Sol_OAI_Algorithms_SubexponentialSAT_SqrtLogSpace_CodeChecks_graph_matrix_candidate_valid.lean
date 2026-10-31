-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:20:45.411562+00:00
-- url     : https://prove2.me/submissions/2c0260f0-7833-430c-b744-7c7c68b76198

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_graph_stream_runs
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleOdometer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control increment of framed binary tuples

Tuple components are little-endian Boolean words carried by
`Encoding.encodeList id`. The finite table below skips framing bits and
increments only payload bits, with carry continuing into the next component.
Neither the number of components nor their widths enters the control table.
-/

namespace SubexponentialSAT.ExecCNFTupleOdometer

open SubexponentialSAT.BitProgram SubexponentialSAT.CounterPrograms

theorem encoded_length (words : List (List Bool)) :
    (Encoding.encodeList id words).length =
      2 * words.flatten.length + 2 * words.length + 1 := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    rw [Encoding.length_encodeList_cons]
    simp only [id_eq, List.flatten_cons, List.length_append, List.length_cons]
    omega

end SubexponentialSAT.ExecCNFTupleOdometer

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Enumerators
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators

open BitProgram StructuredCalls ExecCNFTupleEnumeration

/-- The complete current tuple, including record delimiters, stays polynomial.
This is a bound on one word of data, not on the number of enumerated tuples. -/
theorem encoded_shape_length {words : List (List Bool)} {shape : List ℕ}
    (hshape : words.map List.length = shape) :
    (Encoding.encodeList id words).length = 2 * shape.sum + 2 * shape.length + 1 := by
  have hn := congrArg List.length hshape
  have hb := congrArg List.sum hshape
  simp only [List.length_map] at hn
  rw [ExecCNFTupleOdometer.encoded_length, hn]
  simpa only [List.length_flatten] using congrArg (fun n => 2 * n + 2 * shape.length + 1) hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-table conversion of one odometer tuple to one arithmetic candidate.
The input contains only the current candidate. The output is reversed scalar
frames, directly suitable for the existing word and matrix callbacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

open BitProgram CodeCandidates

private theorem initialize_round (bit : Bool) (input output : List Bool)
    (regs : Fin 4 → Bool) (hzero : regs 0 = false) (hone : regs 1 = true) :
    Trace zeroTupleProgram 8 (initializeCfg (some 3) regs (bit :: input) output)
      (initializeCfg (some 3) (readRegs regs 2 3 (some bit)) input
        (true :: true :: false :: true :: false :: false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr,
    readRegs, Function.update_apply, hzero, hone]
  all_goals (funext i; fin_cases i <;> simp)

private theorem initialize_loop (input output : List Bool) (regs : Fin 4 → Bool)
    (hzero : regs 0 = false) (hone : regs 1 = true) :
    ∃ rf, Trace zeroTupleProgram (8 * input.length + 3)
      (initializeCfg (some 3) regs input output)
      (initializeCfg none rf []
        ((List.replicate input.length [true, true, false, true, false, false]).flatten ++ output)) := by
  induction input generalizing regs output with
  | nil =>
      refine ⟨readRegs regs 2 3 none, ?_⟩
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr,
        readRegs, Function.update_apply]
  | cons bit input ih =>
      obtain ⟨rf, hr⟩ := ih
        (true :: true :: false :: true :: false :: false :: output)
        (readRegs regs 2 3 (some bit))
        (by simpa [readRegs] using hzero) (by simpa [readRegs] using hone)
      refine ⟨rf, ?_⟩
      have h := (initialize_round bit input output regs hzero hone).trans hr
      simpa [List.length_cons, List.replicate_succ', List.flatten_append,
        List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h

private theorem initialize_encoding (d : ℕ) :
    (List.replicate d [true, true, false, true, false, false]).flatten ++ [false] =
      Encoding.encodeList id (List.replicate d [false, false]) := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simpa [List.replicate_succ, Encoding.encodeList, Encoding.frame] using
        congrArg (fun rest => true :: true :: false :: true :: false :: false :: rest) ih

/-- Empty dimensions produce the one-bit empty tuple, not an absent witness. -/
theorem initialize_trace (input : List Bool) (regs : Fin 4 → Bool) :
    ∃ rf, Trace zeroTupleProgram (8 * input.length + 6)
      (initializeCfg (some zeroTupleProgram.entry) regs input [])
      (initializeCfg none rf []
        (Encoding.encodeList id (List.replicate input.length [false, false]))) := by
  let ready := Function.update (Function.update regs 0 false) 1 true
  have hstart : Trace zeroTupleProgram 3 (initializeCfg (some zeroTupleProgram.entry) regs input [])
      (initializeCfg (some 3) ready input [false]) := by
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply, step, zeroTupleProgram, initializeCfg, execInstr, ready]
    first | done | (funext i; fin_cases i <;> rfl)
  obtain ⟨rf, hr⟩ := initialize_loop input [false] ready (by simp [ready]) (by simp [ready])
  refine ⟨rf, ?_⟩
  have h := hstart.trans hr
  have htime : 3 + (8 * input.length + 3) = 8 * input.length + 6 := by omega
  rw [htime] at h
  simpa [initialize_encoding] using h

/-- The dimension is consumed from one caller port; all other caller tapes
survive the concrete constructor call. -/
theorem initialize_call {R S : ℕ} (register : Fin 4 ↪ Fin R) (stack : Fin 2 ↪ Fin S)
    (a : StructuredCalls.State R S) (houtput : a.stacks (stack 1) = []) :
    ∃ b : StructuredCalls.State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram zeroTupleProgram register stack))
        (8 * (a.stacks (stack 0)).length + 6) a b ∧
      b.stacks (stack 0) = [] ∧
      b.stacks (stack 1) = Encoding.encodeList id
        (List.replicate (a.stacks (stack 0)).length [false, false]) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) := by
  obtain ⟨rf, ht⟩ := initialize_trace (a.stacks (stack 0)) (a.regs ∘ register)
  let final : StructuredCalls.State 4 2 :=
    ⟨rf, ![[], Encoding.encodeList id
      (List.replicate (a.stacks (stack 0)).length [false, false])]⟩
  have hstart : (StructuredCalls.projectState register stack a).withPC
      (some zeroTupleProgram.entry) =
      initializeCfg (some zeroTupleProgram.entry) (a.regs ∘ register)
        (a.stacks (stack 0)) [] := by
    change (⟨some zeroTupleProgram.entry, a.regs ∘ register, a.stacks ∘ stack⟩ : Cfg 4 2 12) = _
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact houtput
  have ht' : Trace zeroTupleProgram (8 * (a.stacks (stack 0)).length + 6)
      ((StructuredCalls.projectState register stack a).withPC (some zeroTupleProgram.entry))
      (final.withPC none) := by rw [hstart]; exact ht
  refine ⟨StructuredCalls.embedState register stack a final,
    StructuredCalls.eval_call_from_state zeroTupleProgram register stack a
      register.injective stack.injective ht', ?_, ?_, ?_, ?_⟩
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 0
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 1
  · exact fun i hi => StructuredCalls.embedState_stack_frame _ _ _ _ i hi
  · exact fun i hi => StructuredCalls.embedState_register_frame _ _ _ _ i hi

private theorem convert_read (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 7
      (cfg (some 1) regs (true :: true :: a :: true :: b :: false :: input) output)
      (cfg (some 8) ![false, true, a, b, regs 4] input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, convert, cfg, execInstr, readRegs,
    Function.update_apply]
  all_goals first | (constructor <;> funext i <;> fin_cases i <;> simp) | (funext i <;> fin_cases i <;> simp)

private theorem convert_write (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 9
      (cfg (some 8) ![false, true, a, b, regs 4] input output)
      (cfg (some 1) (roundRegs ternary regs a b) input
        (false :: b :: true :: a :: true :: output)) := by
  cases ternary <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, convert, cfg, roundRegs, invalidDigit,
      execInstr, readRegs, Function.update_apply] <;>
    all_goals first | (constructor <;> funext i <;> fin_cases i <;> simp) | (funext i <;> fin_cases i <;> simp)

private theorem convert_round (ternary a b : Bool) (regs : Fin 5 → Bool)
    (input output : List Bool) :
    Trace (convert ternary) 16
      (cfg (some 1) regs (true :: true :: a :: true :: b :: false :: input) output)
      (cfg (some 1) (roundRegs ternary regs a b) input
        (false :: b :: true :: a :: true :: output)) :=
  (convert_read ternary a b regs input output).trans
    (convert_write ternary a b regs input output)

private theorem convert_exit (ternary : Bool) (regs : Fin 5 → Bool) (output : List Bool) :
    Trace (convert ternary) 3
      (cfg (some 1) regs [false] output)
      (cfg none (readRegs regs 0 1 (some false)) [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, convert, cfg, execInstr, readRegs,
    Function.update_apply]
  all_goals (funext i; fin_cases i <;> simp)

private theorem convert_loop (ternary : Bool) (xs : List (Bool × Bool))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ rf, rf 4 = (regs 4 || xs.any (invalidDigit ternary)) ∧
      Trace (convert ternary) (16 * xs.length + 3)
        (cfg (some 1) regs (tupleBits xs) output)
        (cfg none rf [] ((scalarFrames xs).reverse ++ output)) := by
  induction xs generalizing regs output with
  | nil =>
    refine ⟨readRegs regs 0 1 (some false), ?_, ?_⟩
    · simp [readRegs]
    · simpa [tupleBits, scalarFrames, Encoding.encodeList] using convert_exit ternary regs output
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    obtain ⟨rf, hr, ht⟩ := ih (roundRegs ternary regs a b)
      (false :: b :: true :: a :: true :: output)
    refine ⟨rf, ?_, ?_⟩
    · simpa [roundRegs, Bool.or_assoc] using hr
    · have h := (convert_round ternary a b regs (tupleBits xs) output).trans ht
      simpa [tupleBits, scalarFrames, Encoding.encodeList, Encoding.frame, digitBits,
        Function.comp_def, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        List.append_assoc] using h

/-- Complete execution, including initialization, every rejected digit and halt. -/
theorem convert_trace (ternary : Bool) (xs : List (Bool × Bool))
    (regs : Fin 5 → Bool) (output : List Bool) :
    ∃ rf, rf 4 = xs.any (invalidDigit ternary) ∧
      Trace (convert ternary) (16 * xs.length + 4)
        (cfg (some 0) regs (tupleBits xs) output)
        (cfg none rf [] ((scalarFrames xs).reverse ++ output)) := by
  obtain ⟨rf, hr, ht⟩ := convert_loop ternary xs (Function.update regs 4 false) output
  refine ⟨rf, by simpa using hr, ?_⟩
  have hstart : step (convert ternary) (cfg (some 0) regs (tupleBits xs) output) =
      some (cfg (some 1) (Function.update regs 4 false) (tupleBits xs) output) := by
    simp [step, convert, cfg, execInstr]
  have h := Computation.Trace.cons hstart ht
  convert h using 1
  all_goals try with_reducible_and_instances rfl

/-- Concrete port relocation, preserving the entire off-port caller frame. -/
theorem convert_call {R S : ℕ} (ternary : Bool)
    (register : Fin 5 ↪ Fin R) (stack : Fin 2 ↪ Fin S)
    (xs : List (Bool × Bool)) (a : StructuredCalls.State R S)
    (hinput : a.stacks (stack 0) = tupleBits xs) :
    ∃ b : StructuredCalls.State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram (convert ternary) register stack))
        (16 * xs.length + 4) a b ∧
      b.regs (register 4) = xs.any (invalidDigit ternary) ∧
      b.stacks (stack 0) = [] ∧
      b.stacks (stack 1) = (scalarFrames xs).reverse ++ a.stacks (stack 1) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) := by
  obtain ⟨rf, hr, ht⟩ := convert_trace ternary xs (a.regs ∘ register) (a.stacks (stack 1))
  let final : StructuredCalls.State 5 2 :=
    ⟨rf, ![[], (scalarFrames xs).reverse ++ a.stacks (stack 1)]⟩
  have hstart : (StructuredCalls.projectState register stack a).withPC (some (convert ternary).entry) =
      cfg (some 0) (a.regs ∘ register) (tupleBits xs) (a.stacks (stack 1)) := by
    change (⟨some 0, a.regs ∘ register, a.stacks ∘ stack⟩ : Cfg 5 2 18) = _
    congr 1
    funext i
    fin_cases i
    · exact hinput
    · rfl
  have ht' : Trace (convert ternary) (16 * xs.length + 4)
      ((StructuredCalls.projectState register stack a).withPC (some (convert ternary).entry))
      (final.withPC none) := by rw [hstart]; exact ht
  refine ⟨StructuredCalls.embedState register stack a final,
    StructuredCalls.eval_call_from_state (convert ternary) register stack a
      register.injective stack.injective ht', ?_, ?_, ?_, ?_, ?_⟩
  · exact (StructuredCalls.embedState_register _ _ _ _ register.injective 4).trans hr
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 0
  · exact StructuredCalls.embedState_stack _ _ _ _ stack.injective 1
  · exact fun i hi => StructuredCalls.embedState_stack_frame _ _ _ _ i hi
  · exact fun i hi => StructuredCalls.embedState_register_frame _ _ _ _ i hi

/-- Preparing one streaming scan restores the dimension copy and scratch;
only the counter and the one-bit rejection latch are initialized. -/
theorem prepareScan_eval {S : ℕ} (p : ScanPorts S) (a : StructuredCalls.State 16 S)
    (hi : a.stacks (p.stack 1) = []) (hc : a.stacks (p.stack 2) = [])
    (hs : a.stacks (p.stack 3) = []) (hl : a.stacks (p.stack 4) = []) :
    ∃ b, StructuredCalls.Eval (prepareScan p) (15 * (a.stacks (p.stack 0)).length + 13) a b ∧
      b.stacks = Function.update
        (Function.update a.stacks (p.stack 2)
          (Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false])))
        (p.stack 4) [false] := by
  let copied : StructuredCalls.State 16 S :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks (p.stack 0) (p.stack 1) a.stacks⟩
  have hcopy : StructuredCalls.Eval
      (.call (StackRoutines.copyProgram (p.stack 0) (p.stack 1) (p.stack 3) 0 1))
      (7 * (a.stacks (p.stack 0)).length + 5) a copied :=
    .call _ (ListRegisterProgram.copy_run _ _ _ _ _
      (p.stack.injective.ne (by decide)) (p.stack.injective.ne (by decide))
      (p.stack.injective.ne (by decide)) (by decide) a.regs a.stacks hs)
  have hcopied : copied.stacks (p.stack 1) = a.stacks (p.stack 0) := by
    simp [copied, StackRoutines.copyStacks, hi]
  have hcopiedFrame (i : Fin S) (hne : i ≠ p.stack 1) : copied.stacks i = a.stacks i := by
    simp [copied, StackRoutines.copyStacks, hne]
  have houtput : copied.stacks ((scanInitializePorts p) 1) = [] := by
    change copied.stacks (p.stack 2) = []
    exact (hcopiedFrame _ (p.stack.injective.ne (by decide))).trans hc
  obtain ⟨initialized, hinitialize, hempty, htuple, hframe, _⟩ :=
    initialize_call scanRegisters (scanInitializePorts p) copied houtput
  have hinitInput : initialized.stacks (p.stack 1) = [] := hempty
  have hinitCounter : initialized.stacks (p.stack 2) =
      Encoding.encodeList id (List.replicate (a.stacks (p.stack 0)).length [false, false]) := by
    change initialized.stacks (p.stack 2) = Encoding.encodeList id
      (List.replicate (copied.stacks (p.stack 1)).length [false, false]) at htuple
    simpa only [hcopied] using htuple
  have hinitFrame (i : Fin S) (h1 : i ≠ p.stack 1) (h2 : i ≠ p.stack 2) :
      initialized.stacks i = a.stacks i := by
    rw [hframe i (by
      rintro ⟨j, hj⟩
      fin_cases j
      · exact h1 hj.symm
      · exact h2 hj.symm)]
    exact hcopiedFrame i h1
  let flagged := (StructuredProgram.Atom.set (s := S) 13 false).eval initialized
  let b := (StructuredProgram.Atom.push (p.stack 4) (13 : Fin 16)).eval flagged
  have hseed : StructuredCalls.Eval
      (.seq (.base (.atom (.set 13 false))) (.base (.atom (.push (p.stack 4) 13))))
      2 initialized b := .seq (.base (.atom _ _)) (.base (.atom _ _))
  refine ⟨b, ?_, ?_⟩
  · have h := hcopy.seq (hinitialize.seq hseed)
    change StructuredCalls.Eval (prepareScan p)
      ((7 * (a.stacks (p.stack 0)).length + 5) +
        ((8 * (copied.stacks (p.stack 1)).length + 6) + 2)) a b at h
    rw [hcopied] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · have hlatch : initialized.stacks (p.stack 4) = [] :=
      (hinitFrame _ (p.stack.injective.ne (by decide))
        (p.stack.injective.ne (by decide))).trans hl
    have hb : b.stacks = Function.update initialized.stacks (p.stack 4) [false] := by
      simp [b, flagged, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, hlatch]
    rw [hb]
    funext i
    by_cases h4 : i = p.stack 4
    · subst i; simp
    by_cases h2 : i = p.stack 2
    · subst i; simp [h4, hinitCounter]
    by_cases h1 : i = p.stack 1
    · subst i; simp [h4, h2, hinitInput, hi]
    · simp [h4, h2, hinitFrame i h1 h2]

theorem finishScan_eval {S : ℕ} (counter latch : Fin S) (hcl : counter ≠ latch)
    (a : StructuredCalls.State 16 S) (rejected : Bool) (hl : a.stacks latch = [rejected]) :
    ∃ b, StructuredCalls.Eval (finishScan counter latch)
      (2 * (a.stacks counter).length + 5) a b ∧ b.regs 15 = !rejected ∧
      b.stacks = Function.update (Function.update a.stacks latch []) counter [] := by
  let popped := (StructuredProgram.Atom.pop latch (13 : Fin 16) 14).eval a
  let flagged := (StructuredProgram.Atom.bnot (s := S) (15 : Fin 16) 13).eval popped
  let b : StructuredCalls.State 16 S :=
    ⟨readRegs flagged.regs 0 1 none, StackRoutines.clearStacks counter flagged.stacks⟩
  have hcounter : flagged.stacks counter = a.stacks counter := by
    simp [flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hcl]
  have hclear : StructuredCalls.Eval (.call (StackRoutines.clearProgram counter 0 1))
      (2 * (flagged.stacks counter).length + 3) flagged b :=
    .call _ (ListRegisterProgram.clear_run _ _ _ _ _)
  refine ⟨b, ?_, ?_, ?_⟩
  · have h := (StructuredCalls.Eval.base (.atom (.pop latch 13 14) a)).seq
      ((StructuredCalls.Eval.base (.atom (.bnot 15 13) popped)).seq hclear)
    rw [hcounter] at h
    convert h using 1
    · rfl
    · omega
  · simp [b, flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hl]
  · simp [b, flagged, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      StackRoutines.clearStacks, hl]

/-- The native setup, complete core scan, actual Boolean readout and cleanup
form one measured run. Its storage uses the core's prefix bound, never the
core's possibly exponential running time. -/
theorem scanWrapper_resources {S l A B T : ℕ} (p : ScanPorts S) (core : Program 16 S l)
    (a : StructuredCalls.State 16 S) (rejected : Bool)
    (hi : a.stacks (p.stack 1) = []) (hc : a.stacks (p.stack 2) = [])
    (hs : a.stacks (p.stack 3) = []) (hl : a.stacks (p.stack 4) = [])
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcore : ∀ prepared : StructuredCalls.State 16 S,
      prepared.stacks = scanPreparedStacks p a →
      ∃ (n : ℕ) (middle : StructuredCalls.State 16 S), n ≤ T ∧
        Trace core n (prepared.withPC (some core.entry)) (middle.withPC none) ∧
        middle.stacks (p.stack 4) = [rejected] ∧
        (∀ i, i ≠ p.stack 2 → i ≠ p.stack 4 → middle.stacks i = prepared.stacks i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ n →
          Trace core prefixSteps (prepared.withPC (some core.entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ B) :
    ∃ steps out, StructuredCalls.Eval (scanWrapper p core) steps a out ∧
      steps ≤ T + 15 * (a.stacks (p.stack 0)).length + 2 * B + 18 ∧
      out.regs 15 = !rejected ∧ out.stacks = a.stacks ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (StructuredCalls.compiled (scanWrapper p core) (p.stack 0) (p.stack 4))
          prefixSteps (a.withPC (some (StructuredCalls.compiled
            (scanWrapper p core) (p.stack 0) (p.stack 4)).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          S * A + 15 * (a.stacks (p.stack 0)).length + S * B + 3 * B + 18 := by
  obtain ⟨prepared, hprepare, hprepared⟩ := prepareScan_eval p a hi hc hs hl
  obtain ⟨n, middle, hn, htrace, hlatch, hframe, hspace⟩ := hcore prepared hprepared
  have hmiddle : ∀ i, (middle.stacks i).length ≤ B :=
    hspace n _ (Nat.le_refl _) htrace
  obtain ⟨out, hfinish, hanswer, hout⟩ := finishScan_eval (p.stack 2) (p.stack 4)
    (p.stack.injective.ne (by decide)) middle rejected hlatch
  have hcall : StructuredCalls.Eval (.call core) n prepared middle := .call _ htrace
  let bound := S * A + 15 * (a.stacks (p.stack 0)).length + S * B + 3 * B + 18
  have hprepareSpace : ∀ prefixSteps intermediate,
      prefixSteps ≤ 15 * (a.stacks (p.stack 0)).length + 13 →
      Trace (StructuredCalls.compiled (prepareScan p) (p.stack 0) (p.stack 4))
        prefixSteps (a.withPC (some (StructuredCalls.compiled
          (prepareScan p) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle ht i
    have hinit : dataBits (a.withPC (some (StructuredCalls.compiled
        (prepareScan p) (p.stack 0) (p.stack 4)).entry)) ≤ S * A :=
      StreamResources.dataBits_le_mul _ ha
    have h := StructuredSpace.local_stack_bound
      (StructuredCalls.compiled (prepareScan p) (p.stack 0) (p.stack 4))
      (steps := 15 * (a.stacks (p.stack 0)).length + 13) hinit prefixSteps intermediate hle ht i
    dsimp [bound]
    omega
  have hcallSpace : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled (.call core) (p.stack 0) (p.stack 4)) prefixSteps
        (prepared.withPC (some (StructuredCalls.compiled
          (.call core) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    have h := StructuredSpace.call_stack_bound core
      (StructuredCalls.compiled (.call core) (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (.call core)) (StructuredCalls.exitAddress (.call core))
      (fun pc => StructuredCalls.compiled_site (.call core) (p.stack 0) (p.stack 4) pc)
      htrace hspace
    intro prefixSteps intermediate hle ht i
    have hb := h prefixSteps intermediate hle ht i
    dsimp [bound]
    omega
  have hfinishSpace : ∀ prefixSteps intermediate,
      prefixSteps ≤ 2 * (middle.stacks (p.stack 2)).length + 5 →
      Trace (StructuredCalls.compiled (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4))
        prefixSteps (middle.withPC (some (StructuredCalls.compiled
          (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4)).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle ht i
    have hinit : dataBits (middle.withPC (some (StructuredCalls.compiled
        (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4)).entry)) ≤ S * B :=
      StreamResources.dataBits_le_mul _ hmiddle
    have h := StructuredSpace.local_stack_bound
      (StructuredCalls.compiled (finishScan (p.stack 2) (p.stack 4)) (p.stack 0) (p.stack 4))
      (steps := 2 * B + 5) hinit prefixSteps intermediate (by have := hmiddle (p.stack 2); omega) ht i
    dsimp [bound]
    omega
  refine ⟨(15 * (a.stacks (p.stack 0)).length + 13) +
    (n + (2 * (middle.stacks (p.stack 2)).length + 5)), out,
    hprepare.seq (hcall.seq hfinish), ?_, hanswer, ?_, ?_⟩
  · have := hmiddle (p.stack 2)
    omega
  · rw [hout]
    funext i
    by_cases h2 : i = p.stack 2
    · subst i; simp [hc]
    by_cases h4 : i = p.stack 4
    · subst i; simp [h2, hl]
    simp only [Function.update_of_ne h2, Function.update_of_ne h4]
    rw [hframe i h2 h4, hprepared]
    simp [h2, h4]
  · have hseq := StructuredSpace.sequence_stack_bound hcall hfinish (p.stack 0) (p.stack 4)
      hcallSpace hfinishSpace
      (StructuredCalls.compiled (.seq (.call core) (finishScan (p.stack 2) (p.stack 4)))
        (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (.seq (.call core) (finishScan (p.stack 2) (p.stack 4))))
      (StructuredCalls.exitAddress (.seq (.call core) (finishScan (p.stack 2) (p.stack 4))))
      (StructuredCalls.compiled_site _ (p.stack 0) (p.stack 4))
    exact StructuredSpace.sequence_stack_bound hprepare (hcall.seq hfinish) (p.stack 0) (p.stack 4)
      hprepareSpace hseq
      (StructuredCalls.compiled (scanWrapper p core) (p.stack 0) (p.stack 4))
      (StructuredCalls.siteAddress (scanWrapper p core))
      (StructuredCalls.exitAddress (scanWrapper p core))
      (StructuredCalls.compiled_site _ (p.stack 0) (p.stack 4))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixProgram

theorem matrixWords_eq_words_flatten (rows : List (List (List Bool))) :
    matrixWords rows = words rows.flatten := by
  induction rows with
  | nil => rfl
  | cons ys rows ih => simp [matrixWords, List.flatten_cons, words_append, ih]

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramRepresentation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-for-byte agreement between generated candidates and arithmetic inputs.
These identities remove recoding from the search interface; they are not
assumptions that a rearrangement of an existing tape is cost-free. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem words_eq_flatMap (xs : List (List Bool)) :
    Subexp.MatrixProgramSupport.words xs = xs.flatMap Encoding.frame := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Subexp.MatrixProgramSupport.words, ih]

theorem framedVector_eq_scalarFrames {p d : ℕ} [Fact p.Prime]
    (v : Fin d → ZMod p) : framedVector v = scalarFrames (List.ofFn v) := by
  simp [framedVector, SubexpTupleRefinement.encodeTuple,
    StackEncoding.encodeDataStack_eq_flatMap, framedScalarCode,
    Subexp.BasisTransposeProgram.framedCode, scalarFrames,
    words_eq_flatMap, SubexpEnumerationPayload.scalarCode]
  rw [← List.map_ofFn]
  simp only [List.flatMap_map, scalarWord_eq]

theorem flattenMatrix_ofFn {p rows cols : ℕ}
    (M : Fin rows → Fin cols → ZMod p) :
    List.ofFn (flattenMatrix M) =
      (List.ofFn fun i => List.ofFn fun j => M i j).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hidx : (finProdFinEquiv (i,j)).val = i.val * cols + j.val := by
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  change flattenMatrix M ⟨i.val * cols + j.val, _⟩ = M i j
  rw [show (⟨i.val * cols + j.val, _⟩ : Fin (rows * cols)) =
      finProdFinEquiv (i,j) from Fin.ext hidx.symm]
  simp [flattenMatrix]

theorem framedMatrix_eq_matrixFrames {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) : framedMatrix M = matrixFrames M := by
  rw [framedMatrix, framedVector_eq_scalarFrames, flattenMatrix_ofFn]
  simp [scalarFrames, matrixFrames, words_eq_flatMap,
    Subexp.MatrixVectorProgram.matrixWords_eq_words_flatten,
    List.map_flatten, List.map_ofFn, Function.comp_def]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Space of the concrete sparse-code predicates

The local-code and Walsh predicates are polynomial-time bit programs. These bounds apply
to every candidate, including losing candidates, and every stack in each actual source
prefix. They are intended as the body estimates of bounded-memory enumeration; the
materialized candidate-family programs are not used here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem field_frames_eq {p d : ℕ} [Fact p.Prime] (x : Fin d → ZMod p) :
    (CodeCandidates.fieldWords x).flatMap Encoding.frame = scalarFrames (List.ofFn x) := by
  simp [CodeCandidates.fieldWords, scalarFrames, words_eq_flatMap,
    scalarWord_eq, List.map_ofFn, Function.comp_def]

theorem pair_frames_eq {p d : ℕ} [Fact p.Prime] (xs : List (Bool × Bool))
    (x : Fin d → ZMod p) (h : xs.map CodeCandidates.digitBits = CodeCandidates.fieldWords x) :
    CodeCandidates.scalarFrames xs = scalarFrames (List.ofFn x) := by
  rw [← field_frames_eq, ← h, List.flatMap_map]
  rfl

/-- Conversion is paid for afresh at every visit. The current counter remains
available, while the temporary input is consumed and all off-port stacks survive. -/
theorem copy_convert_eval {S : ℕ} (ternary : Bool)
    (current input payload scratch : Fin S)
    (hci : current ≠ input) (hct : current ≠ scratch) (hti : scratch ≠ input)
    (hip : input ≠ payload) (xs : List (Bool × Bool)) (a : State 16 S)
    (hcurrent : a.stacks current = CodeCandidates.tupleBits xs)
    (hinput : a.stacks input = []) (hpayload : a.stacks payload = [])
    (hscratch : a.stacks scratch = []) :
    ∃ b, Eval (copyConvertCommand ternary current input payload scratch)
        (58 * xs.length + 16) a b ∧
      b.regs 4 = xs.any (CodeCandidates.invalidDigit ternary) ∧
      b.stacks input = [] ∧ b.stacks payload = (CodeCandidates.scalarFrames xs).reverse ∧
      (∀ i, i ≠ input → i ≠ payload → b.stacks i = a.stacks i) := by
  let copied := SubexpSetupStorage.copyState current input a
  have hcopy := SubexpSetupStorage.copy_eval current input scratch a hci hct hti hscratch
  have hcopied : copied.stacks input = CodeCandidates.tupleBits xs := by
    simp [copied, SubexpSetupStorage.copyState_stack, hcurrent, hinput]
  let registers : Fin 5 ↪ Fin 16 := ⟨Fin.castAdd 11, Fin.castAdd_injective _ _⟩
  let ports : Fin 2 ↪ Fin S := ⟨![input, payload], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨b, hrun, hflag, hempty, hword, hframe, _⟩ :=
    CodeCandidateProgram.convert_call ternary registers ports xs copied hcopied
  refine ⟨b, ?_, hflag, hempty, ?_, ?_⟩
  · have h := hcopy.seq hrun
    rw [hcurrent, CodeCandidates.tupleBits_length] at h
    convert h using 1
    · rfl
    · omega
  · have hcopypayload : copied.stacks payload = [] :=
      (SubexpSetupStorage.copyState_frame current input payload a (Ne.symm hip)).trans hpayload
    change b.stacks payload = (CodeCandidates.scalarFrames xs).reverse ++ copied.stacks payload at hword
    simpa only [hcopypayload, List.append_nil] using hword
  · intro i hi hp
    rw [hframe i (by
      rintro ⟨j, hj⟩
      fin_cases j
      · change input = i at hj
        exact hi hj.symm
      · change payload = i at hj
        exact hp hj.symm)]
    exact SubexpSetupStorage.copyState_frame current input i a hi

/-- Matrix scalar order agrees with the original row-major matrix encoding.
The converter therefore stages one actual matrix without recoding a family. -/
theorem pair_matrix_frames_eq {p rows cols : ℕ} [Fact p.Prime]
    (xs : List (Bool × Bool)) (M : Fin rows → Fin cols → ZMod p)
    (h : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords M) :
    CodeCandidates.scalarFrames xs = matrixFrames M := by
  calc
    CodeCandidates.scalarFrames xs = scalarFrames (List.ofFn (flattenMatrix M)) :=
      pair_frames_eq xs (flattenMatrix M) h
    _ = framedMatrix M := (framedVector_eq_scalarFrames (flattenMatrix M)).symm
    _ = matrixFrames M := framedMatrix_eq_matrixFrames M

theorem installMatrix_eval {S : ℕ} (payload matrix : Fin S) (hpm : payload ≠ matrix)
    (word : List Bool) (a : State 16 S) (hp : a.stacks payload = word.reverse) :
    ∃ out, Eval (installMatrix payload matrix)
        (2 * (a.stacks matrix).length + 3 * word.length + 6) a out ∧
      out.stacks payload = [] ∧ out.stacks matrix = word ∧
      (∀ i, i ≠ payload → i ≠ matrix → out.stacks i = a.stacks i) := by
  let cleared := SubexpSetupStorage.clearState matrix a
  let out := SubexpScanPrimitives.afterTransfer cleared payload matrix 0 1
  have hc := SubexpSetupStorage.clear_eval matrix a
  have ht := SubexpScanPrimitives.transfer_eval cleared payload matrix 0 1 hpm (by decide)
  have hpayload : cleared.stacks payload = word.reverse := by
    simpa [cleared, SubexpSetupStorage.clearState, hpm] using hp
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · have he := hc.seq ht
    rw [hpayload, List.length_reverse] at he
    convert he using 1
    · rfl
    · omega
  · simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, hpm]
  · simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, hpm,
      cleared, SubexpSetupStorage.clearState, hp]
  · intro i hi hj
    simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
      cleared, SubexpSetupStorage.clearState, hi, hj]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/



namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

private theorem zero_tuple_encoded_length (d : ℕ) :
    (Encoding.encodeList id (List.replicate d [false, false])).length = 6 * d + 1 := by
  rw [Enumerators.encoded_shape_length (by simp :
    (List.replicate d [false, false]).map List.length = List.replicate d 2)]
  simp
  omega

private theorem scan_prepared_bound {S A : ℕ} (p : CodeCandidateProgram.ScanPorts S)
    (a prepared : State 16 S) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hp : prepared.stacks = CodeCandidateProgram.scanPreparedStacks p a) :
    ∀ i, (prepared.stacks i).length ≤ A + 6 * (a.stacks (p.stack 0)).length + 1 := by
  intro i
  rw [hp]
  unfold CodeCandidateProgram.scanPreparedStacks
  by_cases hi : i = p.stack 4
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    by_cases hj : i = p.stack 2
    · subst i
      rw [Function.update_self, zero_tuple_encoded_length]
      omega
    · rw [Function.update_of_ne hj]
      have hb := ha i
      omega

private theorem rejection_bool (bit : Bool) (P : Prop) [Decidable P]
    (h : bit = false ↔ P) : bit = !(decide P) := by
  cases bit <;> simp_all

/-- Complete actual graph-matrix checker: it initializes its word counter,
checks every word, computes the Boolean acceptance bit, then clears temporary
state. Time and the uniform source-prefix space bound describe the same run. -/
theorem graph_checker_runs {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D) (a : ScanState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hDbits : a.stacks 32 = Dbits) (hr : a.stacks 33 = List.replicate r true)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcounter : a.stacks 36 = [])
    (hlatch : a.stacks 37 = []) (hscratch : a.stacks 38 = []) (hcopy : a.stacks 39 = []) :
    ∃ steps out, Eval graphChecker steps a out ∧
      steps ≤ graphStreamBudget D r qbits.length Dbits.length + 15 * r + 2 * coreSpace A r (graphCallbackBudget D r qbits.length Dbits.length) + 18 ∧
      (out.regs 15 = true ↔ WalshExistence.Good q s) ∧ out.stacks = a.stacks ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (compiled graphChecker 33 37) prefixSteps
          (a.withPC (some (compiled graphChecker 33 37).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          40 * A + 15 * r + 43 * coreSpace A r (graphCallbackBudget D r qbits.length Dbits.length) + 18) := by
  classical
  have hcore : ∀ prepared : ScanState,
      prepared.stacks = CodeCandidateProgram.scanPreparedStacks graphScanPorts a →
      ∃ (n : ℕ) (middle : ScanState), n ≤ graphStreamBudget D r qbits.length Dbits.length ∧
        Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) n
          (prepared.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
          (middle.withPC none) ∧
        middle.stacks 37 = [!(decide (WalshExistence.Good q s))] ∧
        (∀ i, i ≠ 36 → i ≠ 37 → middle.stacks i = prepared.stacks i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ n →
          Trace (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody) prefixSteps
            (prepared.withPC (some (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ coreSpace A r (graphCallbackBudget D r qbits.length Dbits.length) := by
    intro prepared hprepared
    have hf (i : Fin 40) (hi : i ≠ 36) (hj : i ≠ 37) : prepared.stacks i = a.stacks i := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, graphScanPorts, hi, hj]
    have hb : ∀ i, (prepared.stacks i).length ≤ A + 6 * r + 1 := by
      simpa [graphScanPorts, hr] using scan_prepared_bound graphScanPorts a prepared ha hprepared
    have hcounter' : prepared.stacks 36 = Encoding.encodeList id (List.replicate r [false, false]) := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, graphScanPorts, hr]
    have hlatch' : prepared.stacks 37 = [false] := by
      rw [hprepared]
      simp [CodeCandidateProgram.scanPreparedStacks, graphScanPorts]
    have he' : GraphWorkEmpty (projectState id graphStreamStacks prepared) := by
      intro i
      apply (hf _ ?_ ?_).trans (he i)
      all_goals
        intro h
        have hv := congrArg Fin.val h
        change i.val = _ at hv
        have hi := i.isLt
        omega
    obtain ⟨n, middle, hn, htrace, hframe, hscratch', hdecide, hspace⟩ :=
      graph_stream_runs s q qbits Dbits hqv hDv prepared he' ((hf 29 (by decide) (by decide)).trans hm)
        ((hf 30 (by decide) (by decide)).trans ht) ((hf 31 (by decide) (by decide)).trans hq)
        ((hf 32 (by decide) (by decide)).trans hDbits)
        ((hf 34 (by decide) (by decide)).trans hp) ((hf 35 (by decide) (by decide)).trans htmp)
        ((hf 39 (by decide) (by decide)).trans hcopy) hcounter'
        ((hf 38 (by decide) (by decide)).trans hscratch) hlatch'
        (A + 6 * r + 1) (by omega) hb
    obtain ⟨bit, hbit⟩ := hframe.latch_word
    have hbitvalue : bit = !(decide (WalshExistence.Good q s)) :=
      rejection_bool bit _ (by simpa [hbit] using hdecide)
    refine ⟨n, middle, hn, htrace, hbit.trans (congrArg List.singleton hbitvalue), ?_, hspace⟩
    intro i hi hj
    by_cases hs : i = 38
    · subst i
      exact hscratch'.trans ((hf 38 (by decide) (by decide)).trans hscratch).symm
    · exact hframe.frame i hi hs hj
  obtain ⟨steps, out, hrun, htime, hanswer, hout, hspace⟩ :=
    CodeCandidateProgram.scanWrapper_resources graphScanPorts
      (ExecCNFTupleEnumeration.program graphCounterPorts graphStreamBody)
      a (!(decide (WalshExistence.Good q s))) hcopy hcounter htmp hlatch ha hcore
  refine ⟨steps, out, hrun, ?_, ?_, hout, ?_⟩
  · simpa [graphScanPorts, hr] using htime
  · simp only [hanswer, Bool.not_not, decide_eq_true_eq]
  · have hsum (A q b : ℕ) : 40 * A + 15 * q + 40 * b + 3 * b + 18 =
        40 * A + 15 * q + 43 * b + 18 := by omega
    simpa [graphChecker, graphScanPorts, hr, hsum] using hspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- A complete checker call keeps its local every-prefix space proof after
embedding; the eight persistent outer-search stacks are counted separately. -/
theorem lift_checker_resources (checker : Cmd 16 40) (input output : Fin 40)
    (a : MatrixState) (small : ScanState) {n A B : ℕ}
    (hrun : Eval checker n (projectState id checkerPorts a) small)
    (hrestore : small.stacks = (projectState id checkerPorts a).stacks)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hspace : ∀ k c, k ≤ n → Trace (compiled checker input output) k
      ((projectState id checkerPorts a).withPC (some (compiled checker input output).entry)) c →
      ∀ i, (c.stacks i).length ≤ B) :
    ∃ out, Eval (liftChecker checker input output) (n + 1) a out ∧
      out.stacks = a.stacks ∧ out.regs = small.regs ∧
      (∀ k c, k ≤ n + 1 → Trace (compiled (liftChecker checker input output) 40 42) k
        (a.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max B A) := by
  let out := embedState id checkerPorts a small
  have ht := compiled_halt_trace hrun input output
  have hs := StructuredSpace.compiled_halt_stack_bound hrun input output hspace
  have hc := eval_call_from_state (compiled checker input output) id checkerPorts a
    Function.injective_id (Fin.castAdd_injective _ _) ht
  have hinitial : ProgramLinking.embedCfg id checkerPorts id none
      (a.withPC (none : Option (Fin (size checker + 1))))
      ((projectState id checkerPorts a).withPC (some (compiled checker input output).entry)) =
      a.withPC (some (compiled checker input output).entry) := by
    change (embedState id checkerPorts a (projectState id checkerPorts a)).withPC _ = _
    rw [embedState_project id checkerPorts a Function.injective_id (Fin.castAdd_injective _ _)]
    rfl
  have hlift := ProgramLinking.liftProgram_trace (compiled checker input output) id checkerPorts
    (a.withPC none) Function.injective_id (Fin.castAdd_injective _ _) ht
  rw [hinitial] at hlift
  have hlift' : Trace (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)
      (n + 1) (a.withPC (some (compiled checker input output).entry)) (out.withPC none) := by
    simpa [out, embedState, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC] using hlift
  have hliftspace := StructuredSpace.liftProgram_stack_bound
    (compiled checker input output) id checkerPorts (a.withPC none)
    Function.injective_id (Fin.castAdd_injective _ _) ht hs ha
  rw [hinitial] at hliftspace
  refine ⟨out, hc, ?_, ?_, ?_⟩
  · funext i
    by_cases hi : ∃ j, checkerPorts j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack id checkerPorts a small (Fin.castAdd_injective _ _) j).trans
        (congrFun hrestore j)
    · exact embedState_stack_frame id checkerPorts a small i hi
  · funext i
    exact embedState_register id checkerPorts a small Function.injective_id i
  · exact StructuredSpace.call_stack_bound
      (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)
      (compiled (liftChecker checker input output) 40 42)
      (siteAddress (liftChecker checker input output)) (exitAddress (liftChecker checker input output))
      (compiled_site (liftChecker checker input output) 40 42) hlift' hliftspace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- This composition lemma charges conversion and replacement locally, while
using the separately proved complete checker's space bound for its long scan.
The next two theorems instantiate this interface with the actual checkers. -/
theorem matrix_candidate_valid (ternary : Bool) (matrix : Fin 48)
    (checker : Cmd 16 40) (input output : Fin 40)
    (hm43 : matrix ≠ 43) (hm44 : matrix ≠ 44)
    (xs : List (Bool × Bool)) (word : List Bool) (hword : CodeCandidates.scalarFrames xs = word)
    (a : MatrixState) (A T B : ℕ) (P : Prop)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (hscratch : a.stacks 45 = [])
    (hvalid : xs.any (CodeCandidates.invalidDigit ternary) = false)
    (hchecker : ∀ prepared : MatrixState, prepared.stacks = Function.update a.stacks matrix word →
      ∃ n out, n ≤ T ∧ Eval (liftChecker checker input output) n prepared out ∧
        (out.regs 15 = true ↔ P) ∧ out.stacks = prepared.stacks ∧
        ∀ k c, k ≤ n → Trace (compiled (liftChecker checker input output) 40 42) k
          (prepared.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
          ∀ i, (c.stacks i).length ≤ B) :
    ∃ n out, n ≤ T + 2 * A + 73 * xs.length + 23 ∧
      Eval (matrixCandidate ternary matrix checker input output) n a out ∧
      (out.regs 15 = true ↔ P) ∧ out.stacks = Function.update a.stacks matrix word ∧
      (∀ k c, k ≤ n → Trace (compiled (matrixCandidate ternary matrix checker input output) 40 42) k
        (a.withPC (some (compiled (matrixCandidate ternary matrix checker input output) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * xs.length + 23) B) := by
  obtain ⟨b, hcopy, hflag, hb43, hb44, hbframe⟩ := copy_convert_eval ternary 40 43 44 45
    (by decide) (by decide) (by decide) (by decide) xs a hcurrent hinput hpayload hscratch
  have hbm : b.stacks matrix = a.stacks matrix := hbframe matrix hm43 hm44
  have hwlen : word.length = 5 * xs.length := by
    rw [← hword, CodeCandidates.scalarFrames_length]
  obtain ⟨prepared, hinstall, hp44, hpm, hpframe⟩ := installMatrix_eval 44 matrix (Ne.symm hm44)
    word b (by rw [hb44, hword])
  have hprepared : prepared.stacks = Function.update a.stacks matrix word := by
    funext i
    by_cases hi : i = matrix
    · subst i
      simpa using hpm
    · rw [Function.update_of_ne hi]
      by_cases h44 : i = 44
      · subst i
        exact hp44.trans hpayload.symm
      · rw [hpframe i h44 hi]
        by_cases h43 : i = 43
        · subst i
          exact hb43.trans hinput.symm
        · exact hbframe i h43 h44
  obtain ⟨n, out, hn, hcheck, haccept, hrestore, hcheckspace⟩ := hchecker prepared hprepared
  let bound := max (3 * A + 73 * xs.length + 23) B
  have hcopyspace : ∀ k c, k ≤ 58 * xs.length + 16 →
      Trace (compiled (copyConvertCommand ternary 40 43 44 45) 40 42) k
        (a.withPC (some (compiled (copyConvertCommand ternary 40 43 44 45) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := ha i
    exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * xs.length + 23).trans (Nat.le_max_left _ _)
  have hinstallspace : ∀ k c, k ≤ 2 * (b.stacks matrix).length + 3 * word.length + 6 →
      Trace (compiled (installMatrix 44 matrix) 40 42) k
        (b.withPC (some (compiled (installMatrix 44 matrix) 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
    have hb := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le (compiled_trace hcopy 40 42) i
    change (c.stacks i).length ≤ (b.stacks i).length + k at hg
    change (b.stacks i).length ≤ (a.stacks i).length + (58 * xs.length + 16) at hb
    have hi := ha i
    have hm := ha matrix
    rw [hbm, hwlen] at hk
    exact (by omega : (c.stacks i).length ≤ 3 * A + 73 * xs.length + 23).trans (Nat.le_max_left _ _)
  have hcheckspace' : ∀ k c, k ≤ n → Trace (compiled (liftChecker checker input output) 40 42) k
      (prepared.withPC (some (compiled (liftChecker checker input output) 40 42).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro k c hk ht i
    exact (hcheckspace k c hk ht i).trans (Nat.le_max_right _ _)
  have hsequence := StructuredSpace.sequence_stack_bound hinstall hcheck 40 42 hinstallspace hcheckspace'
    (compiled (.seq (installMatrix 44 matrix) (liftChecker checker input output)) 40 42)
    (siteAddress (.seq (installMatrix 44 matrix) (liftChecker checker input output)))
    (exitAddress (.seq (installMatrix 44 matrix) (liftChecker checker input output)))
    (compiled_site _ 40 42)
  let rejected : Cmd 16 48 := .seq (SubexpSetupStorage.clearCmd 44) (.base (.atom (.set 15 false)))
  let tail : Cmd 16 48 := .ite 4 rejected (.seq (installMatrix 44 matrix) (liftChecker checker input output))
  have htail : Eval tail ((2 * (b.stacks matrix).length + 3 * word.length + 6 + n) + 1) b out :=
    .ite_false (hflag.trans hvalid) (hinstall.seq hcheck)
  have htailspace := StructuredSpace.conditional_false_stack_bound (hflag.trans hvalid)
    (hinstall.seq hcheck) 40 42 hsequence (compiled tail 40 42) (siteAddress tail)
    (exitAddress tail) (compiled_site tail 40 42)
  refine ⟨(58 * xs.length + 16) + ((2 * (b.stacks matrix).length + 3 * word.length + 6 + n) + 1), out,
    ?_, hcopy.seq htail, haccept, hrestore.trans hprepared, ?_⟩
  · have hm := ha matrix
    rw [hbm, hwlen]
    omega
  · exact StructuredSpace.sequence_stack_bound hcopy htail 40 42 hcopyspace htailspace
      (compiled (matrixCandidate ternary matrix checker input output) 40 42)
      (siteAddress (matrixCandidate ternary matrix checker input output))
      (exitAddress (matrixCandidate ternary matrix checker input output))
      (compiled_site (matrixCandidate ternary matrix checker input output) 40 42)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

private theorem updated_matrix_bound (a prepared : MatrixState) (A : ℕ) (matrix : Fin 48)
    (word : List Bool) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hp : prepared.stacks = Function.update a.stacks matrix word) :
    ∀ i, (prepared.stacks i).length ≤ A + word.length := by
  intro i
  rw [hp]
  by_cases hi : i = matrix
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    exact (ha i).trans (Nat.le_add_right _ _)

theorem graph_matrix_candidate_valid_oai {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords s)
    (hvalid : xs.any (CodeCandidates.invalidDigit false) = false)
    (a : MatrixState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : ∀ i : Fin 29, a.stacks (Fin.castAdd 19 i) = [])
    (ht : a.stacks 30 = List.replicate D true) (hq : a.stacks 31 = qbits) (hDbits : a.stacks 32 = Dbits)
    (hr : a.stacks 33 = List.replicate r true)
    (hp : a.stacks 34 = []) (htmp : a.stacks 35 = []) (hcounter : a.stacks 36 = [])
    (hlatch : a.stacks 37 = []) (hscratch : a.stacks 38 = []) (hcopy : a.stacks 39 = [])
    (hcurrent : a.stacks 40 = CodeCandidates.tupleBits xs)
    (hinput : a.stacks 43 = []) (hpayload : a.stacks 44 = []) (houtertmp : a.stacks 45 = []) :
    ∃ n out, n ≤ matrixCheckTime A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
        (graphStreamBudget D r qbits.length Dbits.length) + 2 * A + 73 * (D * r) + 23 ∧
      Eval graphMatrixCandidate n a out ∧
      (out.regs 15 = true ↔ WalshExistence.Good q s) ∧
      out.stacks = Function.update a.stacks 29 (matrixFrames s) ∧
      (∀ k c, k ≤ n → Trace (compiled graphMatrixCandidate 40 42) k
        (a.withPC (some (compiled graphMatrixCandidate 40 42).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (3 * A + 73 * (D * r) + 23)
          (matrixCheckSpace A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length))) := by
  have hlen : xs.length = D * r := by simpa [CodeCandidates.matrixWords] using congrArg List.length hfields
  have hword := pair_matrix_frames_eq xs s hfields
  have hwordlen : (matrixFrames s).length = 5 * (D * r) := by
    rw [← hword, CodeCandidates.scalarFrames_length, hlen]
  have result := matrix_candidate_valid false 29 graphChecker 33 37
      (by decide) (by decide) xs (matrixFrames s) hword a A
      (matrixCheckTime A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length)
        (graphStreamBudget D r qbits.length Dbits.length))
      (matrixCheckSpace A (D * r) r (graphCallbackBudget D r qbits.length Dbits.length))
      (WalshExistence.Good q s) ha hcurrent hinput hpayload houtertmp hvalid
  rw [hlen] at result
  apply result
  intro prepared hprepared
  have hf (i : Fin 48) (hi : i ≠ 29) : prepared.stacks i = a.stacks i := by
    rw [hprepared, Function.update_of_ne hi]
  have hb : ∀ i, (prepared.stacks i).length ≤ A + 5 * (D * r) := by
    simpa [hwordlen] using updated_matrix_bound a prepared A 29 (matrixFrames s) ha hprepared
  have he' : GraphWorkEmpty (projectState id graphStreamStacks (projectState id checkerPorts prepared)) := by
    intro i
    apply (hf (Fin.castAdd 19 i) ?_).trans (he i)
    intro h
    have hv := congrArg Fin.val h
    change i.val = 29 at hv
    omega
  have hm : (projectState id checkerPorts prepared).stacks 29 = matrixFrames s := by
    change prepared.stacks 29 = _
    rw [hprepared, Function.update_self]
  obtain ⟨n, small, hrun, hn, haccept, hrestore, hspace⟩ := graph_checker_runs s q qbits Dbits hqv hDv
    (projectState id checkerPorts prepared) (A + 5 * (D * r)) (fun i => hb (checkerPorts i)) he' hm
    ((hf 30 (by decide)).trans ht) ((hf 31 (by decide)).trans hq) ((hf 32 (by decide)).trans hDbits)
    ((hf 33 (by decide)).trans hr) ((hf 34 (by decide)).trans hp) ((hf 35 (by decide)).trans htmp)
    ((hf 36 (by decide)).trans hcounter) ((hf 37 (by decide)).trans hlatch)
    ((hf 38 (by decide)).trans hscratch) ((hf 39 (by decide)).trans hcopy)
  obtain ⟨out, hcall, hout, hregs, hbound⟩ := lift_checker_resources graphChecker 33 37
    prepared small hrun hrestore hb hspace
  refine ⟨n + 1, out, ?_, hcall, ?_, hout, hbound⟩
  · unfold matrixCheckTime
    omega
  · simpa only [hregs] using haccept

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid_oai
