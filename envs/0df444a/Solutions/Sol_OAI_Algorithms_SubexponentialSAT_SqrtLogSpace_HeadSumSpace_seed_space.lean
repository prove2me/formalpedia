-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.seed_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:49:28.068289+00:00
-- url     : https://prove2.me/submissions/628beeba-afe4-47f2-9547-31618778f530

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CopySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every-prefix storage of the actual preserving copy table. Empty destination
and temporary stacks permit the original per-stack envelope to be reused. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace

open BitProgram

private theorem copyWeight_step {r s : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8}
    (hstep : step (StackRoutines.copyProgram src dst tmp value present) a = some b) :
    copyWeight src dst tmp present b ≤ copyWeight src dst tmp present a := by
  cases hpc : a.pc with
  | none => simp [step, hpc] at hstep
  | some pc =>
      simp only [step, hpc, Option.map, Option.some.injEq] at hstep
      rw [← hstep]
      fin_cases pc
      · cases hx : a.stacks src <;>
          simp [copyWeight, execInstr, hpc, hx, readRegs, hsd.symm, hst.symm]
      · cases hr : a.regs present <;>
          simp [copyWeight, execInstr, hpc, hr]
      · simp [copyWeight, execInstr, hpc, hst, htd.symm]
        omega
      · cases hx : a.stacks tmp <;>
          simp [copyWeight, execInstr, hpc, hx, readRegs, hst, htd.symm]
      · cases hr : a.regs present <;>
          simp [copyWeight, execInstr, hpc, hr]
      · simp [copyWeight, execInstr, hpc, hsd.symm, hst.symm]
        omega
      · simp [copyWeight, execInstr, hpc, hsd, htd]
      · simp [copyWeight, execInstr, hpc]

private theorem copyWeight_trace {r s steps : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8}
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    copyWeight src dst tmp present b ≤ copyWeight src dst tmp present a := by
  induction ht with
  | refl => exact le_rfl
  | cons hs _ ih => exact ih.trans (copyWeight_step src dst tmp value present hsd hst htd hs)

theorem copyProgram_frame {r s steps : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) {a b : Cfg r s 8}
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b)
    (i : Fin s) (his : i ≠ src) (hid : i ≠ dst) (hit : i ≠ tmp) :
    b.stacks i = a.stacks i := by
  have hsingle {a b : Cfg r s 8}
      (hs : step (StackRoutines.copyProgram src dst tmp value present) a = some b) :
      b.stacks i = a.stacks i := by
    cases hpc : a.pc with
    | none => simp [step, hpc] at hs
    | some pc =>
        simp only [step, hpc, Option.map, Option.some.injEq] at hs
        rw [← hs]
        fin_cases pc <;> simp [execInstr, his, hid, hit]
  induction ht with
  | refl => rfl
  | cons hs _ ih => exact ih.trans (hsingle hs)

private theorem ports_le_copyWeight {r s : ℕ} (src dst tmp : Fin s) (present : Fin r)
    (a : Cfg r s 8) :
    (a.stacks src).length ≤ copyWeight src dst tmp present a ∧
    (a.stacks dst).length ≤ copyWeight src dst tmp present a ∧
    (a.stacks tmp).length ≤ copyWeight src dst tmp present a := by
  unfold copyWeight
  cases a.pc with
  | none => dsimp; omega
  | some pc => dsimp; split_ifs <;> omega

/-- Exact local copying never exceeds the source's original word length;
every off-port caller word retains its own independent bound. -/
theorem copyProgram_stack_bound {r s steps frameBound : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8} (hentry : a.pc = some 0)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = [])
    (hframe : ∀ i, i ≠ src → i ≠ dst → i ≠ tmp → (a.stacks i).length ≤ frameBound)
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ max (a.stacks src).length frameBound := by
  have hweight : copyWeight src dst tmp present b ≤ (a.stacks src).length := by
    have h := copyWeight_trace src dst tmp value present hsd hst htd ht
    simpa [copyWeight, hentry, hdst, htmp] using h
  obtain ⟨hsrc, hdst', htmp'⟩ := ports_le_copyWeight src dst tmp present b
  intro i
  by_cases hi : i = src
  · subst i
    exact (hsrc.trans hweight).trans (Nat.le_max_left _ _)
  by_cases hd : i = dst
  · subst i
    exact (hdst'.trans hweight).trans (Nat.le_max_left _ _)
  by_cases hw : i = tmp
  · subst i
    exact (htmp'.trans hweight).trans (Nat.le_max_left _ _)
  rw [copyProgram_frame src dst tmp value present ht i hi hd hw]
  exact (hframe i hi hd hw).trans (Nat.le_max_right _ _)

theorem copyProgram_no_growth {r s steps bound : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8} (hentry : a.pc = some 0)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = [])
    (ha : ∀ i, (a.stacks i).length ≤ bound)
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ bound := by
  intro i
  exact (copyProgram_stack_bound src dst tmp value present hsd hst htd hentry hdst htmp
    (fun j _ _ _ => ha j) ht i).trans (max_le (ha src) le_rfl)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

private theorem powerTwo_scan (word output : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 2)
      (counterCfg 2 bit present flag word output)
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ output)) := by
  induction word generalizing output bit present with
  | nil =>
      exact .cons (b := counterCfg 3 false false flag [] output)
        (by simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  | cons b word ih =>
      have h := Computation.Trace.cons
        (show step powerTwoProgram (counterCfg 2 bit present flag (b :: word) output) =
          some (counterCfg 3 b true flag word output) by
            simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (Computation.Trace.cons
          (show step powerTwoProgram (counterCfg 3 b true flag word output) =
            some (counterCfg 4 b true flag word output) by
              simp [step, powerTwoProgram, counterCfg, execInstr])
          (Computation.Trace.cons
            (show step powerTwoProgram (counterCfg 4 b true flag word output) =
              some (counterCfg 5 false true flag word output) by
                simp [step, powerTwoProgram, counterCfg, execInstr])
            (Computation.Trace.cons
              (show step powerTwoProgram (counterCfg 5 false true flag word output) =
                some (counterCfg 2 false true flag word (false :: output)) by
                  simp [step, powerTwoProgram, counterCfg, execInstr])
              (ih (false :: output) false true))))
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      simp [List.replicate_succ', List.append_assoc]

theorem powerTwo_trace (word : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 5)
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry))
      ((localData false false flag []
        (List.replicate word.length false ++ [true])).withPC none) := by
  have hstart : Trace powerTwoProgram 2 (counterCfg 0 bit present flag word [])
      (counterCfg 2 true present flag word [true]) :=
    .cons (b := counterCfg 1 true present flag word [])
      (by simp [step, powerTwoProgram, counterCfg, execInstr])
      (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  have hend : Trace powerTwoProgram 1
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ [true]))
      ((localData false false flag [] (List.replicate word.length false ++ [true])).withPC none) :=
    .cons (by simp [step, powerTwoProgram, counterCfg, execInstr, localData,
      StructuredProgram.State.withPC]) (.refl _)
  have h := (hstart.trans (powerTwo_scan word [true] true present flag)).trans hend
  have ht : 2 + (4 * word.length + 2) + 1 = 4 * word.length + 5 := by omega
  rw [ht] at h
  simpa [localData, StructuredProgram.State.withPC, counterCfg, powerTwoProgram] using h

/-- Every prefix of fuel construction has linear storage, including scratch. -/
theorem powerTwo_prefix_stack_bound (word : List Bool) (bit present flag : Bool)
    {steps : ℕ} {intermediate : Cfg 3 2 7} (hle : steps ≤ 4 * word.length + 5)
    (htrace : Trace powerTwoProgram steps
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry)) intermediate)
    (i : Fin 2) : (intermediate.stacks i).length ≤ 5 * word.length + 5 := by
  have hs : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  have hg := trace_dataBits powerTwoProgram htrace
  have hinit : dataBits
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry)) = word.length := by
    simp [dataBits, stackBits, localData,
      counterStacks, Fin.sum_univ_two]
  rw [hinit] at hg
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem copy_eval (d : Data) (src dst : Fin 896)
    (hsd : src≠dst) (hst : src≠31) (htd : (31:Fin 896)≠dst) (ht : d.stacks 31=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copyState d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 31 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

theorem clear_eval (d : Data) (src : Fin 896) :
    Eval (clear src) (2*(d.stacks src).length+3) d (clearState d src) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram


theorem seq_space {c e : Code} {n m B : ℕ} {a b d : Data}
    (hc : Eval c n a b) (he : Eval e m b d)
    (hcb : (∀ q z, q ≤ n → Trace (compiled c 860 860) q
      (a.withPC (some (compiled c 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) (heb : (∀ q z, q ≤ m → Trace (compiled e 860 860) q
      (b.withPC (some (compiled e 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) :
    (∀ q z, q ≤ (n+m) → Trace (compiled (.seq c e) 860 860) q
      (a.withPC (some (compiled (.seq c e) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) :=
  StructuredSpace.sequence_stack_bound hc he 860 860 hcb heb
    (compiled (.seq c e) 860 860) (siteAddress (.seq c e)) (exitAddress (.seq c e))
    (compiled_site (.seq c e) 860 860)

theorem copy_space {n B : ℕ} {a b : Data} (src dst : Fin 896)
    (he : Eval (copy src dst) n a b) (hsd : src≠dst) (hst : src≠31)
    (htd : (31:Fin 896)≠dst) (hd : a.stacks dst=[]) (ht : a.stacks 31=[])
    (ha : ∀ i, (a.stacks i).length≤B) : (∀ q z, q ≤ n → Trace (compiled (copy src dst) 860 860) q
      (a.withPC (some (compiled (copy src dst) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _
      (compiled_site (copy src dst) 860 860) tr
    intro q z _ hq
    exact CopySpace.copyProgram_no_growth src dst 31 0 1 hsd hst htd rfl hd ht ha hq

theorem clear_space {n B : ℕ} {a b : Data} (src : Fin 896)
    (he : Eval (clear src) n a b) (ha : ∀ i, (a.stacks i).length≤B) :
    (∀ q z, q ≤ n → Trace (compiled (clear src) 860 860) q
      (a.withPC (some (compiled (clear src) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _
      (compiled_site (clear src) 860 860) tr
    intro q z _ hq i
    exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le src 0 1 hq i).trans (ha i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

theorem power_eval (d : Data) (hf : d.stacks 860 = []) :
    Eval power (4 * (d.stacks 861).length + 5) d (powerResult d) := by
  have hr : Function.Injective powerRegisters := Fin.castAdd_injective _ _
  have hs : Function.Injective powerStacks := by decide
  have hp : projectState powerRegisters powerStacks d =
      CounterForPrograms.localData (d.regs 0) (d.regs 1) (d.regs 2)
        (d.stacks 861) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [powerStacks, counterStacks, hf]
  have ht := Counters.powerTwo_trace (d.stacks 861) (d.regs 0) (d.regs 1) (d.regs 2)
  rw [← hp] at ht
  exact eval_call_from_state Counters.powerTwoProgram powerRegisters powerStacks d hr hs ht

open HeadEvaluationProgram.StagedGate (copy copyState copy_eval clear clearState clear_eval)


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Sharp storage bounds for binary head-assignment controllers. Only the
counter's retained word length enters the local controller budget; every other
caller stack retains the same envelope throughout arbitrarily many visits. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

private theorem local_call_space {R S labels steps bound : ℕ} (p : Ports R S)
    (program : Program 3 2 labels) (a : State R S) (b : State 3 2)
    (hs : a.stacks p.scratch = [])
    (hrun : Trace program steps
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry))
      (b.withPC none))
    (hlocal : ∀ q z, q ≤ steps → Trace program q
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry)) z →
      ∀ i, (z.stacks i).length ≤ bound)
    (hframe : ∀ i, (a.stacks i).length ≤ bound) :
    let command := Cmd.call (ProgramLinking.liftProgram program p.register (stackPorts p))
    ∀ q z, q ≤ steps → Trace (compiled command p.counter p.counter) q
      (a.withPC (some (compiled command p.counter p.counter).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  dsimp only
  have hstart : install p a (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) [] = a := by
    rw [← hs]
    exact install_self p a
  have he := eval_call_lifted program p.register (stackPorts p) a
    p.register.injective (stackPorts p).injective hrun
  change Eval (.call (ProgramLinking.liftProgram program p.register (stackPorts p))) steps
    (install p a (a.regs (p.register 0)) (a.regs (p.register 1))
      (a.regs (p.register 2)) (a.stacks p.counter) [])
    (embedState p.register (stackPorts p) a b) at he
  rw [hstart] at he
  have hglobal := StructuredSpace.liftProgram_stack_bound program p.register (stackPorts p)
    (a.withPC none) p.register.injective (stackPorts p).injective hrun hlocal hframe
  have hinit : ProgramLinking.embedCfg p.register (stackPorts p) id none (a.withPC none)
      ((localData (a.regs (p.register 0)) (a.regs (p.register 1))
        (a.regs (p.register 2)) (a.stacks p.counter) []).withPC (some program.entry)) =
      a.withPC (some (ProgramLinking.liftProgram program p.register (stackPorts p)).entry) := by
    change (install p a _ _ _ _ []).withPC _ = _
    rw [hstart]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call prog ht =>
      exact StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (.call (ProgramLinking.liftProgram program p.register (stackPorts p)))
          p.counter p.counter) ht hglobal


/-- Constructing exponential fuel scans its linear-width witness and retains
one unchanged caller envelope. -/
theorem seed_power_space (a : HeadSumProgram.Data) (bound : ℕ)
    (hf : a.stacks 860 = []) (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hbudget : 5 * (a.stacks 861).length + 5 ≤ bound) :
    ∀ q z, q ≤ 4 * (a.stacks 861).length + 5 →
      Trace (compiled HeadSumProgram.power 860 860) q
        (a.withPC (some (compiled HeadSumProgram.power 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  let p : Ports 40 896 :=
    { register := ⟨HeadSumProgram.powerRegisters, Fin.castAdd_injective 3 37⟩
      counter := 861
      scratch := 860
      counter_ne_scratch := by decide }
  have hp : (stackPorts p : Fin 2 → Fin 896) = HeadSumProgram.powerStacks := by
    first | done | (funext i; fin_cases i <;> rfl)
  have hlocal : ∀ q z, q ≤ 4 * (a.stacks 861).length + 5 →
      Trace Counters.powerTwoProgram q
        ((localData (a.regs 0) (a.regs 1) (a.regs 2) (a.stacks 861) []).withPC
          (some Counters.powerTwoProgram.entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
    intro q z hq hz j
    exact (Counters.powerTwo_prefix_stack_bound (a.stacks 861) _ _ _ hq hz j).trans hbudget
  have whole := local_call_space p Counters.powerTwoProgram a _ hf
    (Counters.powerTwo_trace (a.stacks 861) (a.regs 0) (a.regs 1) (a.regs 2))
    hlocal hframe
  unfold HeadSumProgram.power
  rw [← hp]
  exact whole

open HeadEvaluationProgram.StagedGate

/-- The complete actual seed preserves one stack envelope, including an old
accumulator which is cleared by real instructions. -/
theorem seed_space_oai {a b : HeadSumProgram.Data} {steps bound : ℕ}
    (he : Eval HeadSumProgram.seed steps a b)
    (hcursor : a.stacks 859 = []) (hfuel : a.stacks 860 = [])
    (hscratch : a.stacks 861 = []) (htemp : a.stacks 31 = [])
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hbudget : 5 * (a.stacks 651).length + 5 ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled HeadSumProgram.seed 860 860) q
      (a.withPC (some (compiled HeadSumProgram.seed 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound := by
  let d1 := copyState a 651 859
  let d2 := copyState d1 651 861
  have h1 := copy_eval a 651 859 (by decide) (by decide) (by decide) htemp
  have s1 := copy_space 651 859 h1 (by decide) (by decide) (by decide)
    hcursor htemp hframe
  have b1 := s1 _ _ le_rfl (compiled_trace h1 860 860)
  have hd2 : d1.stacks 861 = [] := by
    simp [d1, copyState, StackRoutines.copyStacks, hscratch]
  have ht2 : d1.stacks 31 = [] := by
    simp [d1, copyState, StackRoutines.copyStacks, htemp]
  have h2 := copy_eval d1 651 861 (by decide) (by decide) (by decide) ht2
  have s2 := copy_space 651 861 h2 (by decide) (by decide) (by decide) hd2 ht2 b1
  have b2 := s2 _ _ le_rfl (compiled_trace h2 860 860)
  have hf3 : d2.stacks 860 = [] := by
    simp [d2, d1, copyState, StackRoutines.copyStacks, hfuel]
  have hw3 : d2.stacks 861 = a.stacks 651 := by
    simp [d2, d1, copyState, StackRoutines.copyStacks, hscratch]
  have h3 := HeadSumProgram.power_eval d2 hf3
  have s3 := seed_power_space d2 bound hf3 b2 (by simpa only [hw3] using hbudget)
  have b3 := s3 _ _ le_rfl (compiled_trace h3 860 860)
  have h4 := clear_eval (HeadSumProgram.powerResult d2) 853
  have s4 := clear_space 853 h4 b3
  have whole := seq_space h1 (h2.seq (h3.seq h4)) s1
    (seq_space h2 (h3.seq h4) s2 (seq_space h3 h4 s3 s4))
  have hsteps := StreamResources.eval_steps_eq 860 860 he (h1.seq (h2.seq (h3.seq h4)))
  simpa only [HeadSumProgram.seed, hsteps] using whole


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.seed_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.seed_space_oai
