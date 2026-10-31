-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:47:03.922955+00:00
-- url     : https://prove2.me/submissions/21bd8bab-71f9-4f01-abaf-f297d46cc766

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_nodeSource_target
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeReadout_run_common
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
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

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

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

theorem returned_word {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (ho : ∀ q ∈ outs,Protected q.2)
    (hd : (outs.map Prod.snd).Nodup) (p : Fin s × Fin 768) (hp : p ∈ outs) :
    (returned reg hs ins outs a b).stacks p.2=b.stacks p.1 := by
  have hd' : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies hs outs,∀ z ∈ outputCopies hs outs,q.1≠z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work hs (ho z' hz') q'.1).symm
  exact (finish_value (workPorts hs) (outputCopies hs outs) _ hd' hsep
    (workPort hs p.1,p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    (protected_not_workPorts hs (ho p hp))).trans
      (embedState_stack reg (workPort hs) _ b (workPort_injective hs) p.1)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rowCountOutputs_protected : ∀ p∈rowCountOutputs,Protected p.2 := by simp [rowCountOutputs,Protected,temporary]

theorem cacheOutputs_protected : ∀ p∈cacheOutputs,Protected p.2 := by simp [cacheOutputs,Protected,temporary]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
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

theorem bootState_dimension (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 647=List.replicate records.length true := by
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ 647 (by decide)]
  · exact returned_word rowCountRegs (by decide) rowCountInputs rowCountOutputs _ _
      rowCountOutputs_protected (by decide) (2,647) (by simp [rowCountOutputs])
  · simp [cacheOutputs]


theorem bootState_positive (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 640=words.flatten :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (0,640) (by simp [cacheOutputs])


theorem bootState_negative (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 641=List.replicate (R.length*width.length) false :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (1,641) (by simp [cacheOutputs])


theorem bootState_denominator (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 642=LayoutProgram.IntegerCache.denominatorWord R.length :=
  returned_word cacheRegs (by decide) cacheInputs cacheOutputs _ _ cacheOutputs_protected
    (by decide) (2,642) (by simp [cacheOutputs])

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

theorem start_positive (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 640=words.flatten := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (640:Fin 768)≠665 by decide),
    Function.update_of_ne (show (640:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 640 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_positive _ _ _ _ _ _ _ _ _ _ _

theorem start_negative (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 641=List.replicate (s.R*s.width.length) false := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (641:Fin 768)≠665 by decide),
    Function.update_of_ne (show (641:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 641 (by decide) (by decide) (by decide) (by decide)]
  simpa [unary] using bootState_negative a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

theorem start_denominator (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (start s a ra rd rc words).stacks 642=s.power.1 := by
  unfold start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (642:Fin 768)≠665 by decide),
    Function.update_of_ne (show (642:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 642 (by decide) (by decide) (by decide) (by decide)]
  simpa [unary,Inputs.power] using bootState_denominator a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
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

/-- The native bootstrap dimension is generated from the actual plan stream. -/
theorem native_start_dimension (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (Native.start s a ra rd rc words).stacks 647=List.replicate s.records.length true := by
  unfold Native.start nodeStart
  simp only [tupleInitialized,Function.update_of_ne (show (647:Fin 768)≠665 by decide),
    Function.update_of_ne (show (647:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 647 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_dimension _ _ _ _ _ _ _ _ _ _ _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySourceSnapshot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A proof-only native source snapshot retains the actual readiness words.
It does not clear the running machine. The loader starts from the same native
input and generated cache, so all of its eighteen masters remain identical.
Unrelated scratch from earlier nodes is excluded from the source-local cap. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram LeafProgram.PreparedSource

/-- Both starts regenerate the cache and dimension masters from the same
input and cache witness; no old high-scratch length is assumed. -/
theorem snapshot_masters (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    SignatureHeadLoader.MasterFrame (Native.start s a ra rd rc words)
      (Native.start s (snapshot a) ra rd rc words) := by
  have low (i : Fin 768) (hi : i.val < 340) (hp : i ∈ retainedPorts) :
      (Native.start s (snapshot a) ra rd rc words).stacks i=
        (Native.start s a ra rd rc words).stacks i := by
    rw [Native.start_low _ _ _ _ _ _ _ hi,Native.start_low _ _ _ _ _ _ _ hi]
    exact snapshot_retained a i hp
  constructor
  intro i hi
  simp only [SignatureHeadLoader.masters,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact low _ (by decide) (by decide)
  · exact (Native.start_positive s _ ra rd rc words).trans
      (Native.start_positive s a ra rd rc words).symm
  · exact (Native.start_negative s _ ra rd rc words).trans
      (Native.start_negative s a ra rd rc words).symm
  · exact (Native.start_denominator s _ ra rd rc words).trans
      (Native.start_denominator s a ra rd rc words).symm
  · exact (QueryReadyConstruction.native_start_dimension s _ ra rd rc words).trans
      (QueryReadyConstruction.native_start_dimension s a ra rd rc words).symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

/-- Reassociating the proved concrete prefix with the fixed pair and finish
commands preserves its exact execution, rather than selecting another run. -/
theorem nodeBody_eval {np nq nf : ℕ} {a b c d : Data}
    (hp : Eval prepareNode np a b) (hq : Eval QueryStreamProgram.pairs nq b c)
    (hf : Eval QueryNodeFinish.command nf c d) :
    Eval QueryStreamProgram.nodeBody (np+nq+nf) a d := by
  cases hp with
  | seq hbegin hrest =>
    cases hrest with
    | seq hload hrest =>
      cases hrest with
      | seq hboot hsetup =>
        simpa only [QueryStreamProgram.nodeBody,Nat.add_assoc] using
          hbegin.seq (hload.seq (hboot.seq (hsetup.seq (hq.seq hf))))

/-- The polynomial preparation and readout budgets enter the transient cap;
the potentially exponential pair time does not. All three traces are the
actual segments of the same fixed node-body execution. -/
theorem nodeBody_prefix {np nq nf B D : ℕ} {a b c d : Data}
    (hp : Eval prepareNode np a b) (hq : Eval QueryStreamProgram.pairs nq b c)
    (hf : Eval QueryNodeFinish.command nf c d)
    (ha : WordBound B a) (hc : WordBound B c)
    (hspace : QueryExecution.PrefixBound QueryStreamProgram.pairs nq b D) :
    QueryExecution.PrefixBound QueryStreamProgram.nodeBody (np+nq+nf+1) a
      (max D (896*B+np+nf+1)) := by
  have hmass : stackBits a.stacks ≤ 896*B :=
    StreamResources.dataBits_le_mul (a.withPC (none : Option (Fin 1))) ha
  have growth {command : Code} {n : ℕ} {u v : Data} (he : Eval command n u v) :
      stackBits v.stacks ≤ stackBits u.stacks+n := by
    have htrace := compiled_trace (c:=command) (a:=u) (b:=v) he 838 838
    have hg := trace_dataBits (compiled command 838 838) htrace
    exact hg
  have localPrefix {command : Code} {n spent : ℕ} {u : Data}
      (hm : stackBits u.stacks ≤ 896*B+spent) (hn : spent+n ≤ np+nf+1) :
      QueryExecution.PrefixBound command n u (max D (896*B+np+nf+1)) := by
    constructor
    intro elapsed z ht hz i
    have hin : dataBits (u.withPC (some (compiled command 838 838).entry)) ≤ 896*B+spent := hm
    have hx := StructuredSpace.local_stack_bound (compiled command 838 838)
      (a:=u.withPC (some (compiled command 838 838).entry))
      (steps:=n) (initialBound:=896*B+spent) hin elapsed z ht hz i
    exact hx.trans ((by omega : 896*B+spent+n ≤ 896*B+np+nf+1).trans (Nat.le_max_right _ _))
  cases hp with
  | @seq _ _ n0 nr0 _ a1 _ h0 hr0 =>
    cases hr0 with
    | @seq _ _ n1 nr1 _ a2 _ h1 hr1 =>
      cases hr1 with
      | @seq _ _ n2 n3 _ a3 _ h2 h3 =>
        have hb1 := growth h0
        have hb2 := growth (h0.seq h1)
        have hb3 := growth (h0.seq (h1.seq h2))
        have p0 := localPrefix (command:=QueryAssembler.Nodes.beginNode) (n:=n0) (spent:=0) (u:=a)
          (by omega) (by omega)
        have p1 := localPrefix (command:=NativeLayoutLoad.command) (n:=n1) (spent:=n0) (u:=a1)
          (by omega) (by omega)
        have p2 := localPrefix (command:=QueryStreamProgram.bootstrapNode) (n:=n2) (spent:=n0+n1) (u:=a2)
          (by omega) (by omega)
        have p3 := localPrefix (command:=PairNativeSetup.setupCaller) (n:=n3) (spent:=n0+n1+n2) (u:=a3)
          (by omega) (by omega)
        have hend : stackBits c.stacks ≤ 896*B :=
          StreamResources.dataBits_le_mul (c.withPC (none : Option (Fin 1))) hc
        have pf := localPrefix (command:=QueryNodeFinish.command) (n:=nf) (spent:=0) (u:=c)
          (by omega) (by omega)
        have pq := hspace.mono (Nat.le_max_left D (896*B+(n0+(n1+(n2+n3)))+nf+1))
        have hprefix := QueryExecution.prefix_seq h0 (h1.seq (h2.seq (h3.seq (hq.seq hf)))) p0
          (QueryExecution.prefix_seq h1 (h2.seq (h3.seq (hq.seq hf))) p1
            (QueryExecution.prefix_seq h2 (h3.seq (hq.seq hf)) p2
              (QueryExecution.prefix_seq h3 (hq.seq hf) p3 (QueryExecution.prefix_seq hq hf pq pf))))
        have he := nodeBody_eval (h0.seq (h1.seq (h2.seq h3))) hq hf
        constructor
        apply StructuredSpace.compiled_halt_stack_bound he 838 838
        simpa only [QueryStreamProgram.nodeBody,Nat.add_assoc] using hprefix.bound

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

/-- Every static node word also has an exact frame through the actual pair loop. -/
theorem framePorts_pair (i : Fin 896) (hi : i ∈ framePorts) :
    i ∈ QueryPairEvaluation.framePorts := by
  simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- Readout changes the node index and coefficient stream, preserving the
complete static context used by the next node and final reconstruction. -/
theorem framePorts_finish (i : Fin 896) (hi : i ∈ framePorts) (h307 : i ≠ 307) (h863 : i ≠ 863) :
    i ∉ QueryNodeFinish.touchedPorts := by
  simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact False.elim (h307 rfl) | exact False.elim (h863 rfl) | decide

/-- Complete the very node prefix already executed by `prepare_native_run`.
The pair traversal, tuple evaluator and coefficient readout are the fixed
proved programs. Their retained endpoint cap is shared, and pair running time
never becomes a space estimate. The signed value is subsequently identified
with the shifted source target by the actual source-data lemmas. -/
theorem finish_prepared_node (s : SignatureTupleSource.ProducedSource)
    {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (a b : Data) (np index : ℕ) (remaining : List (List Bool))
    (hp : Eval prepareNode np a b)
    (ha : WordBound F a) (hb : WordBound F b)
    (hcommon : QueryReadyConstruction.CommonReady q s.input.node H high M b)
    (hzero : QueryPairCommit.NodeAccumulatorMeaning q 0 b)
    (hmasters : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b))
    (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
    (hmask : b.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : b.stacks 649=unary s.base)
    (hdepth : b.stacks 832=List.replicate (s.input.n-H.card) true)
    (hbudget : b.stacks 833=List.replicate q.J true)
    (houter : b.stacks 834=[]) (hinner : b.stacks 835=[])
    (hcursor : b.stacks 301=Encoding.encodeList id remaining)
    (hindex : b.stacks 307=List.replicate index true)
    (hout : (b.stacks 863).length+q.J*(d*baseWidth 3 q.p.t) ≤ F)
    (hnext : index+1 ≤ F) :
    ∃ steps e, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 q.p.t)) d),
      Eval QueryStreamProgram.nodeBody steps a e ∧
      codes.length=q.J ∧
      codes.map q.p.ops.decode=List.ofFn
        (∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
          (-1)^(pair.1.card-pair.2.card)*
            QueryPairEvaluation.pairValue s q H high owner head facts pair.1 pair.2).coeff ∧
      e.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      e.stacks 301=Encoding.encodeList id remaining ∧
      e.stacks 307=List.replicate (index+1) true ∧
      e.regs 37= !remaining.isEmpty ∧ e.regs 38=true ∧ e.stacks 89=[] ∧
      (∀ i ∈ framePorts,i ≠ 307 → i ≠ 863 → e.stacks i=a.stacks i) ∧
      WordBound F e ∧
      steps ≤ np+DifferencePairsProgram.cost
        (QueryPairEvaluation.callbackBudget s q (s.input.n-H.card) F S Z B height)
        (s.input.n-H.card) q.J+
        QueryNodeFinish.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F ∧
      Trace (compiled QueryStreamProgram.nodeBody 838 838) (steps+1)
        (a.withPC (some (compiled QueryStreamProgram.nodeBody 838 838).entry)) (e.withPC none) ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
        (max (max (QueryPairEvaluation.callbackSpace s q (s.input.n-H.card) F B) (896*F+13))
          (896*F+np+QueryNodeFinish.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+1)) := by
  have hi : QueryPairEvaluation.Invariant q s.input.node H high M F s b 0 b :=
    ⟨hcommon,hzero,fun i _=>hb i,hmasters,fun _ _=>rfl⟩
  obtain ⟨nq,c,hq,_htrace,hI,_hcontrols,hc,hqt,hqp⟩ :=
    QueryPairEvaluation.run s q H high owner head facts caps cap hheads b 0 hi
      hmask haddress hb hdepth hbudget houter hinner
  have h301 : c.stacks 301=Encoding.encodeList id remaining :=
    (hI.frame 301 (by decide)).trans hcursor
  have h307 : c.stacks 307=List.replicate index true :=
    (hI.frame 307 (by decide)).trans hindex
  have h863 : c.stacks 863=b.stacks 863 := hI.frame 863 (by decide)
  have hcOut : (c.stacks 863).length+q.J*(d*baseWidth 3 q.p.t) ≤ F := by
    rw [h863]
    exact hout
  obtain ⟨nf,e,codes,hf,hlen,hvalue,hout',_h78,_h850,_h862,hscratch,hindex',hguard,hpeek,
    hfframe,hebound,hft,_hftrace,_hfspace⟩ :=
    QueryNodeReadout.run_common q s.input.node H high M F index c hI.common _ hI.accumulator
      remaining h301 h307 hc hcOut hnext
  have hall := nodeBody_eval hp hq hf
  have hpairs : QueryExecution.PrefixBound QueryStreamProgram.pairs nq b
      (max (QueryPairEvaluation.callbackSpace s q (s.input.n-H.card) F B) (896*F+13)) :=
    ⟨fun elapsed cfg ht hz i => hqp elapsed cfg (by omega) hz i⟩
  have hpref := nodeBody_prefix hp hq hf ha hc hpairs
  refine ⟨np+nq+nf,e,codes,hall,hlen,?_,?_,?_,hindex',hguard,hpeek,
    hscratch 89 (by decide),?_,hebound,?_,compiled_halt_trace hall 838 838,?_⟩
  · simpa only [zero_add] using hvalue
  · rw [hout',h863,hframe 863 (by decide)]
  · exact (hfframe 301 (by decide)).trans h301
  · intro i him h307' h863'
    exact (hfframe i (framePorts_finish i him h307' h863')).trans
      ((hI.frame i (framePorts_pair i him)).trans (hframe i him))
  · omega
  · apply hpref.mono
    exact max_le_max (Nat.le_refl _) (by omega)


section AddressedSource
variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
variable (a : Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)

local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

/-- Only the eighteen-master reference changes to the restricted source.
The physical caller and its full query frame stay exactly the actual states. -/
theorem nodeSource_masters (b : Data)
    (hm : SignatureHeadLoader.MasterFrame
      (Native.start native (sourceSnapshot a bits remaining) ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b)) :
    SignatureHeadLoader.MasterFrame (src).masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  exact (hm.stored i hi).trans
    ((QuerySourceSnapshot.snapshot_masters native (sourceSnapshot a bits remaining)
      ra rd rc words).stored i hi).symm

section FactorRun
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (produced : LeafRingSetupProgram.Produced m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3^(m.val 34)) (hv : query.Valid) (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e produced
  hfield query hv hJ source hsource
local notation "H" => HighMarkedFrontend.highSet query
local notation "sourceOwner" => ProducedQueryRank.owner (LeafProgram.Query.packingProblem query k hg) ∘
  Fin.cast (Native.Inputs.plans_length native)
local notation "sourceHead" => (fun t v => ProducedQueryRank.words
  (LeafProgram.Query.packingProblem query k hg) first tail (Sum.inl v) t)
local notation "sourceFacts" => nodeSource_facts query k hg first tail node a bits remaining A
  hbank hparked ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource


include hfield source hsource in
/-- Finish the actual native node with its own bounded source and cache.
All semantic source alignment is instantiated here; the numerical data bounds
are supplied by the separate concrete source-bound construction. -/
theorem nodeSource_run_oai (high : H → Bool) (F S Z T width height : ℕ)
    (caps : QueryVisitorHead.HeadBounds (src).input spec A F S Z T A width)
    (cap : SignatureTupleComplete.RetainedCap src F)
    (hheads : ∀ depth<(native).r,(src).headSize depth ≤ height)
    (b : Data) (np : ℕ) (hp : Eval prepareNode np a b)
    (ha : WordBound F a) (hb : WordBound F b)
    (hcommon : QueryReadyConstruction.CommonReady spec node H high A b)
    (hzero : QueryPairCommit.NodeAccumulatorMeaning spec 0 b)
    (hmasters : SignatureHeadLoader.MasterFrame
      (Native.start native (sourceSnapshot a bits remaining) ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b))
    (hframe : ∀ i ∈ framePorts,b.stacks i=a.stacks i)
    (hmask : b.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : b.stacks 649=unary (src).base)
    (hdepth : b.stacks 832=List.replicate ((native).n-(H).card) true)
    (hbudget : b.stacks 833=List.replicate (spec).J true)
    (houter : b.stacks 834=[]) (hinner : b.stacks 835=[])
    (hcursor : b.stacks 301=Encoding.encodeList id remaining)
    (hout : (b.stacks 863).length+(spec).J*((m.val 34)*baseWidth 3 (spec).p.t) ≤ F)
    (hnext : node.val+1 ≤ F) :
    ∃ steps z, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 (spec).p.t)) (m.val 34)),
      Eval QueryStreamProgram.nodeBody steps a z ∧
      codes.length=(spec).J ∧
      codes.map (spec).p.ops.decode=List.ofFn
        (Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
          (Polynomial.X+Polynomial.C ((spec).p.ops.decode (spec).theta)))).coeff ∧
      z.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      z.stacks 301=Encoding.encodeList id remaining ∧
      z.stacks 307=List.replicate (node.val+1) true ∧
      z.regs 37= !remaining.isEmpty ∧ z.regs 38=true ∧ z.stacks 89=[] ∧
      (∀ i ∈ framePorts,i ≠ 307 → i ≠ 863 → z.stacks i=a.stacks i) ∧
      WordBound F z ∧
      steps ≤ np+DifferencePairsProgram.cost
        (QueryPairEvaluation.callbackBudget src spec ((native).n-(H).card) F S Z T height)
        ((native).n-(H).card) (spec).J+
        QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t) (m.val 34) (spec).p.t (spec).J F ∧
      Trace (compiled QueryStreamProgram.nodeBody 838 838) (steps+1)
        (a.withPC (some (compiled QueryStreamProgram.nodeBody 838 838).entry)) (z.withPC none) ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodeBody (steps+1) a
        (max (max (QueryPairEvaluation.callbackSpace src spec ((native).n-(H).card) F T) (896*F+13))
          (896*F+np+QueryNodeFinish.budget (native).n (baseWidth 3 (spec).p.t)
            (m.val 34) (spec).p.t (spec).J F+1)) := by
  have hm := nodeSource_masters query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc b hmasters
  have hi : b.stacks 307=List.replicate node.val true :=
    (hframe 307 (by decide)).trans hbank.node
  have hr := finish_prepared_node src spec H high sourceOwner sourceHead sourceFacts caps cap
    hheads a b np node.val remaining hp ha hb hcommon hzero hm hframe hmask haddress
    hdepth hbudget houter hinner hcursor hi hout hnext
  have htarget := nodeSource_target query k hg first tail node a bits remaining A
    hbank hparked ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource high
  obtain ⟨steps,z,codes,he,hlen,hcodes,hrest⟩ := hr
  exact ⟨steps,z,codes,he,hlen,hcodes.trans
    (congrArg (fun value : Truncated ((spec).p.model.O (spec).p.t) (spec).J =>
      List.ofFn value.coeff) htarget),hrest⟩

end FactorRun

end AddressedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run_oai
