-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:52:32.102419+00:00
-- url     : https://prove2.me/submissions/d1b178fb-891a-4760-b368-b163c948f765

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_program_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafOuterProgram_stage_bounded_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly_metadata_searches

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

theorem clearWorker_stack (a : Data) (i : Fin 768) :
    (workerCleared a).stacks (workerStack i) = [] :=
  embedState_stack id workerStack a LeafProgram.Cleanup.Wide.blank
    (Fin.castAdd_injective 768 128) i

theorem clearWorker_frame (a : Data) (i : Fin 896) (hi : 768 ≤ i.val) :
    (workerCleared a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  simp only [workerStack,Fin.val_castAdd] at hv
  omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

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

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupBoundSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured bounds for composition of the concrete setup phases

The predicates below retain actual executions. Polynomial coefficients and
degrees are chosen before the input size and the incoming machine state.
-/

namespace SubexponentialSAT.SubexpSetupBoundSpec

open BitProgram StructuredCalls SubexpSetupStorage Filter

theorem wordBound_mono {r s B C : ℕ} {a : State r s}
    (ha : WordBound B a) (hBC : B ≤ C) : WordBound C a :=
  fun i => (ha i).trans hBC

/-- A fixed stack gains at most one bit per actual instruction. -/
theorem eval_wordBound {r s B t : ℕ} {cmd : Cmd r s} {a b : State r s}
    (ha : WordBound B a) (he : Eval cmd t a b) : WordBound (B + t) b := by
  intro i
  have hg := BitProgram.trace_selectedStackBits (compiled cmd i i) {i}
    (compiled_trace he i i)
  have hi : (b.stacks i).length ≤ (a.stacks i).length + t := by
    simpa only [BitProgram.selectedStackBits, Finset.sum_singleton,
      StructuredProgram.State.withPC] using hg
  exact hi.trans (Nat.add_le_add_right (ha i) t)

end SubexponentialSAT.SubexpSetupBoundSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact composition and memory charging for fixed outer-leaf stages. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexpSetupStorage

theorem stageResult_empty {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (i : Fin 768) :
    (stageResult inputs outputs register stack a out).stacks (workerStack i) = [] :=
  clearWorker_stack _ i

theorem stageResult_frame {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (i : Fin 896) (hi : 768 ≤ i.val)
    (hinput : ∀ q ∈ inputs, q.2 ≠ i) (houtput : ∀ q ∈ outputs, q.2 ≠ i)
    (hstack : ∀ j, stack j ≠ i) :
    (stageResult inputs outputs register stack a out).stacks i = a.stacks i := by
  rw [stageResult,clearWorker_frame _ i hi,stageSaved,routes_frame _ _ _ houtput,
    stageReturned,embedState_stack_frame register stack (routesState inputs a) out i
      (by rintro ⟨j,hj⟩; exact hstack j hj),routes_frame _ _ _ hinput]

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCode.decidableIsCodeword _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.Subexp

theorem ternary_scalarWord (x : SparseCode.F3) :
    MatrixWordEncoding.word 3 x=[decide (x=1),decide (x=2)] := by
  rw [CodeSearchProgram.scalarWord_eq]
  have hw : SubexpEnumerationPayload.scalarWidth 3=2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem ternary_frames (xs : List SparseCode.F3) :
    CodeSearchProgram.scalarFrames xs=
      xs.flatMap (fun x => Cell.frame (decide (x=1)) (decide (x=2))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Encoding.frame (MatrixWordEncoding.word 3 x) ++ CodeSearchProgram.scalarFrames xs = _
    rw [ternary_scalarWord,ih]
    rfl

theorem ternary_frames_length (xs : List SparseCode.F3) :
    (CodeSearchProgram.scalarFrames xs).length=5*xs.length := by
  rw [ternary_frames]
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Cell.frame]; omega

theorem matrixWords_flatMap (rows : List (List (List Bool))) :
    MatrixVectorProgram.matrixWords rows=rows.flatMap MatrixProgramSupport.words := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simpa [MatrixVectorProgram.matrixWords] using congrArg (MatrixProgramSupport.words x++·) ih

theorem matrixFrames_rows {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) :
    CodeSearchProgram.matrixFrames Q=
      (List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).flatten := by
  rw [CodeSearchProgram.matrixFrames,matrixWords_flatMap]
  simp only [List.flatMap,CodeSearchProgram.scalarFrames,List.map_ofFn,Function.comp_def]

theorem ternary_matrixFrames_length {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3) :
    (CodeSearchProgram.matrixFrames Q).length=t*(5*D) := by
  rw [matrixFrames_rows]
  simp [List.length_flatten,Function.comp_def,ternary_frames_length]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators
open SubexponentialSAT.BinaryArithmetic

theorem binary_scalarWord (x : ZMod 2) :
    SubexponentialSAT.Subexp.MatrixWordEncoding.word 2 x=[decide (x=1),false] := by
  rw [CodeSearchProgram.scalarWord_eq]
  have hw : SubexpEnumerationPayload.scalarWidth 2=2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem vertexFrames {r : ℕ} (v : Cayley.Cube r) :
    CodeSearchProgram.scalarFrames (List.ofFn v)=Shift.frames (vertexBits v) := by
  simp only [CodeSearchProgram.scalarFrames,CodeSearchProgram.words_eq_flatMap,vertexBits,Shift.frames,List.flatMap,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [binary_scalarWord]
  rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem matrixFrames_shifts {r D : ℕ} (shifts : Fin D → Cayley.Cube r) :
    CodeSearchProgram.matrixFrames shifts=shiftRows (List.ofFn shifts) := by
  rw [matrixFrames_rows]
  simp only [shiftRows,List.flatMap,List.map_ofFn,Function.comp_def,vertexFrames]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem binary_matrixFrames_length {r D : ℕ} (shifts : Fin D → Cayley.Cube r) :
    (CodeSearchProgram.matrixFrames shifts).length=5*(D*r) := by
  rw [matrixFrames_shifts]
  simp [shiftRows,Shift.frames,Cell.frame,List.length_flatMap,Function.comp_def,
    vertexBits,List.sum_replicate,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

theorem cost_eq_explicit {r D t : ℕ} (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) :
    cost dword mword width shifts Q=
      explicitCost r D t width.length dword.length mword.length := by
  simp [cost,vertexCost,sideCost,rowCost,portWidth,initialStacks,inputState,
    binary_matrixFrames_length,ternary_matrixFrames_length,explicitCost,explicitRowCost]
  ring

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

theorem rowInputs_valid : ∀ p ∈ rowInputs, routeValid p := by
  intro p hp
  simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals unfold routeValid; decide

theorem rowOutputs_valid : ∀ p ∈ rowOutputs, routeValid p := by
  intro p hp
  simp only [rowOutputs,List.mem_singleton] at hp
  subst p
  unfold routeValid
  decide

private theorem single_saved {r s : ℕ} (inputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (source dest : Fin 896) (hd : 768 ≤ dest.val) :
    (stageResult inputs [(source,dest)] register stack a out).stacks dest =
      (stageReturned inputs register stack a out).stacks source := by
  rw [stageResult,clearWorker_frame _ dest hd]
  simp [stageSaved,routesState,routed]

theorem serializer_prepared {r D t : ℕ} (a : Data) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true) :
    projectState regs16 stacks64 (routesState rowInputs a) =
      CodeRowsProgram.inputState ((routesState rowInputs a).regs ∘ regs16)
        dword mword width shifts Q := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    have hz : a.stacks (stacks64 i) = [] := hw _ (by simp only [stacks64,Fin.val_castAdd]; omega)
    by_cases h3 : i=3
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h4 : i=4
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h5 : i=5
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h6 : i=6
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h7 : i=7
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h8 : i=8
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h9 : i=9
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h10 : i=10
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h11 : i=11
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    have v3 : i.val≠3 := fun h => h3 (Fin.ext h)
    have v4 : i.val≠4 := fun h => h4 (Fin.ext h)
    have v5 : i.val≠5 := fun h => h5 (Fin.ext h)
    have v6 : i.val≠6 := fun h => h6 (Fin.ext h)
    have v7 : i.val≠7 := fun h => h7 (Fin.ext h)
    have v8 : i.val≠8 := fun h => h8 (Fin.ext h)
    have v9 : i.val≠9 := fun h => h9 (Fin.ext h)
    have v10 : i.val≠10 := fun h => h10 (Fin.ext h)
    have v11 : i.val≠11 := fun h => h11 (Fin.ext h)
    have hf : ∀ p ∈ rowInputs, p.2≠stacks64 i := by
      intro p hp
      simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hv := congrArg Fin.val h <;> simp only [stacks64,Fin.val_castAdd] at hv <;> omega
    change (routesState rowInputs a).stacks (stacks64 i)=_
    rw [routes_frame rowInputs a (stacks64 i) hf,hz]
    simp only [h3,h4,h5,h6,h7,h8,h9,h10,h11,ite_false]

theorem serialize_eval {r D t m : ℕ} (a : Data) (W : ℕ) (hW : WordBound W a)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true)
    (hdv : BinaryArithmetic.toNat dword = D) (hmv : BinaryArithmetic.toNat mword = m)
    (hcap : 3*m ≤ 2^width.length) :
    ∃ steps b, Eval serialize steps a b ∧
      steps ≤ 10000*(W+CodeRowsProgram.cost dword mword width shifts Q+1) ∧
      b.stacks 777 = CodeRowsProgram.rowStream width.length m shifts Q ∧
      (∀ i : Fin 768, b.stacks (workerStack i) = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → b.stacks i = a.stacks i) := by
  have hp := serializer_prepared a dword mword width shifts Q hw hd hm hb hD ht hN hs hQ hr
  obtain ⟨rf,hrun⟩ := CodeRowsProgram.program_runsIn
    ((routesState rowInputs a).regs ∘ regs16) dword mword width shifts Q hdv hmv hcap
  rw [← hp] at hrun
  obtain ⟨steps,hsteps,he⟩ := stage_bounded_eval rowInputs rowOutputs
    CodeRowsProgram.program regs16 stacks64 (Fin.castAdd_injective 16 24)
    (Fin.castAdd_injective 64 832)
    (by intro i h; have hh := congrArg Fin.val h; simp [stacks64] at hh; omega)
    rowInputs_valid rowOutputs_valid (by decide) (by decide) a W hW (hw 767 (by decide))
    _ _ hrun
  let out := CodeRowsProgram.outputState (m:=m) rf dword mword width shifts Q
  refine ⟨steps,stageResult rowInputs rowOutputs regs16 stacks64 a out,he,hsteps,?_,
    stageResult_empty _ _ _ _ _ _,?_⟩
  · rw [show rowOutputs = [(12,777)] from rfl,single_saved _ _ _ _ _ _ _ (by decide)]
    have hh := embedState_stack regs16 stacks64 (routesState rowInputs a) out
      (Fin.castAdd_injective 64 832) 12
    simpa [stageReturned,stacks64,out,CodeRowsProgram.outputState] using hh
  · intro i hi h777
    apply stageResult_frame _ _ _ _ _ _ i hi
    · intro p hp
      simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hh := congrArg Fin.val h <;> simp only at hh <;> omega
    · intro p hp
      simp only [rowOutputs,List.mem_singleton] at hp
      subst p
      exact Ne.symm h777
    · intro j h
      have hh := congrArg Fin.val h
      simp only [stacks64,Fin.val_castAdd] at hh
      omega


/-- Serialization is an actual polynomial-time phase, including its routing
and complete lower-bank cleanup, so instruction growth also bounds its prefix
storage. The preceding searches never use this argument. -/
theorem serializer_trace_space {r D t m : ℕ} (a : Data) (W : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true)
    (hdv : BinaryArithmetic.toNat dword = D) (hmv : BinaryArithmetic.toNat mword = m)
    (hcount : BinaryArithmetic.toNat width = 3*m) :
    ∃ steps b, steps ≤ serializerTime r D t W dword mword width ∧
      Eval serialize steps a b ∧
      b.stacks 777 = CodeRowsProgram.rowStream width.length m shifts Q ∧
      WorkerEmpty b ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ W + serializerTime r D t W dword mword width) ∧
      ∀ k c, k ≤ steps → Trace (compiled serialize 784 788) k
        (a.withPC (some (compiled serialize 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ W + serializerTime r D t W dword mword width := by
  have hcap := (SubexpParameterProgram.value_lt_two_pow_length width).le
  rw [CounterPrograms.value_eq_toNat, hcount] at hcap
  obtain ⟨steps, b, he, htime, hout, hempty, hframe⟩ := serialize_eval a W ha
    dword mword width shifts Q hblank hd hm hb hD ht hN hs hQ hr hdv hmv hcap
  rw [CodeRowsProgram.cost_eq_explicit] at htime
  change steps ≤ serializerTime r D t W dword mword width at htime
  refine ⟨steps, b, htime, he, hout, hempty, hframe, ?_, ?_⟩
  · exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound ha he) (Nat.add_le_add_left htime W)
  · intro k c hk hc i
    have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le hc i
    change (c.stacks i).length ≤ (a.stacks i).length + k at hg
    have hi := ha i
    omega

/-- Concrete metadata words feed both searches and the serializer. The
serializer consumes exactly the matrices returned by those searches. -/
theorem afterMetadata_eval_oai {m occurrence A : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (a : Data) (he : WorkerEmpty a) (hmeta : Metadata m occurrence a)
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hmword : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hwidth : BinaryArithmetic.toNat (a.stacks 768) = 3*m) :
    ∃ (steps : ℕ) (out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ afterTime A m occurrence (a.stacks 800).length (a.stacks 801) (a.stacks 782) (a.stacks 768) ∧
      Eval afterMetadata steps a out ∧
      out.stacks 777 = CodeRowsProgram.rowStream (a.stacks 768).length m shifts Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      WorkerEmpty out ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → i ≠ 815 → i ≠ 816 →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ afterBoundary A m occurrence
        (a.stacks 801) (a.stacks 782) (a.stacks 768)) ∧
      ∀ k c, k ≤ steps → Trace (compiled afterMetadata 784 788) k
        (a.withPC (some (compiled afterMetadata 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ afterSpace A m occurrence (a.stacks 800).length
          (a.stacks 801) (a.stacks 782) (a.stacks 768) := by
  obtain ⟨ns, b, shifts, Q, hns, hes, hshifts, hQ, hgood, hdist, hbempty, hbf, hb, hbs⟩ :=
    metadata_searches hm hocc a he hmeta ha
  have bp (i : Fin 896) (hi : 768 ≤ i.val) (h815 : i ≠ 815) (h816 : i ≠ 816) :
      b.stacks i = a.stacks i := hbf i hi h815 h816
  have hu (j : Fin 7) : b.stacks (unaryMetadataPort j) =
      List.replicate (CodeParametersProgram.parameterValues m occurrence j) true := by
    rw [bp]
    · exact hmeta.unary j
    · simp only [unaryMetadataPort]; omega
    · intro h; have := congrArg Fin.val h; simp only [unaryMetadataPort] at this; have := j.isLt; omega
    · intro h; have := congrArg Fin.val h; simp only [unaryMetadataPort] at this; have := j.isLt; omega
  obtain ⟨nr, out, hnr, her, hout, hempty, hf, hbound, hspace⟩ :=
    serializer_trace_space b (NativeCode.searchBoundary A m occurrence) hb
      (a.stacks 801) (a.stacks 782) (a.stacks 768) shifts Q hbempty
      (bp 801 (by decide) (by decide) (by decide))
      (bp 782 (by decide) (by decide) (by decide))
      (bp 768 (by decide) (by decide) (by decide))
      (hu 0) (hu 1) (hu 6) hshifts hQ (hu 4) (hmeta.binary 0) hmword hwidth
  refine ⟨ns + nr, out, shifts, Q, Nat.add_le_add hns hnr, hes.seq her, hout,
    hgood, hdist, hempty, ?_, hbound, ?_⟩
  · intro i hi h777 h815 h816
    exact (hf i hi h777).trans (hbf i hi h815 h816)
  · exact StructuredSpace.sequence_stack_bound hes her 784 788
      (fun k c hk hc i => (hbs k c hk hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (hspace k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled afterMetadata 784 788) (siteAddress afterMetadata) (exitAddress afterMetadata)
      (compiled_site afterMetadata 784 788)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval_oai
