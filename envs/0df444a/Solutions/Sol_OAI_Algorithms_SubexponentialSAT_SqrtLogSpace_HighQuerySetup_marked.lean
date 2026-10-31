-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.marked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:31:19.589338+00:00
-- url     : https://prove2.me/submissions/ee4b2458-a941-436c-81b8-22a4f86a4d7e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighFrontendShadow_marked_denominator_empty
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_command_front_state
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_command_kept_frame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySetup_prepare_seed

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem fields_good : ∀ f∈fields, f.Good := by
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  fin_cases i <;> simp [Field.Good,field,localSource,destination]

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem clearPorts_mem (j : Fin 768) : j∈clearPorts ↔ 386 ≤ j.val ∧ j.val < 404 := by
  simp only [clearPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,rfl⟩; dsimp [bank]; have := i.isLt; omega
  · intro hj
    refine ⟨⟨j.val-386,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [bank]
    omega

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
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

theorem avoids_liftCommand_of_range {R S : ℕ} (H : Fin S → Prop)
    (c : Cmd r s) (input output : Fin s) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (h : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (liftCommand c input output register stack) :=
  avoids_call_lift_of_range H _ register stack h

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramOuterCarriedMono
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l : ℕ} {H K : Fin s → Prop}

theorem avoidsInstr_mono (sub : ∀ i, H i → K i) {c : Instr r s l}
    (h : AvoidsInstr K c) : AvoidsInstr H c := by
  cases c <;> simp only [AvoidsInstr] at * <;>
    first | trivial | exact fun hi => h (sub _ hi)

theorem avoidsProgram_mono (sub : ∀ i, H i → K i) {p : Program r s l}
    (h : AvoidsProgram K p) : AvoidsProgram H p :=
  fun q => avoidsInstr_mono sub (h q)

theorem avoidsAtom_mono (sub : ∀ i, H i → K i) {c : StructuredProgram.Atom r s}
    (h : AvoidsAtom K c) : AvoidsAtom H c := by
  cases c <;> simp only [AvoidsAtom] at * <;>
    first | trivial | exact fun hi => h (sub _ hi)

theorem avoidsBase_mono (sub : ∀ i, H i → K i) {c : StructuredProgram.Cmd r s}
    (h : AvoidsBase K c) : AvoidsBase H c := by
  induction c with
  | skip => trivial
  | atom a => exact avoidsAtom_mono sub h
  | seq a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | ite i a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | «while» i a ha => exact ha h

theorem avoidsCmd_mono (sub : ∀ i, H i → K i) {c : StructuredCalls.Cmd r s}
    (h : AvoidsCmd K c) : AvoidsCmd H c := by
  induction c with
  | base a => exact avoidsBase_mono sub h
  | call p => exact avoidsProgram_mono sub h
  | seq a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | ite i a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | «while» i a ha => exact ha h

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual frontend neither reads nor writes outer carried tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Replay
open LeafProgram.OuterCarried

private theorem visible (i : Fin 768) (hi : i.val < 320 ∨ 332 < i.val) : ¬ LeafProgram.OuterCarried.hidden i := by
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.mem_nil_iff,or_false]
  rintro (rfl|rfl|rfl) <;> norm_num at hi

private theorem block_visible (b n : ℕ) (h : b+n ≤ 768) (hb : 332 < b) (i : Fin n) :
    ¬ LeafProgram.OuterCarried.hidden (block b n h i) := by
  apply visible
  right
  dsimp [block]
  omega

private theorem copy_avoids (s d : Fin 768) (hs : ¬ LeafProgram.OuterCarried.hidden s) (hd : ¬ LeafProgram.OuterCarried.hidden d) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (copy s d) :=
  avoids_copyProgram LeafProgram.OuterCarried.hidden s d 679 0 1 hs hd (by decide)

private theorem copies_avoids (xs : List (Fin 768 × Fin 768))
    (h : ∀ p∈xs, ¬ LeafProgram.OuterCarried.hidden p.1 ∧ ¬ LeafProgram.OuterCarried.hidden p.2) : AvoidsCmd LeafProgram.OuterCarried.hidden (copies xs) := by
  induction xs with
  | nil => trivial
  | cons p ps ih => exact ⟨copy_avoids p.1 p.2 (h p (by simp)).1 (h p (by simp)).2,
      ih (fun q hq => h q (by simp [hq]))⟩

private theorem sequence_avoids (cs : List Code)
    (h : ∀ c∈cs, AvoidsCmd LeafProgram.OuterCarried.hidden c) : AvoidsCmd LeafProgram.OuterCarried.hidden (sequence cs) := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd]))⟩

private theorem load_avoids (dst : Fin 768) (bits : List Bool) (hd : ¬ LeafProgram.OuterCarried.hidden dst) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (loadBits dst bits) := by
  apply avoids_liftProgram
  apply avoids_compiled
  change AvoidsCmd LeafProgram.OuterCarried.hidden (ArithmeticExpressionSupport.pushWord dst bits)
  induction bits with
  | nil => trivial
  | cons b bs ih => exact ⟨ih,trivial,hd⟩

private theorem clear_avoids (ps : List (Fin 768)) (hp : ∀ p∈ps, ¬ LeafProgram.OuterCarried.hidden p) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (BankRoutines.clearCmd 679 (0 : Fin 40) 1 ps) := by
  induction ps with
  | nil => exact avoids_clearProgram LeafProgram.OuterCarried.hidden 679 0 1 (by decide)
  | cons p ps ih => exact ⟨avoids_clearProgram LeafProgram.OuterCarried.hidden p 0 1 (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))⟩

private theorem export_field_avoids (f : Exports.Field) (hf : f.Good) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.fieldCommand f) := by
  have hs : ¬ LeafProgram.OuterCarried.hidden f.src := visible _ (Or.inr (by have := hf.1; omega))
  have hd : ¬ LeafProgram.OuterCarried.hidden f.dst := visible _ (by rcases hf.2.2 with h|h; left; omega; right; omega)
  unfold Exports.fieldCommand
  split
  · apply avoids_liftCommand_of_range
    intro i
    unfold Exports.ports
    split
    · exact hs
    · split
      · exact hd
      · apply visible; right; dsimp; omega
  · exact avoids_copyProgram LeafProgram.OuterCarried.hidden f.src f.dst 679 0 1 hs hd (by decide)

private theorem export_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Exports.prepareCommand := by
  refine ⟨?_,?_,clear_avoids _ ?_⟩
  · apply avoids_liftCommand_of_range
    intro i
    apply visible
    right
    dsimp [Exports.bank]
    omega
  · change AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.command Exports.fields)
    have h (fs : List Exports.Field) (hf : ∀ f∈fs, f.Good) :
        AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.command fs) := by
      induction fs with
      | nil => trivial
      | cons f fs ih => exact ⟨export_field_avoids f (hf f (by simp)),
          ih (fun g hg => hf g (by simp [hg]))⟩
    exact h _ Exports.fields_good
  · intro p hp
    apply visible
    right
    have := (Exports.clearPorts_mem p).mp hp
    omega

private theorem binary_avoids (s d : Fin 768) (hs : ¬ LeafProgram.OuterCarried.hidden s) (hd : ¬ LeafProgram.OuterCarried.hidden d) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (binary s d) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> simp [binaryPorts,hs,hd]
  decide

/-- Syntactic avoidance includes peeks, so arbitrary carried words cannot affect time. -/
theorem frontend_avoids (k : ℕ) : AvoidsCmd LeafProgram.OuterCarried.hidden (frontend k) := by
  have hcount : AvoidsCmd LeafProgram.OuterCarried.hidden countHashes := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl)
    · exact copy_avoids _ _ (by decide) (by decide)
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hraw : AvoidsCmd LeafProgram.OuterCarried.hidden rawCommand := by
    refine ⟨sequence_avoids _ ?_,?_,copy_avoids _ _ (by decide) (by decide)⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro c (rfl|rfl|rfl)
      · apply copies_avoids
        simp [scopeCopies,LeafProgram.OuterCarried.hidden]
      · exact load_avoids _ _ (by decide)
      · simp [resetScopeRegs,setRegs,SubexpParameterProgram.atoms,AvoidsBase,AvoidsAtom]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 500 80 _ (by decide))
  have hhigh : AvoidsCmd LeafProgram.OuterCarried.hidden highCommand := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact copy_avoids _ _ (by decide) (by decide)
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 417 77 _ (by decide))
    · apply copies_avoids
      simp [highCopies,LeafProgram.OuterCarried.hidden]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 580 32 _ (by decide))
    · exact copy_avoids _ _ (by decide) (by decide)
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hmeasure : AvoidsCmd LeafProgram.OuterCarried.hidden measureCommand := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl|rfl|rfl|rfl|rfl)
    · apply copies_avoids
      simp [statsCopies,LeafProgram.OuterCarried.hidden]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 612 21 _ (by decide))
    · apply copies_avoids
      simp [arityCopies,LeafProgram.OuterCarried.hidden]
    · simp [arityRegisters,setRegs,SubexpParameterProgram.atoms,AvoidsBase,AvoidsAtom]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 633 12 _ (by decide))
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hnumeric : AvoidsCmd LeafProgram.OuterCarried.hidden (numericStage k) := by
    refine ⟨copies_avoids _ ?_,load_avoids _ _ (by decide),sequence_avoids _ ?_⟩
    · simp [LeafProgram.OuterCarried.hidden]
    · simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro c (rfl|rfl|rfl|rfl|rfl) <;> exact binary_avoids _ _ (by decide) (by decide)
  refine ⟨hcount,⟨hraw,hhigh,hmeasure,hnumeric,?_⟩,export_avoids,?_,?_,?_⟩
  · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 340 77 _ (by decide))
  · apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · refine ⟨copy_avoids _ _ (by decide) (by decide),?_⟩
    apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · apply clear_avoids
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact block_visible 417 262 _ (by decide) i

end Replay

/-- The concrete frontend does not read or write tapes 320, 322, or 332. -/
theorem frontend_avoids_outerCarried (k : ℕ) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (frontend k) := Replay.frontend_avoids k

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

open HashGreedyProgram.NativeRound

namespace Carried

open SqrtLog.ProgramTapeReplay

local notation "H" => (fun i : Fin 896 => i ∈ words)

private theorem SafeAvoids.call {l : Nat} {p : Program 40 896 l}
    (hp : AvoidsProgram H p) :
    SafeAvoids (.call p) :=
  ⟨hp⟩

private theorem LowerSafeAvoids.intro {c : Cmd 40 768}
    (hc : AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) c) : LowerSafeAvoids c :=
  ⟨hc⟩

private theorem LowerSafeAvoids.ofMono {K : Fin 768 → Prop} {c : Cmd 40 768}
    (sub : ∀ i, (H ∘ HighMarkedFrontend.stackMap) i → K i)
    (hc : AvoidsCmd K c) : LowerSafeAvoids c :=
  ⟨avoidsCmd_mono sub hc⟩

private theorem LowerSafeAvoids.seq {first second : Cmd 40 768}
    (hfirst : LowerSafeAvoids first) (hsecond : LowerSafeAvoids second) :
    LowerSafeAvoids (.seq first second) :=
  ⟨⟨hfirst.proof, hsecond.proof⟩⟩

private theorem LowerSafeAvoids.liftCall {c : Cmd 40 768}
    (hc : LowerSafeAvoids c) (input output : Fin 768) :
    SafeAvoids (.call (ProgramLinking.liftProgram (compiled c input output)
      id HighMarkedFrontend.stackMap)) :=
  SafeAvoids.call (avoids_liftProgram H _ id HighMarkedFrontend.stackMap
    (avoids_compiled _ c hc.proof input output))

private theorem lower_subset (i : Fin 768) (hi : H (HighMarkedFrontend.stackMap i)) :
    SqrtLog.LeafProgram.OuterCarried.hidden i := by
  simp only [words,Finset.mem_insert,Finset.mem_singleton,HighMarkedFrontend.stackMap,
    Fin.ext_iff,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hi
  simp only [SqrtLog.LeafProgram.OuterCarried.hidden,List.mem_cons,
    Fin.ext_iff,Fin.coe_ofNat_eq_mod]
  have hv := i.isLt
  omega

private theorem mark_input :
    AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) SqrtLog.LeafProgram.Query.markInput := by
  refine ⟨avoids_copyProgram _ 321 699 698 0 1 (by decide) (by decide) (by decide),
    avoids_transferProgram _ 699 705 0 1 (by decide) (by decide), ?_⟩
  exact ⟨True.intro,⟨by change ¬(H ∘ HighMarkedFrontend.stackMap) 706; decide,True.intro⟩⟩

theorem frontend (k : ℕ) : AvoidsCmd H (HighMarkedFrontend.command k) := by
  have hfront := LowerSafeAvoids.ofMono lower_subset
    (SqrtLog.LeafQueryFrontend.frontend_avoids_outerCarried k)
  have hmark := LowerSafeAvoids.intro mark_input
  let hs := (hmark.seq hfront).liftCall 321 338
  have hpack : ∃ c, c = HighMarkedFrontend.command k ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [HighMarkedFrontend.command, HighMarkedFrontend.localProgram,
      SqrtLog.LeafProgram.Query.markedFrontend]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

attribute [local irreducible] HashMarkedReturn.upperClear

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

/-- The measured prefix of the actual fixed successful branch. -/
theorem PreparedRun.eval {q k hg front padding S B cost}
    (run : PreparedRun q k hg front padding S B cost) :
    Eval (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) front
      (HighCountSeed.initialized (result front run.output) run.seedRegs) :=
  run.preparation.seq run.seed

theorem PreparedRun.time {q k hg front padding S B cost}
    (run : PreparedRun q k hg front padding S B cost) :
    run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps ≤
      cost + 110 * localBound S cost + 81 := by
  have hpreparation : run.packingSteps + run.arithmeticSteps ≤ cost :=
    run.preparation_time
  have hseed : run.seedSteps ≤ 110 * localBound S cost + 80 := run.seed_time
  omega

private theorem local_visible (command : Cmd 40 896) (a b : Data) (steps S cost : ℕ)
    (he : Eval command steps a b) (ht : steps ≤ cost + 1)
    (ha : ∀ i, ¬H i → (a.stacks i).length ≤ S) :
    ∀ i, ¬H i → (b.stacks i).length ≤ localBound S cost := by
  intro i hi
  have h := trace_selectedStackBits (compiled command 778 777) {i}
    (compiled_trace he 778 777)
  have hh : (b.stacks i).length ≤ (a.stacks i).length + steps := by
    simpa only [selectedStackBits,Finset.sum_singleton] using h
  have := ha i hi
  unfold localBound
  omega

/-- Preparation is polynomial work, so its local step bound controls only
visible growth; untouched caller words contribute a separate maximum. -/
private theorem local_space (command : Cmd 40 896)
    (havoid : ProgramTapeReplay.AvoidsCmd H command) (a b : Data) (steps S cost B : ℕ)
    (he : Eval command steps a b) (ht : steps ≤ cost + 1)
    (ha : ∀ i, ¬H i → (a.stacks i).length ≤ S)
    (hf : ∀ i, H i → (a.stacks i).length ≤ B) :
    StageSpace command (steps + 1) a (max (localBound S cost) B) := by
  have hs := ProgramTapeReplay.eval_rebase H havoid he (fun _ => [])
  constructor
  apply CommandStackTransport.eval_shadow_prefix_bound H havoid
    778 777 hs _ hf
  intro t z htz hz i hi
  have h := trace_selectedStackBits (compiled command 778 777) {i} hz
  have hh : (z.stacks i).length ≤
      ((ProgramTapeReplay.rebaseState H (fun _ => []) a).stacks i).length + t := by
    simpa only [selectedStackBits,Finset.sum_singleton] using h
  have hv : ((ProgramTapeReplay.rebaseState H (fun _ => []) a).stacks i).length ≤ S := by
    simpa only [ProgramTapeReplay.rebaseState,ProgramTapeReplay.rebaseStacks_of_not_mem
      H (fun _ => []) a.stacks i hi] using ha i hi
  by_cases ht' : t ≤ steps
  · unfold localBound
    omega
  · have heq : t = steps + 1 := by omega
    subst t
    have hz' := trace_same_length_unique hz (compiled_halt_trace hs 778 777)
    subst z
    have hb := local_visible command a b steps S cost he ht ha i hi
    change (ProgramTapeReplay.rebaseStacks H (fun _ => []) b.stacks i).length ≤ _
    rw [ProgramTapeReplay.rebaseStacks_of_not_mem H (fun _ => []) b.stacks i hi]
    exact hb

private theorem projectedVisible (front : Data) (S : ℕ)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S) :
    ∀ i : Fin 768, ¬LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ S := by
  intro i hi
  apply hvisible (stackMap i)
  intro hh
  simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
  simp only [HighQueryProgram.Carried.words, Finset.mem_insert, Finset.mem_singleton,
    stackMap, Fin.ext_iff, Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hh
  have := i.isLt
  omega

private theorem hidden_kept (i : Fin 896) (hi : H i) : HashMarkedReturn.kept i = true := by
  simp only [HighQueryProgram.Carried.words,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide

/-- Marked setup starts with the actual staged record, executes reference
staging exactly once, constructs the real ring, and initializes the current
high mask. Scalar bounds are on canonical physical frontend lengths. -/
theorem marked_oai : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) (a : Data) (S B : ℕ),
      q.Valid → CleanWork (project a) → Sources q (project a) → q.mark.isSome = true →
      a.stacks 321 = q.index.reverse →
      (∀ i, ¬H i → (a.stacks i).length ≤ S) →
      (∀ i, H i → (a.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ S) →
      let A := S + HighMarkedFrontend.budget q k
      let cost := C * (A+1)^d
      ∃ nf front padding w,
        Eval (HighMarkedFrontend.command k) nf a front ∧
        nf + 1 ≤ HighMarkedFrontend.budget q k ∧
        FrontState q k (markedInput (project a)) (project front) padding w ∧
        ∃ run : PreparedRun q k hg front padding A B cost,
          Eval (.seq (HighMarkedFrontend.command k)
              (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps)) a
            (HighCountSeed.initialized (result front run.output) run.seedRegs) ∧
          nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) ≤
            HighMarkedFrontend.budget q k + cost + 110 * localBound A cost + 81 ∧
          (∀ i, HashMarkedReturn.kept i = true →
            (HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i = a.stacks i) ∧
          StageSpace (.seq (HighMarkedFrontend.command k)
            (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) + 1)
            a (prefixBound q A cost B) := by
  obtain ⟨C,d,hprepare⟩ := prepare_seed
  refine ⟨C,d,?_⟩
  intro q k hg a S B hv hc hs hm href hvisible hhidden hvalue hlength A cost
  obtain ⟨nf,b,_,_,_,he,ht,_⟩ := HighMarkedFrontend.command_eval q k a hv hc hs hm href
  let front := result a b
  have he' : Eval (HighMarkedFrontend.command k) nf a front := he
  obtain ⟨padding,w,hfront⟩ := command_front_state q k a front nf hv hc hs hm href he'
  have hblank := HighFrontendShadow.marked_denominator_empty q k a front nf hv hc hs hm href he'
  have hf := HighMarkedFrontend.command_kept_frame q k a front nf hv hc hs hm href he'
  have hfrontVisible : ∀ i, ¬H i → (front.stacks i).length ≤ A := by
    intro i hi
    have h := trace_selectedStackBits (HighMarkedFrontend.program k) {i}
      (compiled_trace he' 321 338)
    have hh : (front.stacks i).length ≤ (a.stacks i).length + nf := by
      simpa only [selectedStackBits,Finset.sum_singleton] using h
    have := hvisible i hi
    dsimp only [A]
    omega
  have hfrontHidden : ∀ i, H i → (front.stacks i).length ≤ B := by
    intro i hi
    rw [hf i (hidden_kept i hi)]
    exact hhidden i hi
  have hval : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).val i ≤ A := by
    rw [hfront.canonicalLengths]
    exact fun i => (hvalue i).trans (Nat.le_add_right _ _)
  have hlen : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).len i ≤ A := by
    rw [hfront.canonicalLengths]
    exact fun i => (hlength i).trans (Nat.le_add_right _ _)
  obtain ⟨run⟩ := hprepare q k hg (markedInput (project a)) front padding w A B
    hfront hfrontVisible hfrontHidden hval hlen hblank
  have hfrontSpace := local_space (HighMarkedFrontend.command k)
    (HighQueryProgram.Carried.frontend k) a front nf S (HighMarkedFrontend.budget q k) B
    he' (by omega) hvisible hhidden
  have hcap : max (localBound S (HighMarkedFrontend.budget q k)) B ≤ prefixBound q A cost B := by
    apply le_trans _ (Nat.le_max_right _ _)
    apply le_trans _ (Nat.le_max_right _ _)
    apply max_le_max_right
    dsimp [localBound,A]
    omega
  have hfs : StageSpace (HighMarkedFrontend.command k) nf a (prefixBound q A cost B) :=
    ⟨fun t z htz hz i => (hfrontSpace.bound t z (by omega) hz i).trans hcap⟩
  have hrs : StageSpace (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) front
      (prefixBound q A cost B) :=
    ⟨fun t z htz hz i => run.prefix_space.bound t z (Nat.le_succ_of_le htz) hz i⟩
  have hseq := StageSpace.seq he' run.eval hfs hrs
  refine ⟨nf,front,padding,w,he',ht,hfront,run,he'.seq run.eval,?_,?_,?_⟩
  · have hr : run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps ≤
        cost + 110 * localBound A cost + 81 := run.time
    omega
  · intro i hi
    exact (run.kept i hi).trans (hf i hi)
  · exact ⟨StructuredSpace.compiled_halt_stack_bound (he'.seq run.eval) 778 777 hseq.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.marked_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.marked_oai
