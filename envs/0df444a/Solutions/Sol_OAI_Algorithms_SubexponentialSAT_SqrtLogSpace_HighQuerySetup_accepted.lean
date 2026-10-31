-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:30:32.455854+00:00
-- url     : https://prove2.me/submissions/a3bd3efb-1871-44ad-ba73-e2abb335da7d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_frontend_time_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighFrontendShadow_accepted_denominator_empty
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_accepted_command_front_state
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryProgram_Carried_accepted_frontend
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog

theorem result_upper_frame (a : Data) (b : LeafProgram.Query.Data) (i : Fin 896)
    (hi : (768 : ℕ) ≤ i.val) : (result a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem noMarkInput_eval (a : Data) : Eval noMarkInput 3 a (unmarkedInput a) :=
  .base (SubexpParameterProgram.atoms_eval _ a)

theorem unmarkedInput_index (a : Data) (h705 : a.stacks 705=[]) :
    (unmarkedInput a).stacks 705=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705]

theorem unmarkedInput_flag (a : Data) (h706 : a.stacks 706=[]) :
    (unmarkedInput a).stacks 706=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h706]

theorem unmarkedInput_frame (a : Data) (i : Fin 768) (h705 : i≠705) (h706 : i≠706) :
    (unmarkedInput a).stacks i=a.stacks i := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705,h706]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete source masters and reusable empty workspace at each marked
query boundary. The frontend's hypotheses follow after the paid reference
staging program; no serialized scope or arithmetic cache is an input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem cleanWork_private (a : Data) (h : CleanWork a) (i : Fin 768)
    (hlo : 340 ≤ i.val) (hhi : i.val < 680) : a.stacks i=[] := by
  apply h
  · intro hp
    simp only [Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
    norm_num at hp
    omega
  · intro hi
    subst i
    norm_num at hlo

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryAccepted
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The accepted (unmarked) query uses the same immutable source masters and
explicitly writes the two false singleton fields consumed by the frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem accepted_ready (q : LeafQueryFrontend.Query) (a : Data)
    (hc : CleanWork a) (hs : Sources q a) (hm : q.mark=none) (hi : q.index=[false]) :
    q.Ready (unmarkedInput a) := by
  have e705 := hc 705 (by decide) (by decide)
  have e706 := hc 706 (by decide) (by decide)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (unmarkedInput_frame a 700 (by decide) (by decide)).trans hs.formula
  · exact (unmarkedInput_frame a 701 (by decide) (by decide)).trans hs.rows
  · rw [hi]
    exact unmarkedInput_index a e705
  · simpa only [hm,Option.isSome_none] using unmarkedInput_flag a e706
  · exact (unmarkedInput_frame a 707 (by decide) (by decide)).trans hs.modulus
  · exact (unmarkedInput_frame a 708 (by decide) (by decide)).trans hs.width
  · exact (unmarkedInput_frame a 709 (by decide) (by decide)).trans hs.ambient
  · intro i hlo hhi
    rw [unmarkedInput_frame a i
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)]
    exact cleanWork_private a hc i hlo hhi
  · exact (unmarkedInput_frame a 338 (by decide) (by decide)).trans
      (hc 338 (by decide) (by decide))
  · exact (unmarkedInput_frame a 718 (by decide) (by decide)).trans
      (hc 718 (by decide) (by decide))
  · exact (unmarkedInput_frame a 719 (by decide) (by decide)).trans
      (hc 719 (by decide) (by decide))

theorem accepted_outputs_empty (a : Data) (hc : CleanWork a) :
    LeafParametersProgram.Exports.OutputEmpty (unmarkedInput a) ∧
      (unmarkedInput a).stacks 704=[] ∧ (unmarkedInput a).stacks 134=[] ∧
      (unmarkedInput a).stacks 141=[] := by
  constructor
  · intro i
    have hne : ¬Protected (LeafParametersProgram.Exports.destination i) := by fin_cases i <;> decide
    have h321 : LeafParametersProgram.Exports.destination i≠321 := by fin_cases i <;> decide
    rw [unmarkedInput_frame a _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact hc _ hne h321
  · refine ⟨?_,?_,?_⟩
    · exact (unmarkedInput_frame a 704 (by decide) (by decide)).trans
        (hc 704 (by decide) (by decide))
    · exact (unmarkedInput_frame a 134 (by decide) (by decide)).trans
        (hc 134 (by decide) (by decide))
    · exact (unmarkedInput_frame a 141 (by decide) (by decide)).trans
        (hc 141 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The original actual marked-scope/high-mask/parameter frontend is lifted
into the shared leaf ABI. Upper caller words and the marked mass collector
are retained; the lower workspace is reclaimed by an actual cleanup program. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

/-- The unmarked native execution also has a source-dependent time bound
without restricting suspended collector words. -/
theorem accepted_command_eval (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark=none)
    (hindex : q.index=[false]) :
    ∃ steps b tau l w,
      Eval (acceptedCommand k) steps a (result a b) ∧
      steps+1 ≤ acceptedBudget q k ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^(2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) := by
  have hready := LeafProgram.Query.accepted_ready q (project a) hc hs hm hindex
  have hempty := LeafProgram.Query.accepted_outputs_empty (project a) hc
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,_,ht,h704,h718,h338,h719,h134,
      hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafQueryFrontend.frontend_eval q k (LeafProgram.Query.unmarkedInput (project a))
      hv hready hempty
  have hn := LeafQueryFrontend.frontend_time_le q k hv hready hempty he
  have hwhole := (LeafProgram.Query.noMarkInput_eval (project a)).seq he
  have hev := eval_liftCommand_from_state (acceptedLocalCommand k) 700 338 id stackMap a
    Function.injective_id (Fin.castAdd_injective _ _) hwhole
  refine ⟨3+n+1,b,tau,l,w,?_,by dsimp [acceptedBudget]; omega,
    ht,h704,h718,h338,h719,h134,hex,h141,hbank,hshape,hguard,hclean,?_⟩
  · simpa only [acceptedCommand,acceptedLocalProgram,result] using hev
  intro i hi h134 h141 h338 h704 h718 h719 h705 h706 _ hd
  exact (hframe i hi h134 h141 h338 h704 h718 h719 hd).trans
    (LeafProgram.Query.unmarkedInput_frame (project a) i h705 h706)

/-- The concrete return collector's retained words survive the actual
frontend result. This includes immutable sources and every caller bank. -/
theorem result_kept_frame (a : Data) (b : LeafProgram.Query.Data)
    (hframe : ∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) →
      i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
      (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks (stackMap i)) :
    ∀ i, HashMarkedReturn.kept i=true → (result a b).stacks i=a.stacks i := by
  intro i hk
  by_cases hi : i.val<768
  · let j : Fin 768 := ⟨i.val,hi⟩
    have hij : i=stackMap j := rfl
    have hv : j.val=320 ∨ j.val=322 ∨ j.val=700 ∨ j.val=701 ∨
        j.val=707 ∨ j.val=708 ∨ j.val=709 ∨ 744 ≤ j.val := by
      simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
        Fin.coe_ofNat_eq_mod] at hk
      dsimp [j]
      omega
    rw [hij,result_stack]
    apply hframe j (by omega)
    all_goals try (intro he; have hh := congrArg Fin.val he; norm_num at hh; omega)
    intro x he
    have hh := congrArg Fin.val he
    fin_cases x <;> norm_num [Exports.destination] at hh <;> omega
  · exact result_upper_frame a b i (by omega)

/-- The accepted history-only frontend preserves the same concrete retained
words before its final count is installed on788. -/
theorem accepted_command_kept_frame (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (steps : ℕ) (hv : q.Valid) (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark=none)
    (hindex : q.index=[false]) (he : Eval (acceptedCommand k) steps a b) :
    ∀ i, HashMarkedReturn.kept i=true → b.stacks i=a.stacks i := by
  obtain ⟨n,c,tau,l,w,hec,_,_,_,_,_,_,_,_,_,_,_,_,_,hf⟩ :=
    accepted_command_eval q k a hv hc hs hm hindex
  have hb := SubexpPrimeProgram.eval_result_unique he hec 700 338
  rw [hb]
  exact result_kept_frame a c hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
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

/-- The accepted query executes actual false-flag staging and the same
concrete preparation on history-only sources, retaining the full ambient n. -/
theorem accepted_oai : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) (a : Data) (S B : ℕ),
      q.Valid → CleanWork (project a) → Sources q (project a) → q.mark = none → q.index = [false] →
      (∀ i, ¬H i → (a.stacks i).length ≤ S) →
      (∀ i, H i → (a.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code
        (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ S) →
      let A := S + HighMarkedFrontend.acceptedBudget q k
      let cost := C * (A+1)^d
      ∃ nf front padding w,
        Eval (HighMarkedFrontend.acceptedCommand k) nf a front ∧
        nf + 1 ≤ HighMarkedFrontend.acceptedBudget q k ∧
        FrontState q k (unmarkedInput (project a)) (project front) padding w ∧
        ∃ run : PreparedRun q k hg front padding A B cost,
          Eval (.seq (HighMarkedFrontend.acceptedCommand k)
              (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps)) a
            (HighCountSeed.initialized (result front run.output) run.seedRegs) ∧
          nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) ≤
            HighMarkedFrontend.acceptedBudget q k + cost + 110 * localBound A cost + 81 ∧
          (∀ i, HashMarkedReturn.kept i = true →
            (HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i = a.stacks i) ∧
          StageSpace (.seq (HighMarkedFrontend.acceptedCommand k)
            (.seq HighQueryProgram.prepare HighQueryProgram.seed))
            (nf + (run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps) + 1)
            a (prefixBound q A cost B) := by
  obtain ⟨C,d,hprepare⟩ := prepare_seed
  refine ⟨C,d,?_⟩
  intro q k hg a S B hv hc hs hm hindex hvisible hhidden hvalue hlength A cost
  obtain ⟨nf,b,_,_,_,he,ht,_⟩ := HighMarkedFrontend.accepted_command_eval q k a hv hc hs hm hindex
  let front := result a b
  have he' : Eval (HighMarkedFrontend.acceptedCommand k) nf a front := he
  obtain ⟨padding,w,hfront⟩ := accepted_command_front_state q k a front nf hv hc hs hm hindex he'
  have hblank := HighFrontendShadow.accepted_denominator_empty q k a front nf hv hc hs hm hindex he'
  have hf := HighMarkedFrontend.accepted_command_kept_frame q k a front nf hv hc hs hm hindex he'
  have hfrontVisible : ∀ i, ¬H i → (front.stacks i).length ≤ A := by
    intro i hi
    have h := trace_selectedStackBits (HighMarkedFrontend.acceptedProgram k) {i}
      (compiled_trace he' 700 338)
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
  obtain ⟨run⟩ := hprepare q k hg (unmarkedInput (project a)) front padding w A B
    hfront hfrontVisible hfrontHidden hval hlen hblank
  have hfrontSpace := local_space (HighMarkedFrontend.acceptedCommand k)
    (HighQueryProgram.Carried.accepted_frontend k) a front nf S (HighMarkedFrontend.acceptedBudget q k) B
    he' (by omega) hvisible hhidden
  have hcap : max (localBound S (HighMarkedFrontend.acceptedBudget q k)) B ≤ prefixBound q A cost B := by
    apply le_trans _ (Nat.le_max_right _ _)
    apply le_trans _ (Nat.le_max_right _ _)
    apply max_le_max_right
    dsimp [localBound,A]
    omega
  have hfs : StageSpace (HighMarkedFrontend.acceptedCommand k) nf a (prefixBound q A cost B) :=
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

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.accepted_oai
