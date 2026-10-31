-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:33:14.098473+00:00
-- url     : https://prove2.me/submissions/931a5dfa-6284-461b-9e06-7c157691e67a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S192
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryStart_resources

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- The successful branch test is the actual register written by the frontend. -/
theorem front_guard_register (q : LeafQueryFrontend.Query) (k : ℕ)
    (base front : Data) (l : Fin 8 → ℕ) (w : Bank.Words)
    (hf : FrontState q k base front l w) (hg : Guard (q.input k)) :
    front.regs 8 = true := hf.guard.mpr hg

/-- Packing and arithmetic preserve the current high mask and all collector
words. This is an endpoint fact about the concrete executed outputs. -/
theorem collector_frame (front packed out : Data) (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hb : packed.stacks = (PackingCallerProgram.result front p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {half : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (ho : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 768) (hlo : 320 ≤ i.val) (hhi : i.val < 340) :
    out.stacks i = front.stacks i := by
  rw [ho.collectorFrame i hlo hhi, hb]
  exact PackingCallerProgram.result_frame front p first rest i
    (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))

/-- Persistent query sources stay byte-identical through the preparation. -/
theorem sources_frame (front packed out : Data) (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hb : packed.stacks = (PackingCallerProgram.result front p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {half : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (ho : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 768) (hi : i ∈ ([700,701,702,703,707,708,709] : List (Fin 768))) :
    out.stacks i = front.stacks i := by
  have hf : out.stacks i = packed.stacks i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ho.highFrame _ (by decide) (by decide) (by decide)
  rw [hf, hb]
  apply PackingCallerProgram.result_frame
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
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

private theorem LowerSafeAvoids.ofMono {K : Fin 768 → Prop} {c : Cmd 40 768}
    (sub : ∀ i, (H ∘ HighMarkedFrontend.stackMap) i → K i)
    (hc : AvoidsCmd K c) : LowerSafeAvoids c :=
  ⟨avoidsCmd_mono sub hc⟩

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

attribute [local irreducible] HashMarkedReturn.upperClear

/-- The actual lower preparation excludes the collector tapes by its
instruction certificate; the selector words lie outside its lifted bank. -/
theorem preparation : AvoidsCmd H prepare := by
  have hcommand := LowerSafeAvoids.ofMono lower_subset
    NativeQueryPreparation.command_avoids
  let hs := hcommand.liftCall 700 728
  have hpack : ∃ c, c = prepare ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [prepare, preparationProgram]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual entry to each high-assignment count. The current frontend mask
survives concrete packing/arithmetic and drives the fixed zero-seed program.
The compact returned boundary is separate from the transient prefix bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound

section Preparation

variable (q : LeafQueryFrontend.Query) (k : ℕ) (base : Lower) (front : Data)
  (l : Fin 8 → ℕ) (bw : Bank.Words) (packed out : Lower)
  (p : PackingCallerProgram.Problem)
  (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
  (hfront : FrontState q k base (HighMarkedFrontend.project front) l bw)
  (hpacked : packed.stacks =
    (PackingCallerProgram.result (HighMarkedFrontend.project front) p first rest).stacks)
  {m : Circuit.Model} {hd : 0 < m.val 34}
  {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
  {cache : RingProgram.ScalarCache 3 (m.val 33)}
  {half : RingProgram.ScalarCode 3 (m.val 33)} {e : LeafRingSetupProgram.Data}
  (hout : ArithmeticOutput packed out m hd M cache half e)

include hfront hpacked hout

/-- Concrete preparation preserves the freshly recomputed current-query mask. -/
theorem prepared_mask :
    (HighMarkedFrontend.result front out).stacks 338 =
      LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) := by
  rw [show (338 : Fin 896) = HighMarkedFrontend.stackMap 338 from rfl,
    HighMarkedFrontend.result_stack]
  exact (NativeQueryPreparation.collector_frame
    (HighMarkedFrontend.project front) packed out p first rest hpacked hout
    338 (by decide) (by decide)).trans hfront.descending

end Preparation

/-- Every immutable source and suspended selector word survives the actual
packing/arithmetic outputs. No source is assumed unread here. -/
theorem prepared_kept_frame (front : Data) (packed out : Lower)
    (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hpacked : packed.stacks =
      (PackingCallerProgram.result (HighMarkedFrontend.project front) p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {half : RingProgram.ScalarCode 3 (m.val 33)} {e : LeafRingSetupProgram.Data}
    (hout : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 896) (hi : HashMarkedReturn.kept i = true) :
    (HighMarkedFrontend.result front out).stacks i = front.stacks i := by
  by_cases hu : 768 ≤ i.val
  · exact HighMarkedFrontend.result_upper_frame front out i hu
  · let j : Fin 768 := ⟨i.val,by omega⟩
    have hij : HighMarkedFrontend.stackMap j = i := Fin.ext rfl
    rw [←hij,HighMarkedFrontend.result_stack]
    change out.stacks j = (HighMarkedFrontend.project front).stacks j
    have hj : j = 320 ∨ j = 322 ∨ j = 700 ∨ j = 701 ∨ j = 707 ∨
        j = 708 ∨ j = 709 ∨ 744 ≤ j.val := by
      simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
        Fin.coe_ofNat_eq_mod] at hi ⊢
      dsimp [j]
      omega
    rcases hj with h | h | h | h | h | h | h | h
    · rw [h]
      exact NativeQueryPreparation.collector_frame _ packed out p first rest hpacked hout
        320 (by decide) (by decide)
    · rw [h]
      exact NativeQueryPreparation.collector_frame _ packed out p first rest hpacked hout
        322 (by decide) (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 700 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 701 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 707 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 708 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 709 (by decide)
    · have ha : out.stacks j = packed.stacks j := by
        apply hout.highFrame j (by omega)
        · intro he
          have hv := congrArg Fin.val he
          change j.val = 699 at hv
          omega
        · intro he
          simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,
            Fin.coe_ofNat_eq_mod] at he
          omega
      rw [ha,hpacked]
      exact PackingCallerProgram.result_frame _ p first rest j
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr h)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
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

private theorem halt_space {command : Cmd 40 896} {steps bound : ℕ} {a b : Data}
    (he : Eval command steps a b) (hspace : StageSpace command steps a bound) :
    StageSpace command (steps + 1) a bound := by
  constructor
  exact StructuredSpace.compiled_halt_stack_bound he 778 777 hspace.bound

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

private theorem projectedHidden (front : Data) (S B : ℕ)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B) :
    ∀ i : Fin 768, LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ max S B := by
  intro i _
  by_cases hi : H (stackMap i)
  · exact (hhidden _ hi).trans (Nat.le_max_right _ _)
  · exact (hvisible _ hi).trans (Nat.le_max_left _ _)

private theorem frontRun (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i : Fin 768, ¬LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ S)
    (hhidden : ∀ i : Fin 768, LeafProgram.OuterCarried.hidden i →
      ((project front).stacks i).length ≤ max S B)
    (hvalue : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).val i ≤ S)
    (hlength : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).len i ≤ S)
    (h728 : front.stacks 728 = []) :
    Nonempty (NativeQueryPreparation.FrontRun q k hg (project front) padding S (max S B)
      (preparationConstant * (S + 1) ^ preparationDegree)) :=
  preparationResources q k hg base (project front) padding w S (max S B)
    hfront hvisible hhidden hvalue hlength h728

private theorem finishPreparation (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B)
    (first : MulticolorTypes.Word (preparedProblem q k hg).r (preparedProblem q k hg).Q)
    (rest : List (MulticolorTypes.Word (preparedProblem q k hg).r
      (preparedProblem q k hg).Q)) (packed : Lower) (np na : ℕ)
    (e : LeafRingSetupProgram.Data)
    (M : SubexpPreparedQuartic.Modulus 3 ((preparedModel q k padding).val 33))
    (cache : RingProgram.ScalarCache 3 ((preparedModel q k padding).val 33))
    (half : RingProgram.ScalarCode 3 ((preparedModel q k padding).val 33)) (out : Lower)
    (hrows : (first :: rest).map Subexp.ReadPlan.encodeWord =
      Subexp.AssignmentAlphabetSemantics.wordBytes (preparedProblem q k hg).r
        (preparedProblem q k hg).Q)
    (hnodup : (first :: rest).Nodup) (hcomplete : ∀ z, z ∈ first :: rest)
    (hpack : Eval PackingCallerProgram.command np (project front) packed)
    (hbytes : packed.stacks =
      (PackingCallerProgram.result (project front) (preparedProblem q k hg)
        first rest).stacks)
    (harith : Eval NativeQueryPreparation.arithmeticCommand na packed out)
    (houtput : ArithmeticOutput packed out (preparedModel q k padding)
      (ring_degree_pos (q.input k) padding hg) M cache half e)
    (hdegree : out.stacks 204 =
      List.replicate ((preparedModel q k padding).val 34) true)
    (hinverse : inverseLaw q k hg padding packed M cache half)
    (he : Eval NativeQueryPreparation.command (np + na) (project front) out)
    (htime : np + na ≤ preparationConstant * (S + 1) ^ preparationDegree) :
    Nonempty (PreparedRun q k hg front padding S B
      (preparationConstant * (S + 1) ^ preparationDegree)) := by
  have hp : Eval HighQueryProgram.prepare (np + na + 1) front (result front out) :=
    eval_call_from_state (compiled NativeQueryPreparation.command 700 728) id stackMap front
      Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace he 700 728)
  have hpv := local_visible HighQueryProgram.prepare front (result front out) (np + na + 1) S
    (preparationConstant * (S + 1) ^ preparationDegree) hp (by omega) hvisible
  have hps := local_space HighQueryProgram.prepare HighQueryProgram.Carried.preparation
    front (result front out) (np + na + 1) S
    (preparationConstant * (S + 1) ^ preparationDegree) B hp
    (by omega) hvisible hhidden
  have hpb : ∀ i, ((result front out).stacks i).length ≤
      max (localBound S (preparationConstant * (S + 1) ^ preparationDegree)) B :=
    fun i => hps.bound _ _ (by omega) (compiled_trace hp 778 777) i
  have hmask := HighQueryStart.prepared_mask q k base front padding w packed out
    (packingProblem q k hg) first rest hfront hbytes houtput
  have hseed : ∀ i ∈ HighQueryLocalBounds.seedSources,
      ((result front out).stacks i).length ≤
        localBound S (preparationConstant * (S + 1) ^ preparationDegree) := by
    intro i hi
    apply hpv i
    simp only [HighQueryLocalBounds.seedSources, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hboundary : max (localBound S
      (preparationConstant * (S + 1) ^ preparationDegree)) B ≤
      boundaryBound q S (preparationConstant * (S + 1) ^ preparationDegree) B :=
    Nat.le_max_right _ _
  have hprefix : boundaryBound q S
      (preparationConstant * (S + 1) ^ preparationDegree) B ≤
      prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B :=
    Nat.le_max_right _ _
  obtain ⟨ns, rf, hst, hs, _, hspace, hbound, hcounter, hclear, hguard, hkept⟩ :=
    HighQueryStart.resources q (result front out)
      (localBound S (preparationConstant * (S + 1) ^ preparationDegree))
      (boundaryBound q S (preparationConstant * (S + 1) ^ preparationDegree) B)
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B)
      hmask hseed (Nat.le_max_left _ _) (fun i => (hpb i).trans (hboundary.trans hprefix))
      (Nat.le_max_left _ _) (fun i _ => (hpb i).trans hboundary)
  have hps' : StageSpace HighQueryProgram.prepare (np + na + 1) front
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B) :=
    ⟨fun t z ht hz i => (hps.bound t z (by omega) hz i).trans (hboundary.trans hprefix)⟩
  have hss : StageSpace HighQueryProgram.seed ns (result front out)
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B) :=
    ⟨fun t z ht hz i => hspace t z (by omega) hz i⟩
  have hseq := StageSpace.seq hp hs hps' hss
  have hpseq : Eval (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (np + na + 1 + ns) front (HighCountSeed.initialized (result front out) rf) :=
    hp.seq hs
  have hprefixSpace : StageSpace (.seq HighQueryProgram.prepare HighQueryProgram.seed)
      (np + na + 1 + ns + 1) front
      (prefixBound q S (preparationConstant * (S + 1) ^ preparationDegree) B) := by
    exact halt_space hpseq hseq
  let packingData : PackingData q k hg := {
    first := first
    rest := rest
    packed := packed
    packingSteps := np }
  let arithmeticData : ArithmeticData q k padding := (na, e, M, cache, half, out)
  let seedData : SeedData := {
    seedSteps := ns
    seedRegs := rf }
  let data : PreparedData q k hg padding := (packingData, arithmeticData, seedData)
  let execution : PreparedExecution q k hg front padding data := {
    rows := hrows
    nodup := hnodup
    complete := hcomplete
    packing := hpack
    packed_words := hbytes
    arithmetic := harith
    arithmetic_output := houtput
    degree := hdegree
    inverse := hinverse
    preparation := hp
    seed := hs }
  refine ⟨⟨data, execution, {
    preparation_time := htime
    seed_time := hst
    guard := NativeQueryPreparation.front_guard_register q k base
      (project front) padding w hfront hg
    mask := hmask
    counter := hcounter
    cleared := hclear
    high_guard := hguard
    kept := ?_
    boundary := hbound
    preparation_space := hps'
    seed_space := hss
    prefix_space := hprefixSpace }⟩⟩
  · intro i hi
    exact (hkept i hi).trans
      (HighQueryStart.prepared_kept_frame front packed out (packingProblem q k hg)
        first rest hbytes houtput i hi)

private theorem finishFrontRun (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B)
    (run : NativeQueryPreparation.FrontRun q k hg (project front) padding S (max S B)
      (preparationConstant * (S + 1) ^ preparationDegree)) :
    Nonempty (PreparedRun q k hg front padding S B
      (preparationConstant * (S + 1) ^ preparationDegree)) := by
  rcases run with ⟨data, execution, bounds⟩
  rcases data with ⟨packingData, arithmeticData⟩
  rcases packingData with ⟨first, rest, packed, np⟩
  rcases arithmeticData with ⟨na, e, M, cache, half, out⟩
  rcases execution with ⟨hrows, hnodup, hcomplete, hpack, hbytes, harith, houtput,
    hdegree, hinverse, he⟩
  have htime := bounds.time
  apply finishPreparation q k hg base front padding w S B hfront hvisible hhidden
    first rest packed np na e M cache half out
  all_goals assumption

private theorem prepareSeedFixed (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base : Lower) (front : Data) (padding : Fin 8 → ℕ)
    (w : Bank.Words) (S B : ℕ)
    (hfront : FrontState q k base (project front) padding w)
    (hvisible : ∀ i, ¬H i → (front.stacks i).length ≤ S)
    (hhidden : ∀ i, H i → (front.stacks i).length ≤ B)
    (hvalue : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).val i ≤ S)
    (hlength : ∀ i, (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) padding)).len i ≤ S)
    (h728 : front.stacks 728 = []) :
    Nonempty (PreparedRun q k hg front padding S B
      (preparationConstant * (S + 1) ^ preparationDegree)) := by
  have hv := projectedVisible front S hvisible
  have hh := projectedHidden front S B hvisible hhidden
  obtain ⟨run⟩ := frontRun q k hg base front padding w S B hfront hv hh
    hvalue hlength h728
  exact finishFrontRun q k hg base front padding w S B hfront hvisible hhidden run

/-- The actual prepared run is constructed from the concrete frontend output
and its serialized scalar bounds. Arbitrary suspended caller words affect
only the separate frame bound, never the preparation or seed time. -/
theorem prepare_seed_oai : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
      (base : Lower) (front : Data) (padding : Fin 8 → ℕ) (w : Bank.Words) (S B : ℕ),
      FrontState q k base (project front) padding w →
      (∀ i, ¬H i → (front.stacks i).length ≤ S) →
      (∀ i, H i → (front.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) padding)).len i ≤ S) →
      front.stacks 728 = [] → Nonempty (PreparedRun q k hg front padding S B (C*(S+1)^d)) := by
  exact ⟨preparationConstant, preparationDegree, prepareSeedFixed⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.prepare_seed_oai
