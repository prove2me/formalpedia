-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:48:17.052608+00:00
-- url     : https://prove2.me/submissions/7758c2ab-a0ed-4f86-a6bd-c954328cc77a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

/-- Resume consumes one suspended frame and exactly restores its payload. -/
theorem popFrame_trace (word frames : List Bool) (v present : Bool) :
    Trace ParserProgram.frameProgram (6 * word.length + 4)
      (ParserProgram.cfg (some 0) v present (Encoding.frame word.reverse ++ frames) [])
      (ParserProgram.cfg none false true frames word) := by
  simpa using ParserProgram.frame_trace word.reverse frames [] v present

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ he => congrArg g he) g a
  · exact Function.extend_apply' _ _ _ h

private theorem word_embed_self (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) :
    embedState frameRegisters (wordPorts src dst h) a
      (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)) = a := by
  apply CounterForPrograms.data_ext
  · have hr : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).regs =
        a.regs ∘ frameRegisters := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend frameRegisters _ a.regs = a.regs
    rw [hr, extend_restrict_eq]
  · have hs : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).stacks =
        a.stacks ∘ wordPorts src dst h := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend (wordPorts src dst h) _ a.stacks = a.stacks
    rw [hs, extend_restrict_eq]

theorem popWord_eval (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (word tail : List Bool) (hs : a.stacks src = Encoding.frame word.reverse ++ tail)
    (hd : a.stacks dst = []) :
    Eval (popWordCommand src dst h) (6 * word.length + 4) a
      (popWordState src dst h a word tail) := by
  have ht := eval_call_lifted ParserProgram.frameProgram frameRegisters (wordPorts src dst h) a
    frameRegisters.injective (wordPorts src dst h).injective
    (a := frameState (a.regs 0) (a.regs 1) (Encoding.frame word.reverse ++ tail) [])
    (b := frameState false true tail word)
    (popFrame_trace word tail (a.regs 0) (a.regs 1))
  rw [← hs, ← hd, word_embed_self] at ht
  exact ht

theorem popWordState_outside (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (popWordState src dst h a word tail).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

theorem readHead_eval (a : Data) (word tail address : List Bool)
    (hframes : a.stacks 840 = Encoding.frame word.reverse ++ tail)
    (hword : a.stacks 838 = []) (haddress : a.stacks 843 = true :: address) :
    Eval readHead (6 * word.length + 5) a (headState a word tail address) := by
  have hp := popWord_eval 840 838 (by decide) a word tail hframes hword
  let b := popWordState 840 838 (by decide) a word tail
  have hb : b.stacks 843 = true :: address := by
    rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide)]
    exact haddress
  have he : Eval (.base (.atom (.pop 843 0 1))) 1 b (headState a word tail address) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop 843 0 1) b) using 1
    all_goals try with_reducible_and_instances rfl
    apply SubexpScanPrimitives.state_ext
    · change readRegs b.regs 0 1 (some true) = readRegs b.regs 0 1 (b.stacks 843).head?
      rw [hb]
      rfl
    · change Function.update b.stacks 843 address = Function.update b.stacks 843 (b.stacks 843).tail
      rw [hb]
      rfl
  simpa only [readHead, headState,
    show 6 * word.length + 4 + 1 = 6 * word.length + 5 by omega] using hp.seq he

/-- The address counts unprocessed heads above the fixed node offset. Reading
one frame decrements exactly once, even if that representative has zero bits. -/
theorem readHead_frames (a : Data) (word : List Bool) (rest : List (List Bool))
    (base : ℕ)
    (hframes : a.stacks 840 = suspendedFrames (word :: rest))
    (hword : a.stacks 838 = [])
    (haddress : a.stacks 843 = List.replicate (base + (word :: rest).length) true) :
    Eval readHead (6 * word.length + 5) a
      (headState a word (suspendedFrames rest) (List.replicate (base + rest.length) true)) := by
  apply readHead_eval
  · simpa only [suspendedFrames, List.flatMap_cons] using hframes
  · exact hword
  · simpa only [List.length_cons, Nat.add_succ, List.replicate_succ] using haddress

private theorem clear_eval (dst : Fin 896) (a : Data) :
    Eval (.call (StackRoutines.clearProgram dst 0 1)) (2 * (a.stacks dst).length + 3)
      a ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks dst a.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run dst (0 : Fin 40) 1 a.regs a.stacks)

theorem overwrite_eval (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) :
    Eval (overwrite src dst) (2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8)
      a (overwriteState src dst a) := by
  have hc := clear_eval dst a
  have ht : (StackRoutines.clearStacks dst a.stacks) 841 = [] := by
    simp [StackRoutines.clearStacks, htd, htmp]
  have hp := copyWord_eval src dst 841 hsd hst htd
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩ ht
  have hs : (StackRoutines.clearStacks dst a.stacks) src = a.stacks src := by
    simp [StackRoutines.clearStacks,hsd]
  simpa only [overwrite, overwriteState, hs, show 2 * (a.stacks dst).length + 3 +
    (7 * (a.stacks src).length + 5) =
    2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 by omega] using hc.seq hp

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

theorem testFrames_eval (a : Data) : Eval testFrames 1 a (tested a) :=
  Eval.base (StructuredProgram.Eval.atom (.peek 840 0 1) a)

theorem tested_empty (a : Data) (h : a.stacks 840 = []) : (tested a).regs 1 = false := by
  simp [tested,readRegs,h]

theorem tested_cons (a : Data) (word : List Bool) (rest : List (List Bool))
    (h : a.stacks 840 = suspendedFrames (word :: rest)) : (tested a).regs 1 = true := by
  have hn : Encoding.frame word.reverse ≠ [] := by
    cases word.reverse <;> simp [Encoding.frame]
  simp [tested,readRegs,h,suspendedFrames,hn]

theorem finishHead_eval (a : Data) :
    Eval finishHead (2 * (a.stacks 838).length + 4) a (finished a) := by
  have h := (clear_eval 838 a).seq (testFrames_eval _)
  simpa only [finishHead, finished, show 2 * (a.stacks 838).length + 3 + 1 =
    2 * (a.stacks 838).length + 4 by omega] using h

theorem finished_stacks (a : Data) :
    (finished a).stacks = Function.update a.stacks 838 [] := rfl

theorem finished_cursor (base : ℕ) (words : List (List Bool)) (a : Data)
    (hf : a.stacks 840 = suspendedFrames words)
    (ha : a.stacks 843 = List.replicate (base + words.length) true) :
    FrameCursor base words (finished a) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [finished_stacks,Function.update_of_ne (by decide : (840 : Fin 896) ≠ 838)] using hf
  · rw [finished_stacks,Function.update_self]
  · simpa only [finished_stacks,Function.update_of_ne (by decide : (843 : Fin 896) ≠ 838)] using ha
  · cases words with
    | nil =>
        apply tested_empty
        simpa [suspendedFrames, StackRoutines.clearStacks,
          Function.update_of_ne (by decide : (840 : Fin 896) ≠ 838)] using hf
    | cons word rest =>
        apply tested_cons _ word rest
        simpa only [StackRoutines.clearStacks,
          Function.update_of_ne (by decide : (840 : Fin 896) ≠ 838)] using hf

/-- Repeated passes retain the same word bound: overwrite replaces one word,
rather than appending to a growing visit history. -/
theorem overwriteState_bound (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((overwriteState src dst a).stacks i).length ≤ B := by
  intro i
  rw [overwriteState_stacks src dst hsd]
  by_cases hi : i = dst
  · subst i
    rw [Function.update_self]
    exact hb src
  · rw [Function.update_of_ne hi]
    exact hb i

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

theorem restart_eval (a : Data) (htmp : a.stacks 841 = []) :
    Eval restart (restartCost a) a (restartState a) := by
  have h1 := overwrite_eval 837 840 (by decide) (by decide) (by decide) a htmp
  have h841 : (overwriteState 837 840 a).stacks 841 = [] :=
    (overwriteState_frame _ _ (by decide) _ _ (by decide)).trans htmp
  have h2 := overwrite_eval 845 843 (by decide) (by decide) (by decide)
    (overwriteState 837 840 a) h841
  have h843 := overwriteState_frame 837 840 (by decide) a 843 (by decide)
  have h845 := overwriteState_frame 837 840 (by decide) a 845 (by decide)
  have ht := h1.seq h2
  simpa only [restart, restartState, h843,h845,restartCost,show
    2 * (a.stacks 840).length + 7 * (a.stacks 837).length + 8 +
      (2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 8) =
    2 * (a.stacks 840).length + 7 * (a.stacks 837).length +
      2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 16 by omega] using ht

theorem restartState_words (a : Data) :
    (restartState a).stacks 840 = a.stacks 837 ∧
      (restartState a).stacks 843 = a.stacks 845 := by
  have h1 := overwriteState_stacks 837 840 (by decide) a
  have h2 := overwriteState_stacks 845 843 (by decide) (overwriteState 837 840 a)
  change (overwriteState 845 843 (overwriteState 837 840 a)).stacks 840 = a.stacks 837 ∧
    (overwriteState 845 843 (overwriteState 837 840 a)).stacks 843 = a.stacks 845
  rw [h2,h1]
  simp

theorem restartState_frame (a : Data) (i : Fin 896) (h840 : i ≠ 840) (h843 : i ≠ 843) :
    (restartState a).stacks i = a.stacks i := by
  rw [restartState,overwriteState_frame _ _ (by decide) _ _ h843,
    overwriteState_frame _ _ (by decide) _ _ h840]

theorem restartState_bound (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((restartState a).stacks i).length ≤ B :=
  overwriteState_bound 845 843 (by decide) _ B
    (overwriteState_bound 837 840 (by decide) a B hb)

theorem restartState_cursor (a : Data) (base : ℕ) (words : List (List Bool))
    (hreps : a.stacks 837 = suspendedFrames words)
    (haddr : a.stacks 845 = List.replicate (base + words.length) true)
    (hcurrent : a.stacks 838 = []) :
    FrameCursor base words (tested (restartState a)) := by
  have hf := (restartState_words a).1.trans hreps
  refine ⟨hf,?_,(restartState_words a).2.trans haddr,?_⟩
  · exact (restartState_frame a 838 (by decide) (by decide)).trans hcurrent
  · cases words with
    | nil => exact tested_empty _ hf
    | cons word rest => exact tested_cons _ word rest hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
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

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

theorem finished_bound (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((finished a).stacks i).length ≤ B := by
  intro i
  rw [finished_stacks]
  by_cases hi : i=838
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    exact ha i

theorem cursor_word_length {base B : ℕ} {word : List Bool}
    {rest : List (List Bool)} {a : Data}
    (hc : FrameCursor base (word::rest) a)
    (ha : ∀ i, (a.stacks i).length ≤ B) : word.length ≤ B := by
  have h := ha 840
  rw [hc.frames] at h
  simp only [suspendedFrames, List.flatMap_cons, List.length_append,
    Encoding.length_frame, List.length_reverse] at h
  omega

/-- The actual frame parser and cleanup are composed with the measured work
trace. The possibly exponential work time does not enter the storage bound. -/
theorem body_prefix (work : Code) (base B D steps : ℕ) (a b : Data)
    (word : List Bool) (rest : List (List Bool))
    (hc : FrameCursor base (word::rest) a)
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hw : Eval work steps
      (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b)
    (hb : ∀ i, (b.stacks i).length ≤ B)
    (hp : PrefixBound work steps
      (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D) :
    PrefixBound (headBody work)
      (6*word.length+5+(steps+(2*(b.stacks 838).length+4))) a
      (max D (904*B+10)) := by
  have hlen := cursor_word_length hc ha
  have hr := readHead_frames a word rest base hc.frames hc.current hc.address
  have hf := finishHead_eval b
  have hread := (prefix_local readHead (6*word.length+5) B a ha).mono
    (show 896*B+(6*word.length+5) ≤ max D (904*B+10) by
      exact (by omega : 896*B+(6*word.length+5) ≤ 904*B+10).trans (Nat.le_max_right _ _))
  have hfinish := (prefix_local finishHead (2*(b.stacks 838).length+4) B b hb).mono
    (show 896*B+(2*(b.stacks 838).length+4) ≤ max D (904*B+10) by
      have h838 := hb 838
      exact (by omega : 896*B+(2*(b.stacks 838).length+4) ≤ 904*B+10).trans
        (Nat.le_max_right _ _))
  exact prefix_seq hr (hw.seq hf) hread
    (prefix_seq hw hf (hp.mono (Nat.le_max_left _ _)) hfinish)

/-- The list is a proof index for the already-emitted frame stack, not an
operational enumeration. This lemma composes actual callback traces and
preserves one fixed endpoint envelope throughout both representative passes. -/
theorem headLoop_resources (work : Code) (base C B D : ℕ)
    (I : List (List Bool) → Data → Prop)
    (step : ∀ word rest a, FrameCursor base (word::rest) a → I (word::rest) a →
      (∀ i, (a.stacks i).length ≤ B) →
      ∃ steps b, Eval work steps
        (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b ∧
        steps ≤ C ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
        b.stacks 843=List.replicate (base+rest.length) true ∧ I rest (finished b) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        PrefixBound work steps
          (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D)
    (words : List (List Bool)) (a : Data) (hc : FrameCursor base words a)
    (hi : I words a) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval (headLoop work) steps a b ∧ FrameCursor base [] b ∧ I [] b ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps ≤ 8*(words.map List.length).sum+(C+10)*words.length+1 ∧
      PrefixBound (headLoop work) steps a (max D (904*B+10)) := by
  induction words generalizing a with
  | nil =>
      have ht : a.regs 1=false := by simpa using hc.guard
      refine ⟨1,a,Eval.while_false ht,hc,hi,ha,by simp,⟨?_⟩⟩
      exact StructuredSpace.while_false_stack_bound (headBody work) 1 a ht
        (fun i => (ha i).trans ((by omega : B ≤ 904*B+10).trans (Nat.le_max_right _ _)))
        (compiled (headLoop work) 838 838) (siteAddress (headLoop work))
        (exitAddress (headLoop work)) (compiled_site (headLoop work) 838 838)
  | cons word rest ih =>
      obtain ⟨nt,b,hw,ht,h838,h840,h843,hI,hb,hprefix⟩ := step word rest a hc hi ha
      have hr := readHead_frames a word rest base hc.frames hc.current hc.address
      have hf := finishHead_eval b
      have hbody := hr.seq (hw.seq hf)
      have hnext := finished_cursor base rest b h840 h843
      obtain ⟨ns,c,hrest,hc',hi',hb',hcost,hspace⟩ :=
        ih (finished b) hnext hI (finished_bound b B hb)
      have htest : a.regs 1=true := by simpa using hc.guard
      refine ⟨_,c,Eval.while_true htest hbody hrest,hc',hi',hb',?_,⟨?_⟩⟩
      · rw [h838]
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
      · exact StructuredSpace.while_true_stack_bound htest hbody hrest 838 838
          (body_prefix work base B D nt a b word rest hc ha hw hb hprefix).bound
          hspace.bound (compiled (headLoop work) 838 838) (siteAddress (headLoop work))
          (exitAddress (headLoop work)) (compiled_site (headLoop work) 838 838)

theorem replay_resources_oai (work : Code) (base C B D : ℕ)
    (I : List (List Bool) → Data → Prop)
    (step : ∀ word rest a, FrameCursor base (word::rest) a → I (word::rest) a →
      (∀ i, (a.stacks i).length ≤ B) →
      ∃ steps b, Eval work steps
        (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b ∧
        steps ≤ C ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
        b.stacks 843=List.replicate (base+rest.length) true ∧ I rest (finished b) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        PrefixBound work steps
          (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D)
    (words : List (List Bool)) (a : Data)
    (hreps : a.stacks 837=suspendedFrames words)
    (haddress : a.stacks 845=List.replicate (base+words.length) true)
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hi : I words (tested (restartState a)))
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval (replay work) steps a b ∧ FrameCursor base [] b ∧ I [] b ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps+1 ≤ 18*B+8*(words.map List.length).sum+(C+10)*words.length+19 ∧
      PrefixBound (replay work) (steps+1) a (max D (914*B+18)) := by
  have hr := restart_eval a hscratch
  have ht := testFrames_eval (restartState a)
  have hs := restartState_bound a B ha
  have hc := restartState_cursor a base words hreps haddress hcurrent
  obtain ⟨steps,b,he,hcursor,hI,hb,hcost,hprefix⟩ :=
    headLoop_resources work base C B D I step words (tested (restartState a)) hc hi hs
  have hwhole := hr.seq (ht.seq he)
  have hrbound : restartCost a ≤ 18*B+16 := by
    have h840 := ha 840
    have h837 := ha 837
    have h843 := ha 843
    have h845 := ha 845
    unfold restartCost
    omega
  have hrestart := (prefix_local restart (restartCost a) B a ha).mono
    (show 896*B+restartCost a ≤ max D (914*B+18) by
      exact (by omega : 896*B+restartCost a ≤ 914*B+18).trans (Nat.le_max_right _ _))
  have htest := (prefix_local testFrames 1 B (restartState a) hs).mono
    (show 896*B+1 ≤ max D (914*B+18) by
      exact (by omega : 896*B+1 ≤ 914*B+18).trans (Nat.le_max_right _ _))
  have hloop := hprefix.mono (show max D (904*B+10) ≤ max D (914*B+18) from
    max_le_max_left D (by omega))
  have hall := prefix_seq hr (ht.seq he) hrestart (prefix_seq ht he htest hloop)
  refine ⟨_,b,hwhole,hcursor,hI,hb,by omega,⟨?_⟩⟩
  exact StructuredSpace.compiled_halt_stack_bound hwhole 838 838 hall.bound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources_oai
