-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:01:02.693573+00:00
-- url     : https://prove2.me/submissions/7bbed7fd-40bb-447b-aa92-743a50aa2155

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_visitor_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_ascend_leaf
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_nonleaf_rel_step
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_setup_rel_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_nonleaf_iteration_masterFrame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_setup_masterFrame

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFinite _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem representative_exists (hN : 0 < N) : Nonempty (Representative key) :=
  ⟨⟨⟨0, hN⟩, by intro j hj; exact (Nat.not_lt_zero _ hj).elim⟩⟩

theorem card_representative_pos (hN : 0 < N) : 0 < Nat.card (Representative key) := by
  let _ := representative_exists key hN
  exact Nat.card_pos

theorem assignment_word (h : ℕ) (i : Fin (2 ^ h)) :
    List.ofFn (assignmentEquiv h i) =
      ExecCNFTupleEnumeration.fixedBits h i := by
  have hv := congrArg List.Vector.toList (List.Vector.ofFn_get (Counters.wordEquiv h i))
  change List.ofFn (List.Vector.get (Counters.wordEquiv h i)) =
    List.Vector.toList (Counters.wordEquiv h i)
  simpa only [List.Vector.toList_ofFn] using hv

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
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

theorem conditional_true_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = true) (heval : StructuredCalls.Eval yes steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled yes inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled yes inputStack outputStack).entry)) intermediate →
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
    (b := a.withPC (some (StructuredCalls.entry yes (fun q => embed (some (.inl q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q)))

/-- A boundary invariant and a uniform actual-body prefix bound establish the
same space bound through any finite number of loop iterations. -/
theorem loop_stack_bound {r s : ℕ} (body : StructuredCalls.Cmd r s) (test : Fin r)
    (inputStack outputStack : Fin s) (I : StructuredCalls.State r s → Prop) (bound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound)
    (hpreserve : ∀ n a b, StructuredCalls.Eval body n a b → I a →
      a.regs test = true → I b)
    (hbody : ∀ n a b, StructuredCalls.Eval body n a b → I a → a.regs test = true →
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
          (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval (.while test body) steps a b) (ha : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  induction steps using Nat.strong_induction_on generalizing a b with
  | h steps ih =>
      cases heval with
      | while_false htest =>
          exact while_false_stack_bound body test a htest (hinitial a ha)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)
      | @while_true _ _ n m a middle b htest hb hw =>
          have hmiddle := hpreserve n a middle hb ha htest
          exact while_true_stack_bound htest hb hw inputStack outputStack
            (hbody n a middle hb ha htest) (ih m (by omega) hw hmiddle)
            _ _ _ (StructuredCalls.compiled_site _ inputStack outputStack)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Attained-signature DFS cardinalities and work

A level is indexed by its attained signatures, not its Boolean assignments or
an ambient rectangular range of raw row values. These finite types describe
visits mathematically; no family or product is materialized by these definitions.
The native encoded-frame traversal is a separate refinement obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS

open scoped BigOperators

/-- Exact cardinality of the partial-tuple domain. -/
theorem card_prefix (A : ℕ → Type*) [∀ i, Fintype (A i)] (depth : ℕ) :
    Fintype.card (Prefix A depth) = prefixCount (fun i => Fintype.card (A i)) depth := by
  rw [Fintype.card_pi]
  exact Fin.prod_univ_eq_prod_range (fun i => Fintype.card (A i)) depth

/-- Empty heads contribute one key, so every factor is at least one. -/
theorem prefixCount_le (K : ℕ → ℕ) {depth levels : ℕ} (hd : depth ≤ levels)
    (hK : ∀ i < levels, 1 ≤ K i) : prefixCount K depth ≤ prefixCount K levels := by
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hd)
  intro i hi _
  exact hK i (Finset.mem_range.mp hi)

/-- Uniform cost bound for all generator invocations in a DFS. -/
theorem generatorWork_le (K cost : ℕ → ℕ) (levels bound : ℕ)
    (hK : ∀ i < levels, 1 ≤ K i) (hc : ∀ i < levels, cost i ≤ bound) :
    generatorWork K cost levels ≤ levels * prefixCount K levels * bound := by
  calc
    generatorWork K cost levels ≤
        ∑ _i ∈ Finset.range levels, prefixCount K levels * bound := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul
        (prefixCount_le K (Nat.le_of_lt (Finset.mem_range.mp hi)) hK)
        (hc i (Finset.mem_range.mp hi))
    _ = levels * prefixCount K levels * bound := by
      simp [Nat.mul_assoc]

/-- The extra predecessor rescans square each head's assignment count, but
never take the product of the assignment counts across different heads. -/
theorem generatorWork_le_four_pow (K cost h : ℕ → ℕ) (levels poly hmax : ℕ)
    (hK : ∀ i < levels, 1 ≤ K i)
    (hc : ∀ i < levels, cost i ≤ poly * 4 ^ h i)
    (hh : ∀ i < levels, h i ≤ hmax) :
    generatorWork K cost levels ≤ poly * levels * prefixCount K levels * 4 ^ hmax := by
  have hb := generatorWork_le K cost levels (poly * 4 ^ hmax) hK
    (fun i hi => (hc i hi).trans
      (Nat.mul_le_mul_left poly (Nat.pow_le_pow_right (by decide) (hh i hi))))
  calc
    generatorWork K cost levels ≤ levels * prefixCount K levels * (poly * 4 ^ hmax) := hb
    _ = poly * levels * prefixCount K levels * 4 ^ hmax := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS
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

theorem Iteration.eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (h : Iteration p q n a b) : Eval (body p q) n a b := by
  cases h with
  | leaf hl hv ha => exact .ite_true hl (.seq hv ha)
  | fresh hl hp hb hf hd =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_true hf hd)))
  | duplicate hl hp hb hf hn =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_false hf hn)))
  | exhausted hl hp hb ha =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_false hb ha))

theorem Traversal.eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (h : Traversal p q n a b) : Eval (loop p q) n a b := by
  induction h with
  | done ha => exact .while_false ha
  | step ha hi _ ih => exact .while_true ha hi.eval ih

/-- Every prefix of the actual fixed controller loop is covered. The body
bound must include suspended frames, all current words, and every scratch
stack; it must be proved uniformly before using this composition rule. -/
theorem traversal_stack_bound {r s : ℕ} (p : Ports r) (q : Routines r s)
    (inputStack outputStack : Fin s) (I : State r s → Prop) (bound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound)
    (hpreserve : ∀ n a b, Eval (body p q) n a b → I a →
      a.regs p.active = true → I b)
    (hbody : ∀ n a b, Eval (body p q) n a b → I a → a.regs p.active = true →
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (compiled (body p q) inputStack outputStack) prefixSteps
          (a.withPC (some (compiled (body p q) inputStack outputStack).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ bound)
    {steps : ℕ} {a b : State r s} (ht : Traversal p q steps a b) (ha : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (loop p q) inputStack outputStack) prefixSteps
        (a.withPC (some (compiled (loop p q) inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound :=
  StructuredSpace.loop_stack_bound (body p q) p.active inputStack outputStack I bound
    hinitial hpreserve hbody ht.eval ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace QueryMasterFrame

theorem refl (a : Data) : QueryMasterFrame a a := ⟨fun _ _ => rfl⟩

theorem trans {a b c : Data} (hab : QueryMasterFrame a b) (hbc : QueryMasterFrame b c) :
    QueryMasterFrame a c := ⟨fun i hi => (hbc.word i hi).trans (hab.word i hi)⟩

end QueryMasterFrame

namespace QueryReady

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a) (hf : QueryMasterFrame a b) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf.word 128 (by decide)).trans h.ambient
    theta := (hf.word 78 (by decide)).trans h.theta
    modulus := (hf.word 194 (by decide)).trans h.modulus
    table := (hf.word 201 (by decide)).trans h.table
    width := (hf.word 202 (by decide)).trans h.width
    scalarZero := (hf.word 203 (by decide)).trans h.scalarZero
    degree := (hf.word 204 (by decide)).trans h.degree
    one := (hf.word 207 (by decide)).trans h.one
    minus := (hf.word 211 (by decide)).trans h.minus
    precision := (hf.word 212 (by decide)).trans h.precision
    order := (hf.word 243 (by decide)).trans h.order
    zero := (hf.word 280 (by decide)).trans h.zero
    code := (hf.word 281 (by decide)).trans h.code
    clauses := (hf.word 700 (by decide)).trans h.clauses
    rows := (hf.word 701 (by decide)).trans h.rows
    rowCount := (hf.word 704 (by decide)).trans h.rowCount
    markedIndex := (hf.word 705 (by decide)).trans h.markedIndex
    markedFlag := (hf.word 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf.word 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf.word 708 (by decide))).trans h.indexWidth
    highMask := (hf.word 702 (by decide)).trans h.highMask
    highBits := (hf.word 703 (by decide)).trans h.highBits
    outer := (hf.word 858 (by decide)).trans h.outer
    inner := (hf.word 857 (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf.word 130 (by decide)).trans h.colors
    nodes := (hf.word 131 (by decide)).trans h.nodes
    typeWidth := (hf.word 132 (by decide)).trans h.typeWidth
    positive := (hf.word 710 (by decide)).trans h.positive
    negative := (hf.word 711 (by decide)).trans h.negative
    sourceWidth := (hf.word 140 (by decide)).trans h.sourceWidth
    power := (hf.word 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf.word 138 (by decide)).trans h.radius
    offset := (hf.word 139 (by decide)).trans h.offset
    metadata := (hf.word 135 (by decide)).trans h.metadata
    plans := (hf.word 136 (by decide)).trans h.plans
    inverses := (hf.word 713 (by decide)).trans h.inverses
    negatives := (hf.word 714 (by decide)).trans h.negatives
    differences := (hf.word 715 (by decide)).trans h.differences
    ringWidth := (hf.word 717 (by decide)).trans h.ringWidth
    rowWidth := (hf.word 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf.word 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈masterPorts := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf.word _ hm]
    exact h.cacheCaps p hp
  · rw [hf.word 128 (by decide)]
    exact h.ambientCap
  · rw [hf.word 207 (by decide)]
    exact h.oneCap

end QueryReady

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

theorem Trace.single {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddMonoid M] (weight : Event key levels → M)
    {event a b} (h : Step key levels event a b) : Trace weight (weight event) a b := by
  simpa using Trace.step h (.refl b : Trace weight 0 b b)

theorem Trace.trans {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddMonoid M] {weight : Event key levels → M}
    {a b c x y} (h : Trace weight x a b) (h' : Trace weight y b c) :
    Trace weight (x + y) a c := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => simpa only [add_assoc] using Trace.step hs (ih h')

private theorem sum_tail_succ {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : Fin n → M) (c : Fin n) :
    (∑ i : Fin n with c.val ≤ i.val, f i) =
      f c + ∑ i : Fin n with c.val + 1 ≤ i.val, f i := by
  classical
  have hs : (Finset.univ.filter fun i : Fin n => c.val ≤ i.val) =
      insert c (Finset.univ.filter fun i : Fin n => c.val + 1 ≤ i.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases he : i = c
      · exact Or.inl he
      · exact Or.inr (by have hn : i.val ≠ c.val := fun h => he (Fin.ext h); omega)
    · rintro (rfl | h) <;> omega
  rw [hs, Finset.sum_insert (by simp)]

private theorem sum_representatives {M : Type*} [AddCommMonoid M]
    (key : (d : ℕ) → Fin (N d) → κ d) (depth : ℕ)
    (f : Representatives key depth → M) :
    (∑ i : Fin (N depth),
      if h : ∀ j, j < i → key depth j ≠ key depth i then f ⟨i, h⟩ else 0) =
      ∑ rep : Representatives key depth, f rep := by
  classical
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    split_ifs with h
    · exact (hi ⟨⟨i, h⟩, rfl⟩).elim
    · rfl
  · intro i
    rw [dite_eq_left i.property]

/-- A complete subtree starts at its first candidate and returns to the
parent's next candidate. This includes the terminal exhaustion test. -/
theorem subtree_trace (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M)
    (remaining depth : ℕ) (h : depth + remaining = levels)
    (ancestors : Prefix (Representatives key) depth) :
    Trace weight (subtreeTotal key levels weight remaining depth h ancestors)
      (enter key levels depth (by omega) ancestors)
      (leave key levels depth (by omega) ancestors) := by
  classical
  induction remaining generalizing depth with
  | zero =>
      have he : depth = levels := by omega
      subst depth
      simpa [subtreeTotal] using Trace.single weight (Step.leaf ancestors)
  | succ remaining ih =>
      let d : Fin levels := ⟨depth, by omega⟩
      let child : Representatives key depth → M := fun rep =>
        subtreeTotal key levels weight remaining (depth + 1) (by omega) (Fin.snoc ancestors rep)
      let charge : Fin (N depth) → M := fun i => weight (.candidate d ancestors i) +
        if hi : ∀ j, j < i → key depth j ≠ key depth i then child ⟨i, hi⟩ else 0
      have scan : ∀ left c, c + left = N depth →
          Trace weight ((∑ i : Fin (N depth) with c ≤ i.val, charge i) +
            weight (.exhausted d ancestors))
            (.scan d ancestors c) (leave key levels depth (by omega) ancestors) := by
        intro left
        induction left with
        | zero =>
            intro c hc
            have he : c = N depth := by omega
            subst c
            have hs : (∑ i : Fin (N depth) with N depth ≤ i.val, charge i) = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              have hn := (Finset.mem_filter.mp hi).2
              omega
            rw [hs, zero_add]
            exact Trace.single weight (.exhausted d ancestors)
        | succ left ihscan =>
            intro c hc
            let i : Fin (N depth) := ⟨c, by omega⟩
            have hn := ihscan (c + 1) (by omega)
            rw [show c = i.val from rfl, sum_tail_succ charge i]
            by_cases hf : ∀ j, j < i → key depth j ≠ key depth i
            · let rep : Representatives key depth := ⟨i, hf⟩
              have ht := ih (depth + 1) (by omega) (Fin.snoc ancestors rep)
              rw [leave_snoc key levels depth d.isLt ancestors rep] at ht
              have hh := (Trace.single weight (Step.fresh d ancestors rep)).trans (ht.trans hn)
              simpa only [charge, dite_eq_left hf, child, add_assoc] using hh
            · have hh := (Trace.single weight (Step.duplicate d ancestors i hf)).trans hn
              simpa only [charge, dite_eq_right hf, add_zero, add_assoc] using hh
      have hs := scan (N depth) 0 (by omega)
      simp only [Nat.zero_le, Finset.filter_true, charge, Finset.sum_add_distrib] at hs
      rw [sum_representatives] at hs
      rw [enter_internal key levels depth d.isLt ancestors]
      change Trace weight
        (((∑ i : Fin (N depth), weight (.candidate d ancestors i)) +
          weight (.exhausted d ancestors)) + ∑ rep, child rep)
        (.scan d ancestors 0) _
      rw [add_right_comm] at hs
      exact hs

private theorem sum_snoc {M : Type*} [AddCommMonoid M]
    (key : (d : ℕ) → Fin (N d) → κ d) (depth : ℕ)
    (f : Prefix (Representatives key) (depth + 1) → M) :
    (∑ ancestors : Prefix (Representatives key) depth,
      ∑ rep : Representatives key depth, f (Fin.snoc ancestors rep)) = ∑ ancestors, f ancestors := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact (Fin.snocEquiv (fun i : Fin (depth + 1) => Representatives key i.val)).sum_comp f

private theorem sum_subtreeTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M)
    (remaining depth : ℕ) (h : depth + remaining = levels) :
    (∑ ancestors : Prefix (Representatives key) depth,
      subtreeTotal key levels weight remaining depth h ancestors) =
        (∑ d ∈ Finset.Ico depth levels, levelTotal key levels weight d) +
          ∑ ancestors : Prefix (Representatives key) levels, weight (.leaf ancestors) := by
  induction remaining generalizing depth with
  | zero =>
      have he : depth = levels := by omega
      subst depth
      simp [subtreeTotal]
  | succ remaining ih =>
      have hd : depth < levels := by omega
      change (∑ ancestors : Prefix (Representatives key) depth,
        (((∑ i : Fin (N depth), weight (.candidate ⟨depth, hd⟩ ancestors i)) +
          weight (.exhausted ⟨depth, hd⟩ ancestors)) +
        ∑ rep : Representatives key depth,
          subtreeTotal key levels weight remaining (depth + 1) (by omega)
            (Fin.snoc ancestors rep))) = _
      rw [Finset.sum_add_distrib, sum_snoc, ih (depth + 1) (by omega),
        Finset.sum_eq_sum_Ico_succ_bot hd]
      simp only [levelTotal, dite_eq_left hd]
      simp only [add_assoc]

/-- Every candidate, exhausted generator and leaf in the attained-prefix
domain is visited exactly once: this holds for arbitrary additive weights. -/
theorem complete_trace (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) :
    Trace weight (eventTotal key levels weight)
      (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) .halt := by
  have hs := sum_subtreeTotal key levels weight levels 0 (by omega)
  rw [Fintype.sum_subsingleton _ (fun i => Fin.elim0 i)] at hs
  have ht := subtree_trace key levels weight levels 0 (by omega) (fun i => Fin.elim0 i)
  simpa only [hs, ← Finset.range_eq_Ico, eventTotal, leave] using ht

theorem Iterations.finish {r s : ℕ} {p : SignatureTupleProgram.Ports r}
    {q : SignatureTupleProgram.Routines r s} {n a b}
    (ht : Iterations p q n a b) (hb : b.regs p.active = false) :
    SignatureTupleProgram.Traversal p q (n + 1) a b := by
  induction ht with
  | refl => exact .done hb
  | step ha hi _ ih =>
      simpa only [Nat.add_assoc] using SignatureTupleProgram.Traversal.step ha hi (ih hb)

/-- Transfer the complete semantic path to actual controller iterations.
The same evaluations carry both the time charge and the callback accumulator.
Concrete routines must prove the local `hstep` clause. -/
theorem Trace.nativeIterations {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddCommMonoid M] {weight : Event key levels → ℕ × M}
    {total start finish} (ht : Trace weight total start finish)
    {r s : ℕ} (p : SignatureTupleProgram.Ports r) (q : SignatureTupleProgram.Routines r s)
    (Rel : Cursor key levels → M → StructuredProgram.State r s → Prop)
    (hstep : ∀ event before after acc a, Step key levels event before after → Rel before acc a →
      a.regs p.active = true ∧ ∃ n b, SignatureTupleProgram.Iteration p q n a b ∧
        Rel after (acc + (weight event).2) b ∧ n + 1 ≤ (weight event).1)
    (acc : M) (a : StructuredProgram.State r s) (ha : Rel start acc a) :
    ∃ n b, Iterations p q n a b ∧ Rel finish (acc + total.2) b ∧ n ≤ total.1 := by
  induction ht generalizing acc a with
  | refl => exact ⟨0, a, .refl a, by simpa using ha, by simp⟩
  | @step event before middle after tail hs _ ih =>
      obtain ⟨ha', n, b, hi, hb, hn⟩ := hstep event before middle acc a hs ha
      obtain ⟨m, c, hc, hrel, hm⟩ := ih (acc + (weight event).2) b hb
      refine ⟨n + m + 1, c, .step ha' hi hc, ?_, ?_⟩
      · simpa only [Prod.snd_add, add_assoc] using hrel
      · change n + m + 1 ≤ (weight event).1 + tail.1
        omega

/-- One actual controller traversal realizes the full weighted event sum.
The bound includes its final guard test; setup and compilation are charged by
`SignatureTupleProgram.program_trace` when this traversal is embedded. -/
theorem native_complete (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → ℕ × M)
    {r s : ℕ} (p : SignatureTupleProgram.Ports r) (q : SignatureTupleProgram.Routines r s)
    (Rel : Cursor key levels → M → StructuredProgram.State r s → Prop)
    (hstep : ∀ event before after acc a, Step key levels event before after → Rel before acc a →
      a.regs p.active = true ∧ ∃ n b, SignatureTupleProgram.Iteration p q n a b ∧
        Rel after (acc + (weight event).2) b ∧ n + 1 ≤ (weight event).1)
    (hhalt : ∀ acc a, Rel .halt acc a → a.regs p.active = false)
    (acc : M) (a : StructuredProgram.State r s)
    (ha : Rel (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) acc a) :
    ∃ n b, SignatureTupleProgram.Traversal p q n a b ∧
      Rel .halt (acc + (eventTotal key levels weight).2) b ∧
      n ≤ (eventTotal key levels weight).1 + 1 := by
  obtain ⟨n, b, ht, hb, hn⟩ :=
    (complete_trace key levels weight).nativeIterations p q Rel hstep acc a ha
  exact ⟨n + 1, b, ht.finish (hhalt _ _ hb), hb, Nat.add_le_add_right hn 1⟩

/-- The exact invocation-domain bound, before any uniform polynomial
estimate. Full tuple callbacks are charged on the same event sum. -/
theorem eventTotal_le (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    (weight : Event key levels → ℕ) (cost : ℕ → ℕ) (leafCost : ℕ)
    (hc : ∀ (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val),
      (∑ i : Fin (N depth.val), weight (.candidate depth ancestors i)) +
        weight (.exhausted depth ancestors) ≤ cost depth.val)
    (hl : ∀ ancestors, weight (.leaf ancestors) ≤ leafCost) :
    eventTotal key levels weight ≤
      generatorWork (fun d => Fintype.card (Representatives key d)) cost levels +
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * leafCost := by
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro depth hd
    have hd' : depth < levels := Finset.mem_range.mp hd
    simp only [levelTotal, dite_eq_left hd']
    calc
      _ ≤ ∑ _ancestors : Prefix (Representatives key) depth, cost depth :=
        Finset.sum_le_sum fun ancestors _ => hc ⟨depth, hd'⟩ ancestors
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
          card_prefix (Representatives key) depth]
  · calc
      _ ≤ ∑ _ancestors : Prefix (Representatives key) levels, leafCost :=
        Finset.sum_le_sum fun ancestors _ => hl ancestors
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
          card_prefix (Representatives key) levels]

theorem candidate_cost_le (n poly : ℕ) (hn : 1 ≤ n) :
    (∑ i : Fin n, poly * (i.val + 1)) + poly ≤ 2 * poly * (n * n) := by
  have hs : (∑ i : Fin n, poly * (i.val + 1)) ≤ n * (poly * n) := by
    calc
      _ ≤ ∑ _i : Fin n, poly * n :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left poly i.isLt
      _ = _ := by simp
  have hp : poly ≤ poly * (n * n) := Nat.le_mul_of_pos_right _ (by positivity)
  nlinarith

/-- The stronger runtime scale needs only one square of each head's raw
assignment count, multiplied by the attained-key product. -/
theorem eventTotal_cost_le (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels poly leafCost hmax : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax) :
    eventTotal key levels (costWeight key levels poly leafCost) ≤
      (2 * poly) * levels *
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * 4 ^ hmax +
      prefixCount (fun d => Fintype.card (Representatives key d)) levels * leafCost := by
  have hpos : ∀ d, 1 ≤ Fintype.card (Representatives key d) := by
    intro d
    have hp : 0 < Fintype.card (Representatives key d) := by
      simpa only [Nat.card_eq_fintype_card] using
        AttainedSignatures.card_representative_pos (key d) (pow_pos (by omega) _)
    omega
  have hc : ∀ (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val),
      (∑ i : Fin (2 ^ h depth.val),
        costWeight key levels poly leafCost (.candidate depth ancestors i)) +
      costWeight key levels poly leafCost (.exhausted depth ancestors) ≤
        (2 * poly) * 4 ^ h depth.val := by
    intro depth ancestors
    have he : 2 ^ h depth.val * 2 ^ h depth.val = 4 ^ h depth.val := by
      rw [← mul_pow]; rfl
    simpa only [costWeight, he] using candidate_cost_le (2 ^ h depth.val) poly
      (Nat.one_le_pow _ _ (by omega))
  exact (eventTotal_le key levels _ (fun d => (2 * poly) * 4 ^ h d) leafCost hc
    (fun _ => le_rfl)).trans (Nat.add_le_add_right
      (generatorWork_le_four_pow _ _ h levels (2 * poly) hmax
        (fun d _ => hpos d) (fun _ _ => le_rfl) hh) _)

theorem eventTotal_callbackWeight (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (value : Prefix (Representatives key) levels → M) :
    eventTotal key levels (callbackWeight key levels value) = ∑ ancestors, value ancestors := by
  simp [eventTotal, levelTotal, callbackWeight]

theorem eventTotal_map (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M A : Type*} [AddCommMonoid M] [AddCommMonoid A]
    (map : M →+ A) (weight : Event key levels → M) :
    eventTotal key levels (fun event => map (weight event)) =
      map (eventTotal key levels weight) := by
  unfold eventTotal
  rw [map_add, map_sum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro depth _
  unfold levelTotal
  split_ifs <;> simp only [map_sum, map_add, map_zero]

/-- Cost and exact callback value share the same weighted traversal. -/
theorem eventTotal_pair (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (cost : Event key levels → ℕ)
    (value : Prefix (Representatives key) levels → M) :
    eventTotal key levels (fun event => (cost event, callbackWeight key levels value event)) =
      (eventTotal key levels cost, ∑ ancestors, value ancestors) := by
  apply Prod.ext
  · exact (eventTotal_map key levels (AddMonoidHom.fst ℕ M) _).symm
  · exact (eventTotal_map key levels (AddMonoidHom.snd ℕ M) _).symm.trans
      (eventTotal_callbackWeight key levels value)

/-- A concrete controller satisfying the local cursor invariant runs every
attained tuple callback once, with the squared-head cost on that same run.
This is the native integration lemma; its local clauses must be discharged
by the actual probe, frame, loader and callback commands. -/
theorem native_complete_bounded (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels poly leafCost hmax : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax)
    {M : Type*} [AddCommMonoid M] (value : Prefix (Representatives key) levels → M)
    {r s : ℕ} (p : SignatureTupleProgram.Ports r) (q : SignatureTupleProgram.Routines r s)
    (Rel : Cursor key levels → M → StructuredProgram.State r s → Prop)
    (hstep : ∀ event before after acc a, Step key levels event before after → Rel before acc a →
      a.regs p.active = true ∧ ∃ n b, SignatureTupleProgram.Iteration p q n a b ∧
        Rel after (acc + callbackWeight key levels value event) b ∧
        n + 1 ≤ costWeight key levels poly leafCost event)
    (hhalt : ∀ acc a, Rel .halt acc a → a.regs p.active = false)
    (acc : M) (a : StructuredProgram.State r s)
    (ha : Rel (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) acc a) :
    ∃ n b, SignatureTupleProgram.Traversal p q n a b ∧
      Rel .halt (acc + ∑ ancestors, value ancestors) b ∧
      n ≤ (2 * poly) * levels *
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * 4 ^ hmax +
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * leafCost + 1 := by
  obtain ⟨n, b, ht, hb, hn⟩ := native_complete key levels
    (fun event => (costWeight key levels poly leafCost event,
      callbackWeight key levels value event)) p q Rel hstep hhalt acc a ha
  rw [eventTotal_pair] at hb hn
  refine ⟨n, b, ht, hb, hn.trans ?_⟩
  exact Nat.add_le_add_right (eventTotal_cost_le h key levels poly leafCost hmax hh) 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleBranchSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix composition for the actual exhausted and leaf branches of the
attained-signature controller. The component executions are the installed
probe, visitor and ascent commands, and every caller stack is covered. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative

theorem leaf_body_eval (load visit : Cmd 40 896)
    (a b c : State 40 896) (nv na : ℕ)
    (hl : a.regs controllerPorts.leaf = true)
    (hv : Eval visit nv a b) (hasc : Eval (ascendWith load) na b c) :
    Eval (body controllerPorts (assembleRoutines load candidateCall visit))
      (nv + na + 1) a c :=
  (Iteration.leaf hl hv hasc).eval

/-- Visiting one attained tuple and ascending share the same space cap,
including the outer branch instruction and final compiled halt. -/
theorem leaf_body_prefix_bound (load visit : Cmd 40 896)
    (a b c : State 40 896) (nv na D : ℕ)
    (hl : a.regs controllerPorts.leaf = true)
    (hv : Eval visit nv a b) (hasc : Eval (ascendWith load) na b c)
    (hvs : ∀ p q, p ≤ nv → Trace (compiled visit 0 0) p
      (a.withPC (some (compiled visit 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D)
    (has : ∀ p q, p ≤ na → Trace (compiled (ascendWith load) 0 0) p
      (b.withPC (some (compiled (ascendWith load) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D) :
    ∀ p q, p ≤ nv + na + 2 →
      Trace (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines load candidateCall visit)) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ D := by
  have hseq := hv.seq hasc
  have hsseq := StructuredSpace.sequence_stack_bound hv hasc 0 0 hvs has
    (compiled (.seq visit (ascendWith load)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have he := leaf_body_eval load visit a b c nv na hl hv hasc
  have hwhole := StructuredSpace.conditional_true_stack_bound
    (no := .seq (probeWith candidateCall)
      (.ite controllerPorts.available
        (.ite controllerPorts.fresh (descendWith load) advanceCandidateCommand)
        (ascendWith load))) hl hseq 0 0 hsseq
    (compiled (body controllerPorts (assembleRoutines load candidateCall visit)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hhalt := StructuredSpace.compiled_halt_stack_bound he 0 0 hwhole
  intro p q hpq hq i
  exact hhalt p q (by omega) hq i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage


/-- The query snapshot contains every actual loader master. -/
theorem source_master_queryMaster (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i∈QueryTupleState.masterPorts := by
  simp only [SignatureHeadLoader.masters, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem source_frame_of_queryFrame (base : LeafHeadSetupProgram.Data)
    (a b : State 40 896)
    (ha : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : QueryTupleState.QueryMasterFrame a b) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  exact (hf.word (SignatureHeadLoader.lowStacks i) (source_master_queryMaster i hi)).trans
    (ha.stored i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem cursor_enabled (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ)
    (cursor : Cursor key levels) (a : State 40 896)
    (ha : CursorStorage h key levels base cursor a)
    (hactive : a.regs controllerPorts.active=true) :
    ∃ event after, Step key levels event cursor after := by
  classical
  cases ha with
  | @scan depth ancestors candidate a hs =>
    by_cases hc : candidate < 2 ^ h depth.val
    · let c : Fin (2^h depth.val) := ⟨candidate,hc⟩
      by_cases hf : ∀ j, j < c → key depth.val j ≠ key depth.val c
      · exact ⟨_,_,Step.fresh depth ancestors ⟨c,hf⟩⟩
      · exact ⟨_,_,Step.duplicate depth ancestors c hf⟩
    · have he : candidate=2^h depth.val := by have hb := hs.range; omega
      subst candidate
      exact ⟨_,_,Step.exhausted depth ancestors⟩
  | leaf hs => exact ⟨_,_,Step.leaf _⟩
  | halt hf => simp only [hf,Bool.false_eq_true] at hactive


theorem Boundary.cursorStorage {s : ProducedSource} {F : ℕ}
    {cursor : Cursor s.key s.input.r} {a : State 40 896}
    (ha : Boundary s F cursor a) :
    CursorStorage s.headSize s.key s.input.r s.base cursor a := by
  cases ha with
  | scan hs => exact .scan hs.toScanStorage
  | leaf hs => exact .leaf hs.toLeafStorage
  | halt hs => exact .halt hs.active

theorem Boundary.wordBound {s : ProducedSource} {F : ℕ}
    {cursor : Cursor s.key s.input.r} {a : State 40 896}
    (ha : Boundary s F cursor a) : WordBound F a := by
  cases ha with
  | scan hs => exact hs.bound
  | leaf hs => exact hs.bound
  | halt hs => exact hs.bound

theorem queryMaster_persistent (i : Fin 896) (hi : i∈QueryTupleState.masterPorts) :
    PersistentPort i := by
  simp only [QueryTupleState.masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact ⟨by decide,by decide,by decide⟩

theorem query_frame_of_persistent (a b : State 40 896)
    (hf : ∀ i,PersistentPort i → b.stacks i=a.stacks i) :
    QueryTupleState.QueryMasterFrame a b :=
  ⟨fun i hi => hf i (queryMaster_persistent i hi)⟩

theorem leafStorage_frame (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ)
    (ancestors : Prefix (Representatives key) levels) (a b : State 40 896)
    (ha : LeafStorage h key levels base ancestors a)
    (hf : ∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i)
    (hr : ∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i)
    (hc : ∀ i∈currentHeadPorts,b.stacks i=[]) :
    LeafStorage h key levels base ancestors b := by
  refine ⟨⟨ha.depth_le,?_,?_,?_,?_,?_⟩,?_,hc⟩
  · exact (hf 836 (by decide)).trans ha.cursors
  · exact (hf 837 (by decide)).trans ha.representatives
  · exact (hf 842 (by decide)).trans ha.heads
  · exact (hf 845 (by decide)).trans ha.address
  · exact (hr 36 (by decide)).trans ha.active
  · exact (hr 37 (by decide)).trans ha.leaf

theorem leafBoundary_frame (s : ProducedSource) (F : ℕ)
    (ancestors : Prefix (Representatives s.key) s.input.r) (a b : State 40 896)
    (ha : LeafBoundary s F ancestors a) (hb : WordBound F b)
    (hm : QueryTupleState.QueryMasterFrame a b)
    (hf : ∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i)
    (hr : ∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i)
    (hc : ∀ i∈currentHeadPorts,b.stacks i=[])
    (hz : s.input.r=0 → b.stacks 649=a.stacks 649) : LeafBoundary s F ancestors b := by
  exact ⟨leafStorage_frame s.headSize s.key s.input.r s.base ancestors a b
    ha.toLeafStorage hf hr hc,hb,source_frame_of_queryFrame s.masters a b ha.masters hm,
    fun hzero => (hz hzero).trans (ha.zero_address649 hzero)⟩

/-- At completed traversal, the actual root flag is false and low649 again
contains the original node base for the next finite-difference pair. -/
theorem Rel.halted {s : ProducedSource} {F r Q n d : ℕ}
    {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ}
    {acc : Truncated (q.p.model.O q.p.t) q.J} {a : State 40 896}
    (ha : Rel s F q node H high E U P .halt acc a) :
    a.regs controllerPorts.active=false ∧ a.stacks 649=unary s.base := by
  cases ha.boundary with
  | halt hb => exact ⟨hb.active,hb.address649⟩

/-- Any active concrete cursor has one of the proved semantic steps. The
numeric counter bound excludes both overshoot and a stuck scan state. -/
theorem Rel.enabled {s : ProducedSource} {F r Q n d : ℕ}
    {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ}
    {cursor : Cursor s.key s.input.r} {acc : Truncated (q.p.model.O q.p.t) q.J}
    {a : State 40 896} (ha : Rel s F q node H high E U P cursor acc a)
    (hactive : a.regs controllerPorts.active=true) :
    ∃ event after, Step s.key s.input.r event cursor after :=
  cursor_enabled s.headSize s.key s.input.r s.base cursor a ha.boundary.cursorStorage hactive

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Complete runs of the fixed attained-signature controller. The retained
boundary cap is separate from transient prefix storage and measured time. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource
open SignatureTupleComplete

/-- Paid setup, a proved actual traversal, and the final compiled halt share
one trace and one all-stack prefix bound. -/
theorem setup_traversal_prefix (ports : Ports 40) (code : Routines 40 896)
    (ns nt bound : ℕ) (a b c : State 40 896)
    (setup : Eval code.setup ns a b) (traversal : Traversal ports code nt b c)
    (hs : QueryExecution.PrefixBound code.setup ns a bound)
    (ht : QueryExecution.PrefixBound (loop ports code) nt b bound) :
    QueryExecution.PrefixBound (SignatureTupleProgram.command ports code) (ns+nt+1) a bound := by
  have hseq := QueryExecution.prefix_seq setup traversal.eval hs ht
  constructor
  exact StructuredSpace.compiled_halt_stack_bound (.seq setup traversal.eval) 838 838 hseq.bound

/-- Source port selectors only choose external readback; they do not change
any instruction or stack in an internal command trace. -/
theorem prefix_ports (code : Cmd 40 896) (steps bound : ℕ) (a : State 40 896)
    (h : QueryExecution.PrefixBound code steps a bound) (input output : Fin 896) :
    ∀ p z,p ≤ steps → BitProgram.Trace (compiled code input output) p
      (a.withPC (some (compiled code input output).entry)) z →
      ∀ i,(z.stacks i).length ≤ bound := by
  intro p z hp hz i
  exact h.bound p z hp hz i

/-- Determinism transfers a locally exhibited iteration's bound to every
actual body derivation used by the compiled while-loop prefix theorem. -/
theorem traversal_prefix_of_iterations (ports : Ports 40) (code : Routines 40 896)
    (I : State 40 896 → Prop) (D : ℕ)
    (hbound : ∀ a,I a → WordBound D a)
    (hrealized : ∀ a,I a → a.regs ports.active=true → ∃ steps b,
      Iteration ports code steps a b ∧ I b ∧
        QueryExecution.PrefixBound (body ports code) (steps+1) a D)
    {steps : ℕ} {a b : State 40 896} (ht : Traversal ports code steps a b) (ha : I a) :
    QueryExecution.PrefixBound (loop ports code) steps a D := by
  have preserve : ∀ n a b,Eval (body ports code) n a b → I a →
      a.regs ports.active=true → I b ∧ QueryExecution.PrefixBound (body ports code) (n+1) a D := by
    intro n a b he ha active
    obtain ⟨n',b',hit,hb,hp⟩ := hrealized a ha active
    have htime := StreamResources.eval_steps_eq (0 : Fin 896) 0 he hit.eval
    have hout := he.final_unique (0 : Fin 896) hit.eval
    subst n'
    subst b'
    exact ⟨hb,hp⟩
  constructor
  apply traversal_stack_bound ports code 838 838 I D hbound
  · intro n a b he ha active
    exact (preserve n a b he ha active).1
  · intro n a b he ha active elapsed z hprefix hz i
    exact (preserve n a b he ha active).2.bound elapsed z (by omega) hz i
  · exact ht
  · exact ha

/-- The enriched cursor relation supplies a uniform whole-loop prefix
invariant from actual locally realized steps; no traversal-time term is used
as a space bound. -/
theorem rel_loop_prefix (s : ProducedSource) (F D leafCost : ℕ) (hFD : F ≤ D)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
    (hstep : ∀ event before after acc a,Step s.key s.input.r event before after →
      Rel s F q node H high E U P before acc a →
      a.regs controllerPorts.active=true ∧ ∃ steps b,
        Iteration controllerPorts routines steps a b ∧
        Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
        steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
        QueryExecution.PrefixBound (body controllerPorts routines) (steps+1) a D)
    {cursor : Cursor s.key s.input.r} {acc : Truncated (q.p.model.O q.p.t) q.J}
    {steps : ℕ} {a b : State 40 896} (ht : Traversal controllerPorts routines steps a b)
    (ha : Rel s F q node H high E U P cursor acc a) :
    QueryExecution.PrefixBound (loop controllerPorts routines) steps a D := by
  let I : State 40 896 → Prop := fun state => ∃ cursor total,Rel s F q node H high E U P cursor total state
  apply traversal_prefix_of_iterations controllerPorts routines I D
  · intro state hstate i
    obtain ⟨cursor,total,hstate⟩ := hstate
    exact (hstate.boundary.wordBound i).trans hFD
  · intro state hstate active
    obtain ⟨cursor,total,hstate⟩ := hstate
    obtain ⟨event,after,hnext⟩ := hstate.enabled active
    obtain ⟨_,n,out,hit,hout,_,hprefix⟩ := hstep event cursor after total state hnext hstate
    exact ⟨n,out,hit,⟨after,_,hout⟩,hprefix⟩
  · exact ht
  · exact ⟨_,_,ha⟩

/-- Relational traversal composes exact physical frames without storing a
trace or a family of states at runtime. -/
theorem traversal_masterFrame (ports : Ports 40) (code : Routines 40 896)
    (I : State 40 896 → Prop)
    (hstep : ∀ n a b,I a → a.regs ports.active=true → Iteration ports code n a b →
      I b ∧ QueryTupleState.QueryMasterFrame a b)
    {steps : ℕ} {a b : State 40 896} (ht : Traversal ports code steps a b) (ha : I a) :
    QueryTupleState.QueryMasterFrame a b := by
  induction ht with
  | done _ => exact .refl _
  | step active hit _ ih =>
    obtain ⟨hb,hf⟩ := hstep _ _ _ ha active hit
    exact hf.trans (ih hb)

/-- No new representative is selected while reconstructing a leaf. -/
theorem emitted_word (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (ancestors : Prefix (Representatives s.key) s.input.r) (g : Fin s.input.r) :
    QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g
      (emittedRepresentatives s q H owner head facts ancestors)=
        ExecCNFTupleEnumeration.fixedBits (s.headSize g.val) (ancestors g).val.val := by
  unfold QueryVisitorHead.representativeWord emittedRepresentatives
  let e : (Moments.Head (fun v : ResidualEmbedding.Free H =>
      head s.input.node v.val) g → Bool) ≃ (Fin (s.headSize g.val) → Bool) :=
    BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (selectedHeads s.input.n s.input.rows s.input.low (s.base+g.val))
    (HeadIdentifierProgram.chosenIds_bound _ _) (HeadIdentifierProgram.chosenIds_nodup _ _)
    (facts.selected g)
  change List.ofFn (e (e.symm (AttainedSignatures.assignmentEquiv
    (s.headSize g.val) (ancestors g).val)))=_
  rw [e.apply_symm_apply]
  exact AttainedSignatures.assignment_word (s.headSize g.val) (ancestors g).val

/-- An attained leaf now invokes the actual two-pass visitor and the actual
return controller. All arithmetic and head-loading services are instantiated. -/
theorem leaf_step (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hpositive : 0 < s.input.r)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (ancestors : Prefix (Representatives s.key) s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (ha : Rel s F q s.input.node H high E U M (.leaf ancestors) acc a) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q s.input.node H high E U M (leave s.key s.input.r s.input.r le_rfl ancestors)
        (acc+emittedValue s q H E U high owner head facts ancestors) b ∧
      steps+1 ≤ QueryVisitorSemantics.visitorCost s q F S Z B height+eventPolynomial s F ∧
      QueryExecution.PrefixBound (body controllerPorts routines) (steps+1) a
        (max (prefixEnvelope s F) (QueryVisitorSemantics.visitorSpace s q F B)) ∧
      QueryTupleState.QueryMasterFrame a b := by
  cases hboundary : ha.boundary with
  | leaf hl =>
    have hreps : a.stacks 837=suspendedFrames (List.ofFn (fun g =>
        QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g
          (emittedRepresentatives s q H owner head facts ancestors))).reverse := by
      rw [show a.stacks 837=representativeFrames s.headSize s.key s.input.r ancestors
        from hl.representatives]
      simp only [representativeFrames,representativeWords,emitted_word]
    obtain ⟨nv,b,hvisit,hqr,hacc,hframe,hb,hports,hregs,hcurrent,htv,hpv⟩ :=
      QueryVisitorSemantics.visitor_run s q H E U high owner head facts caps
        (emittedRepresentatives s q H owner head facts ancestors)
        (fun g => hheads g.val g.isLt) a ha.query ha.accumulator hl.bound hl.masters
        hreps hl.address (hl.cleared 838 (by decide))
    have hleaf := leafBoundary_frame s F ancestors a b hl hb hframe hports hregs hcurrent
      (fun hz => by omega)
    obtain ⟨na,c,hasc,hc,hta,hpa,hfa⟩ := ascend_leaf s F cap ancestors b hleaf
    have hframea := query_frame_of_persistent b c hfa
    have hr : Rel s F q s.input.node H high E U M
        (leave s.key s.input.r s.input.r le_rfl ancestors)
        (acc+emittedValue s q H E U high owner head facts ancestors) c :=
      ⟨hc,hqr.frame hframea,hacc.frame (hfa 851 ⟨by decide,by decide,by decide⟩)⟩
    refine ⟨hl.active,nv+na+1,c,Iteration.leaf hl.leaf hvisit hasc,hr,by omega,?_,
      hframe.trans hframea⟩
    constructor
    unfold routines
    apply SignatureTupleBranchSpace.leaf_body_prefix_bound loadHead QueryVisitorProgram.visitor
      a b c nv na _ hl.leaf hvisit hasc
    · intro elapsed cfg he ht i
      exact (hpv.bound elapsed cfg (by omega) ht i).trans (Nat.le_max_right _ _)
    · intro elapsed cfg he ht i
      exact (hpa elapsed cfg (by omega) ht i).trans (Nat.le_max_left _ _)

/-- Every semantic event is implemented by the fixed concrete controller.
No local evaluator or successful-run premise remains in this theorem. -/
theorem actual_step (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hpositive : 0 < s.input.r)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (step : Step s.key s.input.r event before after)
    (ha : Rel s F q s.input.node H high E U M before acc a) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q s.input.node H high E U M after
        (acc+callbackWeight s.key s.input.r (emittedValue s q H E U high owner head facts) event) b ∧
      steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) (leafCost s q F S Z B height) event ∧
      QueryExecution.PrefixBound (body controllerPorts routines) (steps+1) a (runSpace s q F B) ∧
      QueryTupleState.QueryMasterFrame a b := by
  by_cases hleaf : ∃ ancestors,event=Event.leaf ancestors
  · obtain ⟨ancestors,rfl⟩ := hleaf
    cases step with
    | leaf ancestors =>
      exact leaf_step s q H E U high owner head facts caps cap hpositive hheads ancestors acc a ha
  · have hnon : ∀ ancestors,event≠Event.leaf ancestors := by
      intro ancestors he
      exact hleaf ⟨ancestors,he⟩
    obtain ⟨hactive,steps,b,hit,hb,ht,hp⟩ :=
      nonleaf_rel_step s F (leafCost s q F S Z B height) cap q s.input.node H high E U M
        (emittedValue s q H E U high owner head facts) event before after acc a step ha hnon
    refine ⟨hactive,steps,b,hit,hb,ht,?_,?_⟩
    · constructor
      intro elapsed cfg helapsed htrace i
      exact (hp elapsed cfg helapsed htrace i).trans (Nat.le_max_left _ _)
    · exact nonleaf_iteration_masterFrame s F (leafCost s q F S Z B height)
        cap event before after step ha.boundary hnon hit

/-- The complete positive-depth run executes each attained tuple once.
The actual84-master frame, count-accumulator meaning, time and every source
prefix all refer to this same fixed program execution. Numerical/source
certificates are instantiated by the actual produced-input constructors. -/
theorem positive_run_resources_oai (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hpositive : 0 < s.input.r)
    (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q s.input.node H high E U M a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryTupleState.QueryReady q s.input.node H high E U M b ∧
      QueryTupleState.PairAccumulatorMeaning q
        (acc+tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)) b ∧
      WordBound F b ∧ b.stacks 649=unary s.base ∧ QueryTupleState.QueryMasterFrame a b ∧
      steps+1 ≤ eventPolynomial s F+(2*eventPolynomial s F)*s.input.r*
        tupleCount s.key s.input.r*4^height+tupleCount s.key s.input.r*leafCost s q F S Z B height+2 ∧
      ∀ elapsed cfg,elapsed ≤ steps+1 → BitProgram.Trace SignatureTupleComplete.program elapsed
        (a.withPC (some SignatureTupleComplete.program.entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ runSpace s q F B := by
  let value := emittedValue s q H E U high owner head facts
  let cost := leafCost s q F S Z B height
  have localStep : ∀ event before after acc a,Step s.key s.input.r event before after →
      Rel s F q s.input.node H high E U M before acc a →
      a.regs controllerPorts.active=true ∧ ∃ steps b,
        Iteration controllerPorts routines steps a b ∧
        Rel s F q s.input.node H high E U M after
          (acc+callbackWeight s.key s.input.r value event) b ∧
        steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) cost event := by
    intro event before after acc a he ha
    obtain ⟨active,steps,b,hit,hb,ht,_,_⟩ :=
      actual_step s q H E U high owner head facts caps cap hpositive hheads event before after acc a he ha
    exact ⟨active,steps,b,hit,hb,ht⟩
  obtain ⟨ns,b,hs,hb,hts,hspaces⟩ := setup_rel_run s F cap q s.input.node H high E U M acc a
    hbound hm hz hquery hacc
  obtain ⟨nt,c,htr,hc,htt⟩ := native_complete_bounded s.headSize s.key s.input.r
    (eventPolynomial s F) cost height hheads value controllerPorts routines
    (Rel s F q s.input.node H high E U M) localStep (fun _ _ h => h.halted.1) acc b hb
  have hFD : F ≤ runSpace s q F B := by
    have hp : F ≤ prefixEnvelope s F := by unfold prefixEnvelope; omega
    exact hp.trans (Nat.le_max_left _ _)
  have hpLoop := rel_loop_prefix s F (runSpace s q F B) cost hFD q s.input.node H high E U M value
    (fun event before after acc a he ha => by
      obtain ⟨active,steps,b,hit,hb,ht,hp,_⟩ :=
        actual_step s q H E U high owner head facts caps cap hpositive hheads event before after acc a he ha
      exact ⟨active,steps,b,hit,hb,ht,hp⟩) htr hb
  let I : State 40 896 → Prop := fun state =>
    ∃ cursor total,Rel s F q s.input.node H high E U M cursor total state
  have hpreserve : ∀ steps a b,I a → a.regs controllerPorts.active=true →
      Iteration controllerPorts routines steps a b → I b ∧ QueryTupleState.QueryMasterFrame a b := by
    intro steps a b hI hactive hit
    obtain ⟨cursor,total,ha⟩ := hI
    obtain ⟨event,after,he⟩ := ha.enabled hactive
    obtain ⟨_,n,out,hi,ho,_,_,hf⟩ :=
      actual_step s q H E U high owner head facts caps cap hpositive hheads event cursor after total a he ha
    have heq := hit.eval.final_unique (0 : Fin 896) hi.eval
    subst out
    exact ⟨⟨after,_,ho⟩,hf⟩
  have hloopFrame := traversal_masterFrame controllerPorts routines I hpreserve htr ⟨_,_,hb⟩
  have hpSetup : QueryExecution.PrefixBound routines.setup ns a (runSpace s q F B) := by
    constructor
    intro elapsed cfg he ht i
    exact (hspaces elapsed cfg (by omega) ht i).trans (Nat.le_max_left _ _)
  have he : Eval SignatureTupleComplete.command (ns+nt) a c := .seq hs htr.eval
  have hp := setup_traversal_prefix controllerPorts routines ns nt (runSpace s q F B)
    a b c hs htr hpSetup hpLoop
  have combine (i t p work leaf : ℕ) (hi : i+1 ≤ p) (ht : t ≤ work+leaf+1) :
      i+t+1 ≤ p+work+leaf+2 := by omega
  exact ⟨ns+nt,c,he,compiled_halt_trace he 837 851,hc.query,hc.accumulator,
    hc.boundary.wordBound,hc.halted.2,(setup_masterFrame s F cap a hbound hm hz hs).trans hloopFrame,
    combine _ _ _ _ _ hts htt,prefix_ports SignatureTupleComplete.command _ _ a hp 837 851⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources_oai
