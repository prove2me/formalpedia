-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:42:28.992348+00:00
-- url     : https://prove2.me/submissions/957fb40e-763f-4fad-826b-f9f5f92a570a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect_NodeBoundary_sourceBank
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect_node_run
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
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

theorem clearOne_eval (i : Fin 896) (a : Data) :
    Eval (clearOne i) (2 * (a.stacks i).length + 3) a (cleared i a) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem clearMany_eval (ps : List (Fin 896)) (a : Data) :
    Eval (clearMany ps) (clearCost ps a) a (clearedMany ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih => exact (clearOne_eval p a).seq (ih _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed indexed traversal of the actual framed node table. The installed
worker is a real command; its measured, frame-preserving execution remains an
explicit producer obligation. Neither the index nor a jet is semantic advice. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_store (regs : Fin 40 → Bool) (a b : Store) (src dst : Fin 768)
    (hsd : src ≠ dst) (hst : src ≠ 305) (htd : (305 : Fin 768) ≠ dst)
    (htmp : a.temporary = []) (hout : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.copy_run src dst 305 0 1 hsd hst htd
    (by decide) regs (tapes a) (by simpa using htmp)
  apply Eval.call
  simpa only [state,ListRegisterProgram.Run,StructuredProgram.State.withPC,hout] using he

theorem clear_store (regs : Fin 40 → Bool) (a b : Store) (src : Fin 768)
    (hout : Function.update (tapes a) src [] = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.clear_run src (0 : Fin 40) 1 regs (tapes a)
  apply Eval.call
  simpa only [state,ListRegisterProgram.Run,StructuredProgram.State.withPC,clearStacks,hout] using he

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingNodeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid traversal of the actual framed node table. The remaining cursor and
unary index are physical stacks, and the decoded node is transferred to the
original factor port. No list of semantic nodes is manufactured by the machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

theorem initialize_eval (regs : Fin 40 → Bool) (s : Store) :
    Eval initNodes (initializeCost s) (state regs s)
      (state (readRegs regs 0 1 none) (initialized s)) := by
  let a := {s with source := []}
  let b := {a with payload := []}
  let c := {b with temporary := []}
  let d := {c with index := []}
  let e := {d with node := []}
  let rr := readRegs regs 0 1 none
  have hrr : readRegs rr 0 1 none = rr := by
    funext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [rr, readRegs, h0, h1]
  have h1 := clear_store regs s a 301 (by simp [a])
  have h2 := clear_store rr a b 302 (by simp [b])
  have h3 := clear_store rr b c 305 (by simp [c])
  have h4 := clear_store rr c d 307 (by simp [d])
  have h5 := clear_store rr d e 78 (by simp [e])
  have h6 := copy_store rr e (initialized s) 300 301
    (by decide) (by decide) (by decide) rfl
    (by simp [copyStacks, initialized, e, d, c, b, a, tapes])
  rw [hrr] at h2 h3 h4 h5 h6
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  · simp [initNodes]
  · simp [initializeCost, a, b, c, d, e, tapes]
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes

theorem call_eval (c : Cmd 40 768) (a : Data) (b : LowData) (steps : ℕ)
    (he : Eval c steps (low a) b) :
    Eval (call c) (steps+1) a (installed a b) :=
  eval_liftCommand_from_state c 301 78 id lowPort a Function.injective_id
    (Fin.castAdd_injective 768 128) he

theorem initialize_eval (a : Data) :
    Eval initializeNodes (initializeCost a) a (initialized a) := by
  have he := RingNodeSetup.initialize_eval (low a).regs (RingNodeSetup.storeOf (low a))
  rw [RingNodeSetup.state_storeOf] at he
  exact (call_eval _ a _ _ he).seq (NodeReadoutSpace.clearMany_eval _ _)

theorem initializedLow_frame (a : Data) (i : Fin 768)
    (h301 : i≠301) (h302 : i≠302) (h305 : i≠305) (h307 : i≠307) (h78 : i≠78) :
    (initializedLow a).stacks i=(low a).stacks i := by
  have hs := congrArg (fun x : LowData => x.stacks i) (RingNodeSetup.state_storeOf (low a))
  rw [←hs]
  simp only [initializedLow, OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
    RingNodeSetup.initialized, OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes,
    h301,h302,h305,h307,h78,ite_false]

theorem initialized_frame (a : Data) (i : Fin 896)
    (hi : i∉[301,302,305,307,78,850,851,863]) :
    (initialized a).stacks i=a.stacks i := by
  have hn : i∉[850,851,863] := by simp_all
  rw [initialized,NodeReadoutSpace.clearedMany_stack,ite_eq_right hn]
  by_cases hlow : i.val<768
  · let j : Fin 768 := ⟨i.val,hlow⟩
    have hj : lowPort j=i := Fin.ext rfl
    rw [←hj,installed_low,initializedLow_frame]
    · rfl
    all_goals intro h; have hh := congrArg lowPort h; rw [hj] at hh; exact hi (by simp [hh,lowPort])
  · exact installed_high a _ i (by omega)

theorem initialized_words (a : Data) :
    (initialized a).stacks 301=a.stacks 300 ∧
    (initialized a).stacks 302=[] ∧ (initialized a).stacks 305=[] ∧
    (initialized a).stacks 307=[] ∧ (initialized a).stacks 78=[] ∧
    (initialized a).stacks 850=[] ∧ (initialized a).stacks 851=[] ∧
    (initialized a).stacks 863=[] := by
  have hlo (i : Fin 896) (hi : i.val<768) : (installed a (initializedLow a)).stacks i=
      (initializedLow a).stacks ⟨i.val,hi⟩ := by
    have hh : lowPort ⟨i.val,hi⟩=i := Fin.ext rfl
    simpa only [hh] using installed_low a (initializedLow a) ⟨i.val,hi⟩
  simp only [initialized,NodeReadoutSpace.clearedMany_stack]
  simp only [List.mem_cons,Fin.reduceEq,or_self,or_false,ite_true, if_true,ite_false,
    List.not_mem_nil,or_true]
  rw [hlo 301 (by decide),hlo 302 (by decide),hlo 305 (by decide),
    hlo 307 (by decide),hlo 78 (by decide)]
  simp [initializedLow,RingNodeSetup.initialized,RingNodeSetup.storeOf,
    OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes,
    low,projectState,lowPort]


theorem initialized_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    ∀ i,((initialized a).stacks i).length≤ B := by
  intro i
  by_cases hi : i∈[301,302,305,307,78,850,851,863]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [(initialized_words a).1,(initialized_words a).2.1,
      (initialized_words a).2.2.1,(initialized_words a).2.2.2.1,
      (initialized_words a).2.2.2.2.1,(initialized_words a).2.2.2.2.2.1,
      (initialized_words a).2.2.2.2.2.2.1,(initialized_words a).2.2.2.2.2.2.2,
      List.length_nil]
    all_goals first | exact hb 300 | exact Nat.zero_le _
  · rw [initialized_frame a i hi]
    exact hb i

theorem initializeCost_le (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length≤ B) :
    initializeCost a≤23*B+30 := by
  have hclear : NodeReadoutSpace.clearCost [850,851,863] (installed a (initializedLow a))≤6*B+9 := by
    simp only [NodeReadoutSpace.clearCost,NodeReadoutSpace.cleared]
    simp only [Function.update_of_ne (by decide : (851 : Fin 896)≠850),
      Function.update_of_ne (by decide : (863 : Fin 896)≠851),
      Function.update_of_ne (by decide : (863 : Fin 896)≠850)]
    rw [installed_high a _ 850 (by decide),installed_high a _ 851 (by decide),
      installed_high a _ 863 (by decide)]
    have := hb 850; have := hb 851; have := hb 863
    omega
  have h301 := hb 301; have h302 := hb 302; have h305 := hb 305
  have h307 := hb 307; have h78 := hb 78; have h300 := hb 300
  unfold initializeCost RingNodeSetup.initializeCost RingNodeSetup.storeOf low projectState at *
  simp only [lowPort] at *
  change 2*((a.stacks 301).length+(a.stacks 302).length+(a.stacks 305).length+
      (a.stacks 307).length+(a.stacks 78).length)+7*(a.stacks 300).length+20+1+
      NodeReadoutSpace.clearCost [850,851,863] (installed a (initializedLow a))≤23*B+30
  omega


end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open FactorTableBudgets

theorem compact_le (A : ℕ) : A+1 ≤ compactCap A := by
  unfold compactCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

private theorem sourceSize_large (A : ℕ) : A+1 ≤ sourceSize A := by
  unfold sourceSize
  omega

private theorem scalarCap_large (A : ℕ) : sourceSize A+1 ≤ scalarCap A := by
  have h : sourceSize A+1 ≤ (sourceSize A+1)^10 := Nat.le_self_pow (by decide) _
  unfold scalarCap
  omega

theorem original_le_scalar (A : ℕ) : A+1 ≤ scalarCap A := by
  have h1 := sourceSize_large A
  have h2 := scalarCap_large A
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem guardCursor_eval (a : Data) : Eval guardCursor 1 a (guarded a) :=
  .base (.atom (.peek 301 37 38) a)

theorem guarded_test (a : Data) (nodes : List (List Bool))
    (hc : a.stacks 301=Encoding.encodeList id nodes) :
    (guarded a).regs 37 = !nodes.isEmpty ∧ (guarded a).regs 38=true := by
  cases nodes <;> simp [guarded,readRegs,hc,Encoding.encodeList]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeLoopSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed node loop consumes the producer's framed cursor. Each actual
node execution supplies its own emitted coefficient word; no uniform choice
of byte representatives across register states is required. The indexed
invariant carries the complete retained query context between nodes. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeLoopSpace

open BitProgram StructuredCalls

/-- The actual initializer derives the first physical loop boundary from
the produced framed master, including an empty coefficient stream. -/
theorem initialized_boundary (a : Data) (nodes : List (List Bool)) (B : ℕ)
    (hn : a.stacks 300 = Encoding.encodeList id nodes)
    (hb : ∀ port, (a.stacks port).length ≤ B) :
    let start := QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a)
    start.stacks 301 = Encoding.encodeList id nodes ∧
      start.stacks 307 = [] ∧ start.stacks 863 = [] ∧
      start.regs 37 = !nodes.isEmpty ∧ start.regs 38 = true ∧
      ∀ port, (start.stacks port).length ≤ B := by
  dsimp only
  have hw := QueryAssembler.Nodes.initialized_words a
  have hc : (QueryAssembler.Nodes.initialized a).stacks 301 =
      Encoding.encodeList id nodes := hw.1.trans hn
  have hg := QueryNodeFinish.guarded_test (QueryAssembler.Nodes.initialized a) nodes hc
  exact ⟨hc, hw.2.2.2.1, hw.2.2.2.2.2.2.2, hg.1, hg.2,
    QueryAssembler.Nodes.initialized_bound a B hb⟩

/-- Retained ring words, cache masters and high-assignment data outside the
listed physical writes pass through node initialization unchanged. -/
theorem initialized_frame (a : Data) (port : Fin 896)
    (hp : port ∉ [301,302,305,307,78,850,851,863]) :
    (QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a)).stacks port =
      a.stacks port :=
  QueryAssembler.Nodes.initialized_frame a port hp

/-- Induct on the number of physical node records still to be read. The
output list is a proof witness only; the machine retains the flat stream863.
All component prefixes share one cap, independent of the number of nodes. -/
theorem loop_eval_prefix (nodes : List (List Bool))
    (I : ℕ → Data → Prop) (P : ℕ → List Bool → Prop) (B D C : ℕ)
    (hboundary : ∀ i a, I i a →
      a.stacks 301 = Encoding.encodeList id (nodes.drop i) ∧
      a.stacks 307 = List.replicate i true ∧
      a.regs 37 = !(nodes.drop i).isEmpty ∧
      ∀ port, (a.stacks port).length ≤ B)
    (hnode : ∀ i a, i < nodes.length → I i a →
      ∃ steps b bits, steps ≤ C ∧
        Eval QueryStreamProgram.nodeBody steps a b ∧ I (i + 1) b ∧ P i bits ∧
        b.stacks 863 = a.stacks 863 ++ bits ∧
        ∀ p q, p ≤ steps →
          Trace (compiled QueryStreamProgram.nodeBody 0 0) p
            (a.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port, (q.stacks port).length ≤ D)
    (remaining index : ℕ) (a : Data) (hcount : index + remaining = nodes.length)
    (ha : I index a) :
    ∃ (steps : ℕ) (b : Data) (outputs : List (List Bool)), steps ≤ remaining * (C + 1) + 1 ∧
      Eval QueryStreamProgram.nodeLoop steps a b ∧ I nodes.length b ∧
      outputs.length = remaining ∧
      (∀ j (hj : j < outputs.length), P (index + j) outputs[j]) ∧
      b.stacks 863 = a.stacks 863 ++ outputs.flatten ∧
      ∀ p q, p ≤ steps →
        Trace (compiled QueryStreamProgram.nodeLoop 0 0) p
          (a.withPC (some (compiled QueryStreamProgram.nodeLoop 0 0).entry)) q →
        ∀ port, (q.stacks port).length ≤ max B D := by
  induction remaining generalizing index a with
  | zero =>
    have hi : index = nodes.length := by omega
    subst index
    obtain ⟨_, _, hg, hb⟩ := hboundary nodes.length a ha
    have hg' : a.regs 37 = false := by simpa using hg
    have he : Eval QueryStreamProgram.nodeLoop 1 a a := .while_false hg'
    refine ⟨1, a, [], by simp, he, ha, rfl, ?_, by simp, ?_⟩
    · intro j hj
      simp at hj
    · exact StructuredSpace.while_false_stack_bound QueryStreamProgram.nodeBody 37 a hg'
        (fun port => (hb port).trans (Nat.le_max_left _ _))
        (compiled QueryStreamProgram.nodeLoop 0 0)
        (siteAddress QueryStreamProgram.nodeLoop) (exitAddress QueryStreamProgram.nodeLoop)
        (compiled_site QueryStreamProgram.nodeLoop 0 0)
  | succ remaining ih =>
    have hi : index < nodes.length := by omega
    obtain ⟨_, _, hg, _⟩ := hboundary index a ha
    have hnonempty : nodes.drop index ≠ [] := by
      intro he
      have hl := congrArg List.length he
      simp only [List.length_drop, List.length_nil] at hl
      omega
    have hg' : a.regs 37 = true := by
      rw [hg, List.isEmpty_eq_false_iff.mpr hnonempty]
      rfl
    obtain ⟨first, middle, bits, hfirst, he, hm, hbits, hout, hprefix⟩ := hnode index a hi ha
    obtain ⟨rest, final, outputs, hrest, ht, hf, hlen, hp, ho, hs⟩ :=
      ih (index + 1) middle (by omega) hm
    have hwhole : Eval QueryStreamProgram.nodeLoop (first + rest + 1) a final :=
      .while_true hg' he ht
    refine ⟨first + rest + 1, final, bits :: outputs, ?_, hwhole, hf, ?_, ?_, ?_, ?_⟩
    · simp only [Nat.succ_mul]
      omega
    · simp [hlen]
    · intro j hj
      cases j with
      | zero => simpa only [Nat.add_zero, List.getElem_cons_zero] using hbits
      | succ j =>
        have hj' : j < outputs.length := by simpa using hj
        simpa only [List.getElem_cons_succ, Nat.add_succ, Nat.succ_add] using hp j hj'
    · rw [ho, hout, List.flatten_cons, List.append_assoc]
    · exact StructuredSpace.while_true_stack_bound hg' he ht 0 0
        (fun p q hle htrace port =>
          (hprefix p q hle htrace port).trans (Nat.le_max_right _ _)) hs
        (compiled QueryStreamProgram.nodeLoop 0 0)
        (siteAddress QueryStreamProgram.nodeLoop) (exitAddress QueryStreamProgram.nodeLoop)
        (compiled_site QueryStreamProgram.nodeLoop 0 0)

/-- The physical guard only reads the cursor. Its single instruction cannot
enlarge either an active stack or a preserved caller word. -/
theorem guard_prefix_bound (a : Data) (B : ℕ)
    (ha : ∀ port, (a.stacks port).length ≤ B) :
    ∀ p q, p ≤ 1 →
      Trace (compiled QueryNodeFinish.guardCursor 0 0) p
        (a.withPC (some (compiled QueryNodeFinish.guardCursor 0 0).entry)) q →
      ∀ port, (q.stacks port).length ≤ B := by
  intro p q hp hq port
  have hc : p = 0 ∨ p = 1 := by omega
  rcases hc with rfl | rfl
  · cases hq
    exact ha port
  · have heq := trace_same_length_unique hq
      (compiled_trace (QueryNodeFinish.guardCursor_eval a) 0 0)
    rw [heq]
    exact ha port

/-- Paid cursor initialization and the real initial guard precede the same
node loop. Dirty entry buffers are charged by the existing initializer, and
the accumulated stream starts empty before the first node is evaluated. -/
theorem nodes_eval_prefix (nodes : List (List Bool))
    (I : ℕ → Data → Prop) (P : ℕ → List Bool → Prop) (B D C : ℕ)
    (hboundary : ∀ i a, I i a →
      a.stacks 301 = Encoding.encodeList id (nodes.drop i) ∧
      a.stacks 307 = List.replicate i true ∧
      a.regs 37 = !(nodes.drop i).isEmpty ∧
      ∀ port, (a.stacks port).length ≤ B)
    (hnode : ∀ i a, i < nodes.length → I i a →
      ∃ steps b bits, steps ≤ C ∧
        Eval QueryStreamProgram.nodeBody steps a b ∧ I (i + 1) b ∧ P i bits ∧
        b.stacks 863 = a.stacks 863 ++ bits ∧
        ∀ p q, p ≤ steps →
          Trace (compiled QueryStreamProgram.nodeBody 0 0) p
            (a.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port, (q.stacks port).length ≤ D)
    (a : Data) (ha : ∀ port, (a.stacks port).length ≤ B)
    (hi : I 0 (QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a))) :
    ∃ (steps : ℕ) (b : Data) (outputs : List (List Bool)),
      steps ≤ 23 * B + nodes.length * (C + 1) + 32 ∧
      Eval QueryStreamProgram.nodes steps a b ∧
      I nodes.length b ∧ outputs.length = nodes.length ∧
      (∀ j (hj : j < outputs.length), P j outputs[j]) ∧
      b.stacks 301 = [false] ∧ b.stacks 307 = List.replicate nodes.length true ∧
      b.regs 37 = false ∧ b.stacks 863 = outputs.flatten ∧
      (∀ port, (b.stacks port).length ≤ B) ∧
      ∀ p q, p ≤ steps →
        Trace (compiled QueryStreamProgram.nodes 0 0) p
          (a.withPC (some (compiled QueryStreamProgram.nodes 0 0).entry)) q →
        ∀ port, (q.stacks port).length ≤ max (919 * B + 31) D := by
  let initialized := QueryAssembler.Nodes.initialized a
  let start := QueryNodeFinish.guarded initialized
  obtain ⟨steps, b, outputs, hc, he, hI, hl, hp, ho, hs⟩ :=
    loop_eval_prefix nodes I P B D C hboundary hnode nodes.length 0 start (by simp) hi
  have hinit := QueryAssembler.Nodes.initialize_eval a
  have hguard := QueryNodeFinish.guardCursor_eval initialized
  have htotal : Eval QueryStreamProgram.nodes
      (QueryAssembler.Nodes.initializeCost a + (1 + steps)) a b :=
    hinit.seq (hguard.seq he)
  have hcost := QueryAssembler.Nodes.initializeCost_le a B ha
  have hstart : ∀ port, (initialized.stacks port).length ≤ B :=
    QueryAssembler.Nodes.initialized_bound a B ha
  have hsmall : B ≤ 919 * B + 31 := by omega
  have hguardspace := guard_prefix_bound initialized B hstart
  have hguardloop := StructuredSpace.sequence_stack_bound hguard he 0 0
    (fun p q hle ht port =>
      (hguardspace p q hle ht port).trans (hsmall.trans (Nat.le_max_left _ _)))
    (fun p q hle ht port => (hs p q hle ht port).trans (max_le_max_right D hsmall))
    (compiled (.seq QueryNodeFinish.guardCursor QueryStreamProgram.nodeLoop) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hinitspace : ∀ p q, p ≤ QueryAssembler.Nodes.initializeCost a →
      Trace (compiled QueryAssembler.Nodes.initializeNodes 0 0) p
        (a.withPC (some (compiled QueryAssembler.Nodes.initializeNodes 0 0).entry)) q →
      ∀ port, (q.stacks port).length ≤ max (919 * B + 31) D := by
    intro p q hp hq port
    have hb := StructuredSpace.local_stack_bound
      (compiled QueryAssembler.Nodes.initializeNodes 0 0)
      (steps := 23 * B + 30) (StreamResources.dataBits_le_mul _ ha)
      p q (hp.trans hcost) hq port
    exact hb.trans ((by omega : 896 * B + (23 * B + 30) ≤ 919 * B + 31).trans
      (Nat.le_max_left _ _))
  have hwhole := StructuredSpace.sequence_stack_bound hinit (hguard.seq he) 0 0
    hinitspace hguardloop (compiled QueryStreamProgram.nodes 0 0)
    (siteAddress QueryStreamProgram.nodes) (exitAddress QueryStreamProgram.nodes)
    (compiled_site QueryStreamProgram.nodes 0 0)
  obtain ⟨hcursor, hindex, htest, hb⟩ := hboundary nodes.length b hI
  refine ⟨_, b, outputs, ?_, htotal, hI, hl,
    ?_, ?_, hindex, ?_, ?_, hb, hwhole⟩
  · omega
  · simpa only [Nat.zero_add] using hp
  · simpa [Encoding.encodeList] using hcursor
  · simpa using htest
  · have hz : start.stacks 863 = [] :=
      (QueryAssembler.Nodes.initialized_words a).2.2.2.2.2.2.2
    simpa only [hz, List.nil_append] using ho

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeLoopSpace
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

/-- The retained cap has fixed degree36. No input-dependent exponent is
introduced by the depth, assignment counter or repeated head reconstruction. -/
theorem retainedEnvelope_polynomial (B A : ℕ) :
    retainedEnvelope B A ≤ (100000*20000^6+10050)*(A+B+2)^36 := by
  let X := A+B+2
  change retainedEnvelope B A ≤ (100000*20000^6+10050)*X^36
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h1 : X ≤ X^36 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 36)
  have h2 : X^2 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h6 : X^6 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h0 : 1 ≤ X^36 := one_le_pow₀ hX
  have hb : B ≤ X := by dsimp [X]; omega
  have hb1 : B+1 ≤ X := by dsimp [X]; omega
  have hb2 : B+2 ≤ X := by dsimp [X]; omega
  have ha : A ≤ X := by dsimp [X]; omega
  have hscan : scannerEnvelope B ≤ (100000*20000^6)*X^36 := by
    unfold scannerEnvelope
    rw [mul_pow,←pow_mul]
    change 100000*(20000^6*(B+2)^36) ≤ _
    calc
      _ ≤ 100000*(20000^6*X^36) := by gcongr
      _=_ := (Nat.mul_assoc _ _ _).symm
  have ho : 10000*(B+2)^6 ≤ 10000*X^36 := Nat.mul_le_mul_left 10000 ((Nat.pow_le_pow_left hb2 6).trans h6)
  have hf : 6*B*(B+1) ≤ 6*X^36 := by
    calc
      _ ≤ 6*X*X := by gcongr
      _=6*X^2 := by rw [pow_two,Nat.mul_assoc]
      _ ≤ 6*X^36 := Nat.mul_le_mul_left 6 h2
  have hs : B*B ≤ X^36 := (Nat.mul_le_mul hb hb).trans (by simpa only [pow_two] using h2)
  have hA := ha.trans h1
  have hB := hb.trans h1
  have hB1 := hb1.trans h1
  unfold retainedEnvelope
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingNodeMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual ring producer determines both the factor cutoff and the native
arithmetic cutoff. Its framed node stream uses the same increasing indices as
the physical cursor and the interpolation nodes. -/

noncomputable section

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram.PreparedSource

theorem nodeBits_drop (t d Q : ℕ) (i : Fin Q) :
    (nodeBits t d Q).drop i.val =
      RingProgram.flat (RingNodeProgram.nodeCode t d (i.val+1)) ::
        (nodeBits t d Q).drop (i.val+1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [nodeBits, LeafRingSetupProgram.nodeWords]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TupleRunBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The same compact endpoint cap supports the actual tuple controller and
its visitor. Transient scanner/reload work is bounded separately; none of it
is fed back into the retained frame cap between pairs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open SignatureTupleSource SignatureTupleComplete SignatureTupleLoader

private theorem square_le_compact (T : ℕ) : T^2 ≤ HeadSumBudgets.compactCap T := by
  have hp : T*T ≤ FactorTableBudgets.payloadEnvelope T := by
    unfold FactorTableBudgets.payloadEnvelope
    calc
      T*T = T*T*1 := (Nat.mul_one _).symm
      _ ≤ T*T*(2*(T+T+T)+2*T*(2*T)+2) := Nat.mul_le_mul_left _ (by omega)
  unfold HeadSumBudgets.compactCap
  rw [pow_two]
  omega

/-- The fixed degree36 scanner and both persistent frame banks fit the
already chosen compact head cap, including at ambient size zero. -/
theorem retained_le_compact (B A : ℕ) (hB : B ≤ A) :
    retainedEnvelope B 0 ≤ QueryHeadBudgets.compact A := by
  have hsource : 100*(A+2)^2 ≤ QueryHeadBudgets.sourceSize A+1 := by
    have h := Nat.mul_le_mul_right (100*(A+2)^2+2) (show 1 ≤ A+1 by omega)
    unfold QueryHeadBudgets.sourceSize
    omega
  have hpower : (A+2)^36 ≤ (A+2)^40 := Nat.pow_le_pow_right (by omega) (by decide)
  have hscalar : (QueryHeadBudgets.sourceSize A+1)^20 ≤ (QueryHeadBudgets.scalarCap A)^2 := by
    unfold QueryHeadBudgets.scalarCap
    rw [mul_pow,←pow_mul]
    norm_num
  calc
    retainedEnvelope B 0 ≤ (100000*20000^6+10050)*(B+2)^36 := by
      simpa only [Nat.zero_add] using retainedEnvelope_polynomial B 0
    _ ≤ (100000*20000^6+10050)*(A+2)^36 := by gcongr
    _ ≤ 100^20*(A+2)^40 := Nat.mul_le_mul (by norm_num) hpower
    _ = (100*(A+2)^2)^20 := by rw [mul_pow,←pow_mul]
    _ ≤ (QueryHeadBudgets.sourceSize A+1)^20 := Nat.pow_le_pow_left hsource 20
    _ ≤ (QueryHeadBudgets.scalarCap A)^2 := hscalar
    _ ≤ QueryHeadBudgets.compact A := square_le_compact _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeSourceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete capacities for the actual addressed node source. Its reference
snapshot is bounded only by retained query words, independently of caller
scratch, node index and the actual bootstrap cache witness. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram
open QueryNodeEvaluation

/-- Ordinary cache and output arrays fit the same already fixed compact
cap; this bound contains no callback count or transient budget. -/
theorem compact_capacity (A : ℕ) : 20*(A+1)^4 ≤ QueryHeadBudgets.compact A := by
  have hp : (A+1)^4 ≤ (A+2)^6 :=
    (Nat.pow_le_pow_left (by omega : A+1≤A+2) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  apply le_trans (b := SignatureTupleComplete.retainedEnvelope A 0) ?_
    (TupleRunBudgets.retained_le_compact A A (Nat.le_refl A))
  have hm : 20*(A+1)^4 ≤ 10000*(A+2)^6 := Nat.mul_le_mul (by decide) hp
  unfold SignatureTupleComplete.retainedEnvelope
  omega

/-- The full ordered output array fits before any node cache is produced. -/
theorem array_capacity (Q J d t A : ℕ)
    (hQ : Q≤A) (hJ : J≤A) (hd : d≤A) (ht : t≤A) :
    Q*(J*(d*SubexpLiftRing.baseWidth 3 t))≤QueryHeadBudgets.compact A ∧
    Q≤QueryHeadBudgets.compact A := by
  have hword : Q*(J*(d*SubexpLiftRing.baseWidth 3 t))≤A*(A*(A*(2*A))) := by
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  have hp : 2*A^4≤20*(A+1)^4 := Nat.mul_le_mul (by decide)
    (Nat.pow_le_pow_left (by omega) 4)
  have hA : A≤QueryHeadBudgets.compact A := by
    have h := QueryHeadBudgets.original_le_scalar A
    have hh := HeadSumBudgets.compact_le (QueryHeadBudgets.scalarCap A)
    change _ ≤ QueryHeadBudgets.compact A at hh
    omega
  refine ⟨?_,hQ.trans hA⟩
  apply hword.trans
  calc
    A*(A*(A*(2*A))) = 2*A^4 := by ring
    _ ≤ 20*(A+1)^4 := hp
    _ ≤ QueryHeadBudgets.compact A := compact_capacity A

/-- The authentic scalar bank supplies capacity before entering the node
loop; this theorem has no later cache or source witness argument. -/
theorem model_capacity (m : Circuit.Model) (A : ℕ) (hvalues : ∀ i,m.val i≤A) :
    (m.val 21)*((m.val 42)*((m.val 34)*SubexpLiftRing.baseWidth 3 (m.val 33)))≤
      QueryHeadBudgets.compact A ∧
    m.val 21≤QueryHeadBudgets.compact A :=
  array_capacity _ _ _ _ A (hvalues 21) (hvalues 42) (hvalues 34) (hvalues 33)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

/-- The actual paid initializer establishes the zero-node boundary from the
producer's framed table, including the empty unframed coefficient stream. -/
theorem initialized_boundary (a : Data) (t d Q J B : ℕ)
    (hn : a.stacks 300=Encoding.encodeList id (RingNodeMetadata.nodeBits t d Q))
    (hb : WordBound B a) :
    NodeBoundary a t d Q J B 0
      (QueryNodeFinish.guarded (QueryAssembler.Nodes.initialized a)) := by
  obtain ⟨hcursor,hnode,hstream,hguard,_,hbound⟩ :=
    QueryNodeLoopSpace.initialized_boundary a (RingNodeMetadata.nodeBits t d Q) B hn hb
  refine ⟨by simpa using hcursor,hnode,by simpa using hguard,?_,?_,?_,hbound⟩
  · intro i hi
    apply QueryNodeLoopSpace.initialized_frame a i
    intro hbad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbad
    rcases hbad with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [retainedPorts,QueryNodeEvaluation.framePorts] at hi
  · simp [hstream]
  · omega


/-- The bytes returned by the actual node readout advance the stream length
by exactly J full scalar words. No uniqueness of their encodings is used. -/
theorem NodeBoundary.next {initial a b : Data} {t d Q J B index : ℕ}
    (h : NodeBoundary initial t d Q J B index a)
    (codes : List (DensePolynomialProgram.Coeff (baseWidth 3 t) d))
    (hlen : codes.length=J)
    (hcursor : b.stacks 301=Encoding.encodeList id
      ((RingNodeMetadata.nodeBits t d Q).drop (index+1)))
    (hnode : b.stacks 307=List.replicate (index+1) true)
    (hguard : b.regs 37= !((RingNodeMetadata.nodeBits t d Q).drop (index+1)).isEmpty)
    (hframe : ∀ i∈retainedPorts,b.stacks i=a.stacks i)
    (hstream : b.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten)
    (hscratch : b.stacks 89=[]) (hb : WordBound B b) :
    NodeBoundary initial t d Q J B (index+1) b := by
  refine ⟨hcursor,hnode,hguard,fun i hi=>(hframe i hi).trans (h.retained i hi),?_,
    fun _=>hscratch,hb⟩
  rw [hstream,List.length_append,h.stream_length]
  have hc : ((codes.map RingProgram.flat).flatten).length=J*(d*baseWidth 3 t) := by
    change (DensePolynomialProgram.encode codes).length=_
    simp [hlen]
  rw [hc]
  ring

/-- Fresh per-node cache and parked-input caps are inherited from the
immutable produced words, independently of larger scratch at a loop boundary. -/
theorem NodeBoundary.input_caps {initial a : Data} {t d Q J B index A : ℕ}
    (h : NodeBoundary initial t d Q J B index a)
    (hcache : ∀ i∈QueryNodeEvaluation.cacheInputPorts,(initial.stacks i).length≤A)
    (hparked : ∀ i : Fin 14,
      (initial.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i))).length≤A) :
    (∀ i∈QueryNodeEvaluation.cacheInputPorts,(a.stacks i).length≤A) ∧
    (∀ i : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i))).length≤A) := by
  constructor
  · intro i hi
    have hm : i∈retainedPorts := by
      simp only [QueryNodeEvaluation.cacheInputPorts, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [h.retained i hm]
    exact hcache i hi
  · intro i
    have hm : NativeLayoutLoad.stackMap (LeafProgram.LayoutMasters.high i)∈retainedPorts := by
      fin_cases i <;> decide
    rw [h.retained _ hm]
    exact hparked i

theorem NodeBoundary.arithmetic {initial a : Data} {t d Q J B index : ℕ}
    (h : NodeBoundary initial t d Q J B index a) (out : State 40 768)
    (hf : ∀ i∈QueryReadyConstruction.arithmeticPorts,
      initial.stacks (i.castAdd 128)=out.stacks i) :
    ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i := by
  intro i hi
  have hm : i.castAdd 128∈retainedPorts := by
    simp only [QueryReadyConstruction.arithmeticPorts, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (h.retained _ hm).trans (hf i hi)

/-- The global fixed stream capacity pays for the next complete node, even
when its coefficient words encode zero. -/
theorem NodeBoundary.room {initial a : Data} {t d Q J B index : ℕ}
    (h : NodeBoundary initial t d Q J B index a) (hi : index<Q)
    (hQ : Q≤B) (hstream : Q*(J*(d*baseWidth 3 t))≤B) :
    (a.stacks 863).length+J*(d*baseWidth 3 t)≤B ∧ index+1≤B := by
  constructor
  · rw [h.stream_length]
    calc
      index*(J*(d*baseWidth 3 t))+J*(d*baseWidth 3 t) =
          (index+1)*(J*(d*baseWidth 3 t)) := by ring
      _ ≤ Q*(J*(d*baseWidth 3 t)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ B := hstream
  · omega

section ActualNode
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource LeafHeadSetupProgram
open QueryNodeEvaluation

variable (query : LeafQueryFrontend.Query) (k RB RC RD RI RE : ℕ)
  (hg : Guard (query.input k)) (hv : query.Valid)
  (first : MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q))
  (node : Fin (Query.packingProblem query k hg).Q)
  (m : Circuit.Model) (padding : Fin 8 → ℕ)
  (hm : m=Execute.guardedModel (query.input k) padding)
  (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3 ^ (m.val 34))
  (hQ : m.val 21=(Native.queryInputsAddressed query k hg first tail node).Q)
  (hR : (base.stacks 740).length=(Native.queryInputsAddressed query k hg first tail node).R)
  (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
local notation "H" => HighMarkedFrontend.highSet query
local notation "resources" => ProducedQueryResources.ofPacking query k RB RC RD RI RE hg first tail
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient query) resources


omit hm hQ hR in
/-- The actual initialized node loop retains each emitted coefficient word
and the cache witness from that same execution. A reference target is chosen
only after the nonempty, ordered output stream has been produced. -/
theorem nodes_run_oai (high : H → Bool) (A : ℕ) (a : State 40 896)
    (frontBase front : State 40 768) (bw : Bank.Words)
    (hf : Query.FrontState query k frontBase front padding bw)
    (hpark : ∀ j : Fin 14,
      a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
        (PackingCallerProgram.result front (Query.packingProblem query k hg)
          first tail).stacks (LayoutMasters.high j))
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
    (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
    (hvalues : ∀ i,m.val i≤A)
    (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
    (h708 : (a.stacks 708).length≤A)
    (hnodes : a.stacks 300=Encoding.encodeList id
      (RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h704 : a.stacks 704=List.replicate query.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
    (h706 : a.stacks 706=[query.mark.isSome])
    (h702 : a.stacks 702=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn
      (fun v : Fin (BinaryArithmetic.toNat query.ambient) =>
        if h : v ∈ H then high ⟨v, h⟩ else false))
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (model_eq : m = Execute.guardedModel (query.input k) padding)
    (query_count : m.val 21 = (native).Q)
    (radius_eq : (base.stacks 740).length = (native).R) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ (steps : ℕ) (z : Data) (outputs : List (List Bool)),
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.nodes steps a z ∧
      NodeBoundary a (m.val 33) (m.val 34) (m.val 21) (m.val 42)
        (QueryHeadBudgets.compact A) (m.val 21) z ∧
      outputs.length=m.val 21 ∧ z.stacks 863=outputs.flatten ∧
      (∀ i (hi : i<outputs.length),
        ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
          codes.length=m.val 42 ∧
          codes.map factor.p.ops.decode=List.ofFn
            (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
              (Polynomial.X+Polynomial.C (factor.p.ops.decode
                (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i+1)))))).coeff ∧
          outputs[i]'hi=(codes.map RingProgram.flat).flatten) ∧
      steps≤23*QueryHeadBudgets.compact A+
        (m.val 21)*(nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work+1)+32 ∧
      QueryExecution.PrefixBound QueryStreamProgram.nodes (steps+1) a
        (max (919*QueryHeadBudgets.compact A+31)
          (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A)) := by
  let F := QueryHeadBudgets.compact A
  let ns := RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)
  let I := NodeBoundary a (m.val 33) (m.val 34) (m.val 21) (m.val 42) F
  let P := fun i bytes =>
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ codes : List (DensePolynomialProgram.Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      codes.length=m.val 42 ∧
      codes.map factor.p.ops.decode=List.ofFn
        (Truncated.ofPolynomial (m.val 42) ((NodeConcrete.specTarget factor H high).comp
          (Polynomial.X+Polynomial.C (factor.p.ops.decode
            (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i+1)))))).coeff ∧
      bytes=(codes.map RingProgram.flat).flatten
  have physical : ∀ i b,I i b → b.stacks 301=Encoding.encodeList id (ns.drop i) ∧
      b.stacks 307=List.replicate i true ∧ b.regs 37= !(ns.drop i).isEmpty ∧ WordBound F b := by
    intro i b hb
    exact ⟨hb.cursor,hb.node,hb.guard,hb.bounded⟩
  have capacity := QueryNodeSourceBounds.model_capacity m A hvalues
  have step : ∀ i b, i < ns.length → I i b →
      ∃ steps c bytes, steps ≤ nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work ∧
        Eval QueryStreamProgram.nodeBody steps b c ∧ I (i + 1) c ∧ P i bytes ∧
        c.stacks 863 = b.stacks 863 ++ bytes ∧
        ∀ p q, p ≤ steps → Trace (compiled QueryStreamProgram.nodeBody 0 0) p
          (b.withPC (some (compiled QueryStreamProgram.nodeBody 0 0).entry)) q →
          ∀ port,(q.stacks port).length≤nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A := by
    intro i b hi hb
    have him : i < m.val 21 := by
      simpa only [ns, RingNodeMetadata.nodeBits_length] using hi
    let ix : Fin (Query.packingProblem query k hg).Q := ⟨i,by
      change i < (native).Q
      omega⟩
    have bank := hb.sourceBank query k hg frontBase front padding bw hf first tail ix hpark
    obtain ⟨cacheCap,parkCap⟩ := hb.input_caps hcache hparked
    have sources : Query.Sources query
        (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort b) := by
      exact ⟨(hb.retained 700 (by decide)).trans hsources.formula,
        (hb.retained 701 (by decide)).trans hsources.rows,
        (hb.retained 707 (by decide)).trans hsources.modulus,
        (hb.retained 708 (by decide)).trans hsources.width,
        (hb.retained 709 (by decide)).trans hsources.ambient⟩
    have cursor : b.stacks 301=Encoding.encodeList id
        (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (ix.val+1))::ns.drop (i+1)) := by
      rw [hb.cursor,RingNodeMetadata.nodeBits_drop _ _ _ ⟨i,him⟩]
    have room := hb.room him capacity.2 capacity.1
    obtain ⟨words,hc,steps,c,codes,he,hlen,hvalue,happend,h301,h307,hguard,_hpeek,hscratch,
        hfinalFrame,hbound,hcost,hspace⟩ :=
      node_run query k RB RC RD RI RE hg hv first tail ix m padding model_eq ht hd M cache half e
        base out ho hfield query_count radius_eq hJ source hsource high A b (ns.drop (i+1))
        bank parkCap cacheCap
        hvalues sources (by rw [hb.retained 700 (by decide)]; exact h700)
        (by rw [hb.retained 701 (by decide)]; exact h701)
        (by rw [hb.retained 708 (by decide)]; exact h708) cursor
        ((hb.retained 338 (by decide)).trans hmask) (hb.arithmetic out hframe) hdegree
        ((hb.retained 704 (by decide)).trans h704)
        ((hb.retained 705 (by decide)).trans h705)
        ((hb.retained 706 (by decide)).trans h706)
        ((hb.retained 702 (by decide)).trans h702)
        ((hb.retained 703 (by decide)).trans h703) hb.bounded room.1
    refine ⟨steps,c,(codes.map RingProgram.flat).flatten,hcost,he,?_,?_,happend,?_⟩
    · exact hb.next codes hlen h301 h307 hguard (fun j hj =>
        hfinalFrame j (List.mem_filter.mp hj).1
          (of_decide_eq_true (List.mem_filter.mp hj).2).1
          (of_decide_eq_true (List.mem_filter.mp hj).2).2) happend hscratch hbound
    · exact ⟨words,hc,codes,hlen,hvalue,rfl⟩
    · intro p q hp hq port
      exact hspace.bound p q (by omega) hq port
  obtain ⟨steps,z,outputs,hcost,he,hend,hlen,houtputs,_hcursor,_hindex,_hguard,hstream,hbound,hprefix⟩ :=
    QueryNodeLoopSpace.nodes_eval_prefix ns I P F
      (nodeSpace (native).n (m.val 33) (m.val 34) (m.val 42) A)
      (nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work)
      physical step a ha (initialized_boundary a _ _ _ _ F hnodes ha)
  have hlen' : outputs.length=m.val 21 := by simpa only [ns,RingNodeMetadata.nodeBits_length] using hlen
  have hpositive : 0 < m.val 21 := by
    have hp := node.isLt
    change node.val < (native).Q at hp
    omega
  obtain ⟨words,hc,_codes,_hlen,_value,_bytes⟩ := houtputs 0 (by omega)
  refine ⟨words,hc,steps,z,outputs,he,?_,hlen',hstream,?_,?_,⟨?_⟩⟩
  · simpa only [ns,RingNodeMetadata.nodeBits_length] using hend
  · intro i hi
    obtain ⟨words',hc',codes,hlen,hvalue,hbytes⟩ := houtputs i hi
    exact ⟨codes,hlen,hvalue,hbytes⟩
  · simpa only [ns,RingNodeMetadata.nodeBits_length] using hcost
  · exact StructuredSpace.compiled_halt_stack_bound he 838 838 hprefix


end ActualNode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run_oai
