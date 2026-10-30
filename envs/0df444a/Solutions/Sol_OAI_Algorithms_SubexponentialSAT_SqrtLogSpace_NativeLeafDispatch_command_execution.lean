-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:20:15.926754+00:00
-- url     : https://prove2.me/submissions/831e957e-f388-4066-b27d-f20081de1b93

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeTerminal_readyCommand_bounded

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

variable {V : Type u}

variable [DecidableEq V]

section Decidable

omit [DecidableEq V] in
theorem not_satisfiable_of_empty_mem {F : CNF V} (h : ∅ ∈ F) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  have he := (CNF.eval_eq_true a F).mp ha ∅ h
  simp at he

section Finite

variable [Fintype V]

theorem count_pos_iff (F : CNF V) : 0 < count F ↔ Satisfiable F := by
  simp [count, Finset.card_pos, Finset.Nonempty, Satisfiable]

theorem count_eq_zero_iff (F : CNF V) : count F = 0 ↔ ¬ Satisfiable F := by
  rw [← count_pos_iff]
  cases count F <;> simp

end Finite
end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSparsifyEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact syntax and normalization bridges for the word-based node search. -/

namespace SubexponentialSAT.ExecSparsifyEncoding

open ExecCNF ExecSunflowerCodeTransport

theorem encodeList_map {α β : Type*} (f : α → β) (enc : β → List Bool) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

end SubexponentialSAT.ExecSparsifyEncoding

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

namespace BoundedEval
variable {command first second yes no : Code} {t u B : ℕ} {a b c : Data}

theorem final_bound (h : BoundedEval command t a b B) :
    ∀ i, (b.stacks i).length ≤ B :=
  h.space t _ le_rfl (compiled_trace h.eval 256 256)

theorem seq (h : BoundedEval first t a b B) (g : BoundedEval second u b c B) :
    BoundedEval (.seq first second) (t + u) a c B :=
  ⟨h.eval.seq g.eval, StructuredSpace.sequence_stack_bound h.eval g.eval 256 256 h.space g.space
    (compiled (.seq first second) 256 256) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 256 256)⟩

theorem ite_true {flag : Fin 80} (hf : a.regs flag = true)
    (h : BoundedEval yes t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_true hf h.eval, StructuredSpace.conditional_true_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

theorem ite_false {flag : Fin 80} (hf : a.regs flag = false)
    (h : BoundedEval no t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_false hf h.eval, StructuredSpace.conditional_false_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEmptyClauseProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A preserving empty-clause test on the actual encoded leaf

The fixed program searches for the one-bit encoding of an empty clause.
The leaf on stack 9 and every other caller word are preserved.  Only the
five empty membership work ports and one empty copy port are used.
-/

namespace SubexponentialSAT.SubexpEmptyClauseProgram

open BitProgram StructuredCalls

theorem empty_record_iff {α : Type*} (encode : α → List Bool) (F : List (List α)) :
    [false] ∈ F.map (Encoding.encodeList encode) ↔ [] ∈ F := by
  constructor
  · intro h
    obtain ⟨C, hC, he⟩ := List.mem_map.mp h
    cases C with
    | nil => exact hC
    | cons x xs => simp [Encoding.encodeList] at he
  · intro h
    exact List.mem_map.mpr ⟨[], h, rfl⟩

theorem formula_empty_mem_iff {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    (∅ : SAT.Clause (Fin n)) ∈ ExecCNF.formulaSet F ↔ [] ∈ F := by
  constructor
  · intro h
    obtain ⟨C, hC, hc⟩ := ExecCNF.mem_formulaSet.mp h
    cases C with
    | nil => exact hC
    | cons x xs => simp [ExecCNF.clauseSet] at hc
  · intro h
    exact ExecCNF.mem_formulaSet.mpr ⟨[], h, rfl⟩

theorem empty_unsatisfiable {n : ℕ} (F : List (List (SAT.Literal (Fin n))))
    (h : [] ∈ F) : ¬ SAT.Satisfiable (ExecCNF.formulaSet F) :=
  SAT.not_satisfiable_of_empty_mem ((formula_empty_mem_iff F).mpr h)

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramTrivial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual classification of the two trivial leaf cases. The empty formula
and an empty clause are detected separately on the preserved encoded leaf. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Trivial

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem result_nonempty (a : Data) (records : List (List Bool)) :
    (result a records).regs 7 = decide (records ≠ []) := by
  cases records <;> simp [result,readRegs,Encoding.encodeList]

theorem result_empty_clause (a : Data) (records : List (List Bool)) :
    (result a records).regs 0 = decide ([false] ∈ records) := by
  simp [result,readRegs,SubexpEmptyClauseProgram.result]

end SubexponentialSAT.SqrtLog.LeafProgram.Trivial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

theorem classified_stacks (a : Data) (records : List (List Bool)) :
    (classified a records).stacks = a.stacks := by
  funext i
  by_cases hi : ∃ j, classifierStacks j = i
  · obtain ⟨j, rfl⟩ := hi
    exact embedState_stack _ _ _ _ classifierStacks.injective j
  · exact embedState_stack_frame _ _ _ _ i hi

theorem classified_empty_clause (a : Data) (records : List (List Bool)) :
    (classified a records).regs 0 = decide ([false] ∈ records) := by
  exact (embedState_register _ _ _ _ (Fin.castAdd_injective 10 70) 0).trans
    (SqrtLog.LeafProgram.Trivial.result_empty_clause _ _)

theorem classified_nonempty (a : Data) (records : List (List Bool)) :
    (classified a records).regs 7 = decide (records ≠ []) := by
  exact (embedState_register _ _ _ _ (Fin.castAdd_injective 10 70) 7).trans
    (SqrtLog.LeafProgram.Trivial.result_nonempty _ _)

theorem powered_output (a : Data) (n : ℕ) :
    (powered a n).stacks 263 = countWord (2 ^ n) :=
  embedState_stack _ _ _ _ powerStacks.injective 1

theorem powered_frame (a : Data) (n : ℕ) (hwork : a.stacks 268 = [])
    (i : Fin 1220) (hi : i ≠ 263) : (powered a n).stacks i = a.stacks i := by
  by_cases hw : i = 268
  · subst i
    rw [hwork]
    exact embedState_stack _ _ _ _ powerStacks.injective 0
  · have hport : ¬ ∃ j, powerStacks j = i := by
      rintro ⟨j, rfl⟩
      fin_cases j
      · exact hw rfl
      · exact hi rfl
    rw [powered, embedState_stack_frame _ _ _ _ i hport]
    simp [Native.copiedWord, StackRoutines.copyStacks, hw]

theorem powered_low_regs (a : Data) (n : ℕ) (i : Fin 80) (hi : i.val < 72) :
    (powered a n).regs i = a.regs i := by
  have hport : ¬ ∃ j, powerRegs j = i := by
    rintro ⟨j, rfl⟩
    have hge : 72 ≤ (powerRegs j).val := by
      fin_cases j <;> decide
    omega
  rw [powered, embedState_register_frame _ _ _ _ i hport]
  have h72 : i ≠ 72 := by intro h; have hv : i.val = 72 := congrArg Fin.val h; omega
  have h73 : i ≠ 73 := by intro h; have hv : i.val = 73 := congrArg Fin.val h; omega
  simp [Native.copiedWord, readRegs, h72, h73]

theorem result_frame (a : Data) (n : ℕ) (records : List (List Bool))
    (hwork : a.stacks 268 = []) (i : Fin 1220) (hi : i ≠ 263) :
    (result a n records).stacks i = a.stacks i := by
  by_cases hz : [false] ∈ records
  · simp [result, hz, zeroed, hi, classified_stacks]
  · by_cases he : records = []
    · rw [result, ite_eq_right hz, ite_eq_left he, powered_frame _ _ (by
        simpa [classified_stacks] using hwork) i hi, classified_stacks]
    · simp [result, hz, he, classified_stacks]

theorem result_low_regs (a : Data) (n : ℕ) (records : List (List Bool))
    (i : Fin 80) (hi : i.val < 72) :
    (result a n records).regs i = (classified a records).regs i := by
  have h72 : i ≠ 72 := by intro h; have hv : i.val = 72 := congrArg Fin.val h; omega
  by_cases hz : [false] ∈ records
  · simp [result, hz, zeroed, h72]
  · by_cases he : records = []
    · rw [result, ite_eq_right hz, ite_eq_left he]
      exact powered_low_regs (classified a records) n i hi
    · simp [result, hz, he]

theorem clauseRecords_body {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    Encoding.encodeList id (clauseRecords F) = ExecQuantitativeSparsify.encodeRawFormula F := by
  simp only [clauseRecords, ExecQuantitativeSparsify.encodeRawFormula,
    ExecSparsifyEncoding.encodeList_map]
  rfl

theorem clauseRecords_empty_clause {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    [false] ∈ clauseRecords F ↔ [] ∈ F := SubexpEmptyClauseProgram.empty_record_iff _ F

theorem result_empty_clause {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n)))) :
    (result a n (clauseRecords F)).regs 0 = decide ([] ∈ F) := by
  rw [result_low_regs _ _ _ 0 (by decide), classified_empty_clause]
  simp only [clauseRecords_empty_clause]

theorem result_nonempty {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n)))) :
    (result a n (clauseRecords F)).regs 7 = decide (F ≠ []) := by
  rw [result_low_regs _ _ _ 7 (by decide), classified_nonempty]
  simp only [ne_eq, clauseRecords_nil_iff]

theorem result_nonterminal {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n))))
    (hclause : [] ∉ F) (hformula : F ≠ []) :
    result a n (clauseRecords F) = classified a (clauseRecords F) := by
  simp [result, clauseRecords_empty_clause, hclause, hformula]

/-- The outer trivial cases produce the full ambient count, including n=0. -/
theorem result_count {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n))))
    (houtput : a.stacks 263 = []) (hterminal : [] ∈ F ∨ F = []) :
    (result a n (clauseRecords F)).stacks 263 =
      countWord (SAT.count (ExecCNF.formulaSet F)) := by
  rcases hterminal with hz | he
  · have hzero : SAT.count (ExecCNF.formulaSet F) = 0 :=
      (SAT.count_eq_zero_iff _).mpr (SubexpEmptyClauseProgram.empty_unsatisfiable F hz)
    simp [result, (clauseRecords_empty_clause F).mpr hz, zeroed,
      classified_stacks, houtput, hzero]
  · subst F
    simp [result, clauseRecords, powered_output]

theorem prepared_frame (a : Data) (i : Fin 1220)
    (ho : i ≠ 263) (hw : i ≠ 268) (hs : i ≠ 269) :
    (prepared a).stacks i = a.stacks i := by
  simp [prepared, Native.clearOutputState, ho, hw, hs]

theorem readyResult_count {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n))))
    (hterminal : [] ∈ F ∨ F = []) :
    (readyResult a n (clauseRecords F)).stacks 263 =
      countWord (SAT.count (ExecCNF.formulaSet F)) :=
  result_count (prepared a) F (prepared_output a) hterminal

theorem readyResult_frame (a : Data) (n : ℕ) (records : List (List Bool))
    (i : Fin 1220) (ho : i ≠ 263) (hw : i ≠ 268) (hs : i ≠ 269) :
    (readyResult a n records).stacks i = a.stacks i := by
  rw [readyResult, result_frame _ _ _ (prepared_work a) i ho,
    prepared_frame a i ho hw hs]

@[simp] theorem readyResult_work (a : Data) (n : ℕ) (records : List (List Bool)) :
    (readyResult a n records).stacks 268 = [] := by
  rw [readyResult, result_frame _ _ _ (prepared_work a) 268 (by decide), prepared_work]

@[simp] theorem readyResult_scratch (a : Data) (n : ℕ) (records : List (List Bool)) :
    (readyResult a n records).stacks 269 = [] := by
  rw [readyResult, result_frame _ _ _ (prepared_work a) 269 (by decide), prepared_scratch]

theorem readyResult_empty_clause {n : ℕ} (a : Data)
    (F : List (List (SAT.Literal (Fin n)))) :
    (readyResult a n (clauseRecords F)).regs 0 = decide ([] ∈ F) :=
  result_empty_clause (prepared a) F

theorem readyResult_nonempty {n : ℕ} (a : Data)
    (F : List (List (SAT.Literal (Fin n)))) :
    (readyResult a n (clauseRecords F)).regs 7 = decide (F ≠ []) :=
  result_nonempty (prepared a) F


open DisjointReuse.DFSVisit

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual terminal dispatch for the disjoint counting DFS. The retained ambient
dimension determines the empty-formula count. The nonterminal command is composed
after the same concrete classifier and must supply its own execution proof. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch

open BitProgram StructuredCalls DisjointReuse DFSVisit

variable {n k parameterBound : ℕ} {threshold : List Bool}
  {F : RawCNF n} {a : Data}

theorem ready_body (hr : LeafReady k threshold parameterBound F a) :
    a.stacks 265 = Encoding.encodeList id (NativeTerminal.clauseRecords F) :=
  hr.current.trans (NativeTerminal.clauseRecords_body F).symm

theorem ready_persistent (a : Data) (F : RawCNF n) (i : Fin 1220)
    (hi : i ∈ ([256, 257, 258, 259, 260, 261, 262, 264, 266, 267] : List (Fin 1220))) :
    (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)).stacks i = a.stacks i := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact NativeTerminal.readyResult_frame a n _ _ (by decide) (by decide) (by decide)

/-- The terminal branch returns the canonical whole count, including n = 0. -/
theorem terminal_done (hr : LeafReady k threshold parameterBound F a)
    (hterminal : [] ∈ F ∨ F = []) :
    LeafDone F a (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) := by
  constructor
  · exact NativeTerminal.readyResult_count a F hterminal
  · rw [NativeTerminal.readyResult_frame a n _ 30 (by decide) (by decide) (by decide)]
    exact hr.low_empty 30 (by decide)
  · exact ready_persistent a F

/-- Classification does not enlarge either persistent parameter word. -/
theorem nonterminal_ready (hr : LeafReady k threshold parameterBound F a)
    (hz : [] ∉ F) (hf : F ≠ []) :
    LeafReady k threshold parameterBound F
      (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) := by
  have frame := NativeTerminal.readyResult_frame a n (NativeTerminal.clauseRecords F)
  constructor
  · rw [frame 265 (by decide) (by decide) (by decide)]
    exact hr.current
  · rw [frame 264 (by decide) (by decide) (by decide)]
    exact hr.dimension
  · rw [frame 267 (by decide) (by decide) (by decide)]
    exact hr.ambient
  · rw [frame 264 (by decide) (by decide) (by decide)]
    exact hr.occurrence_length
  · rw [frame 267 (by decide) (by decide) (by decide)]
    exact hr.dimension_length
  · rw [frame 258 (by decide) (by decide) (by decide)]
    exact hr.header
  · rw [frame 259 (by decide) (by decide) (by decide)]
    exact hr.threshold
  · rw [frame 261 (by decide) (by decide) (by decide)]
    exact hr.left_empty
  · rw [frame 262 (by decide) (by decide) (by decide)]
    exact hr.right_empty
  · rw [NativeTerminal.readyResult, NativeTerminal.result_nonterminal _ F hz hf,
      NativeTerminal.classified_stacks, NativeTerminal.prepared_output]
  · intro i hi
    rw [frame i]
    · exact hr.low_empty i hi
    · intro h; have hv : i.val = 263 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 268 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 269 := congrArg Fin.val h; omega

theorem done_after_ready {e : Data}
    (hd : LeafDone F (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e) :
    LeafDone F a e :=
  ⟨hd.count, hd.scratch, fun i hi => (hd.persistent i hi).trans (ready_persistent a F i hi)⟩

private theorem skip_bounded (a : Data) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    BoundedEval (.base .skip) 0 a a bound := by
  refine ⟨.base (.skip a), ?_⟩
  intro prefixSteps c hp hc
  have hz : prefixSteps = 0 := by omega
  subst prefixSteps
  cases hc
  exact ha

/-- Actual classifier, terminal handling and nonterminal execution share one
uniform bound at every compiled prefix. The callback is an execution proof for
the explicit command argument, to be instantiated by the streamed leaf. -/
theorem command_execution_oai (nonterminal : Cmd 80 1220) (leafTime bound : ℕ)
    (hr : LeafReady k threshold parameterBound F a)
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound)
    (hcallback : [] ∉ F → F ≠ [] →
      LeafReady k threshold parameterBound F
        (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) →
      (∀ i, ((NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)).stacks i).length
        ≤ bound) →
      ∃ t ≤ leafTime, ∃ e,
        BoundedEval nonterminal t
          (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e bound ∧
        LeafDone F (NativeTerminal.readyResult a n (NativeTerminal.clauseRecords F)) e) :
    ∃ t ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + leafTime + 33,
      ∃ e, BoundedEval (command nonterminal) t a e bound ∧ LeafDone F a e := by
  obtain ⟨steps, hs, first⟩ := NativeTerminal.readyCommand_bounded a n bound
    (NativeTerminal.clauseRecords F) (ready_body hr)
    (fun i hi => hr.low_empty i (by omega)) hr.header hframe hclassifier hpower
  have hzero := NativeTerminal.readyResult_empty_clause a F
  have hnonempty := NativeTerminal.readyResult_nonempty a F
  by_cases hz : [] ∈ F
  · have second := (skip_bounded _ bound first.final_bound).ite_true
      (no := .ite 7 nonterminal (.base .skip)) (by simpa [hz] using hzero)
    exact ⟨_, by omega, _, first.seq second, terminal_done hr (Or.inl hz)⟩
  · by_cases hf : F = []
    · have second := ((skip_bounded _ bound first.final_bound).ite_false
        (yes := nonterminal) (by simpa [hf] using hnonempty)).ite_false
        (yes := .base .skip) (by simpa [hz] using hzero)
      exact ⟨_, by omega, _, first.seq second, terminal_done hr (Or.inr hf)⟩
    · obtain ⟨t, ht, e, last, hd⟩ :=
        hcallback hz hf (nonterminal_ready hr hz hf) first.final_bound
      have second := (last.ite_true (no := .base .skip)
        (by simpa [hf] using hnonempty)).ite_false (yes := .base .skip)
        (by simpa [hz] using hzero)
      exact ⟨_, by omega, e, first.seq second, done_after_ready hd⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution_oai
