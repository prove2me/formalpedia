-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:50:46.156997+00:00
-- url     : https://prove2.me/submissions/d2112b0f-2c07-418b-8f54-4a67fbb0eab5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_canonical_dfs_execution
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

section Finite

variable [Fintype V]

theorem count_pos_iff (F : CNF V) : 0 < count F ↔ Satisfiable F := by
  simp [count, Finset.card_pos, Finset.Nonempty, Satisfiable]

end Finite
end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ABI
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed disjoint register and stack banks for the counting machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI

theorem countStack_ne_answerStack : countStack ≠ answerStack := by decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem digits_two_eq_map_toNat (a : ℕ) :
    Nat.digits 2 a = a.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction a.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

@[simp] theorem countWord_decode (a : ℕ) :
    Nat.ofDigits 2 ((countWord a).map Bool.toNat) = a := by
  by_cases h : a = 0
  · subst a
    rfl
  · rw [countWord, ite_eq_right h, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 a

@[simp] theorem countWord_toNat (a : ℕ) : BinaryArithmetic.toNat (countWord a) = a := by
  have h (word : List Bool) :
      BinaryArithmetic.toNat word = Nat.ofDigits 2 (word.map Bool.toNat) := by
    induction word with
    | nil => rfl
    | cons b word ih =>
        cases b <;> simp [BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih,
          Nat.ofDigits]
  rw [h, countWord_decode]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete count command including startup and physical full-word export.
The actual positivity suffix is appended by the shared native integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

theorem boundedEval_mono {code : Code} {t a b small large}
    (h : BoundedEval code t a b small) (hle : small ≤ large) : BoundedEval code t a b large :=
  ⟨h.eval, fun p c hp hc i => (h.space p c hp hc i).trans hle⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem positivity_eval {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = []) :
    Eval (positivity ports answer) (8 * (a.stacks ports.counter).length + 8)
      a (positivityResult ports answer a) := by
  simpa only [positivity, positivityResult, Nat.add_assoc] using
    Eval.seq (CounterForPrograms.test_eval ports a hs)
      (Eval.base (StructuredProgram.Eval.atom
        (.push answer (ports.register 2)) (CounterForPrograms.testResult ports a)))

theorem positivityResult_stacks {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = []) :
    (positivityResult ports answer a).stacks = Function.update a.stacks answer
      ((!CounterPrograms.isZero (a.stacks ports.counter)) :: a.stacks answer) := by
  simp only [positivityResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    CounterForPrograms.testResult_flag, CounterForPrograms.testResult_stacks ports a hs]

theorem positivityResult_count {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = [])
    (ha : ports.counter ≠ answer) :
    (positivityResult ports answer a).stacks ports.counter = a.stacks ports.counter := by
  rw [positivityResult_stacks ports answer a hs, Function.update_of_ne ha]

theorem positivityResult_answer {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = [])
    (ha : a.stacks answer = []) :
    (positivityResult ports answer a).stacks answer =
      [decide (0 < BinaryArithmetic.toNat (a.stacks ports.counter))] := by
  rw [positivityResult_stacks ports answer a hs, Function.update_self, ha]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [CounterPrograms.isZero_eq_false_iff, CounterPrograms.value_eq_toNat]

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

theorem answerReady_count (a : State 80 1220) :
    (answerReady a).stacks ABI.countStack = a.stacks ABI.countStack := by
  simp [answerReady, clearOutputState, ABI.countStack, ABI.answerStack, ABI.positivityScratch]

theorem answerReady_scratch (a : State 80 1220) :
    (answerReady a).stacks ABI.positivityScratch = [] := by
  simp [answerReady, clearOutputState]

theorem answerReady_answer (a : State 80 1220) :
    (answerReady a).stacks ABI.answerStack = [] := by
  simp [answerReady, clearOutputState, ABI.answerStack, ABI.positivityScratch]

theorem answerCommand_eval (a : State 80 1220) :
    Eval answerCommand (answerSteps a - 1) a (answerResult a) := by
  have hp := positivity_eval positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a)
  have hs := clearOutput_eval ABI.positivityScratch (clearOutputState ABI.answerStack a)
  have ha := clearOutput_eval ABI.answerStack a
  have h := ha.seq (hs.seq hp)
  have he : (clearOutputState ABI.answerStack a).stacks ABI.positivityScratch =
      a.stacks ABI.positivityScratch := by
    simp [clearOutputState, ABI.answerStack, ABI.positivityScratch]
  convert h using 1
  · rfl
  · simp only [answerSteps, positivityPorts, answerReady_count, he]
    omega
  · rfl

theorem answerResult_count (a : State 80 1220) :
    (answerResult a).stacks ABI.countStack = a.stacks ABI.countStack := by
  exact (positivityResult_count positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a) ABI.countStack_ne_answerStack).trans (answerReady_count a)

theorem answerResult_answer (a : State 80 1220) :
    (answerResult a).stacks ABI.answerStack =
      [decide (0 < BinaryArithmetic.toNat (a.stacks ABI.countStack))] := by
  have h := positivityResult_answer positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a) (answerReady_answer a)
  simpa only [answerResult, positivityPorts, answerReady_count] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

/-- The suffix is linear in the count word; every caller stack is included. -/
theorem answer_all_prefix (a : State 80 1220) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ answerSteps a →
      Trace answerProgram prefixSteps (a.withPC (some answerProgram.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ 1232 * bound + 15 := by
  intro prefixSteps intermediate hsteps htrace i
  have hstart : dataBits (a.withPC (some answerProgram.entry)) ≤ 1220 * bound :=
    StreamResources.dataBits_le_mul _ ha
  have hlocal := StructuredSpace.local_stack_bound answerProgram
    (steps := answerSteps a) hstart
    prefixSteps intermediate hsteps htrace i
  have hcount := ha ABI.countStack
  have hanswer := ha ABI.answerStack
  have hscratch := ha ABI.positivityScratch
  simp only [answerSteps] at hlocal
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeJointOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Append the actual positivity scan to a proved exact-count execution.
Both outputs, the time charge and every source-prefix bound belong to this
same command; the count word is preserved in full. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

theorem answer_bounded (a : State 80 1220) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    DFSVisit.BoundedEval answerCommand (answerSteps a - 1) a (answerResult a)
      (1232 * bound + 15) := by
  refine ⟨answerCommand_eval a, ?_⟩
  intro steps b hs ht i
  exact answer_all_prefix a bound ha steps b (hs.trans (Nat.sub_le _ _)) ht i

theorem append_answer {n : ℕ} (F : SAT.CNF (Fin n))
    (body : Cmd 80 1220) {steps : ℕ} {a b : State 80 1220} {bound : ℕ}
    (hbody : DFSVisit.BoundedEval body steps a b bound)
    (hcount : b.stacks ABI.countStack = countWord (SAT.count F)) :
    ∃ total, total ≤ steps + 12 * bound + 14 ∧
      DFSVisit.BoundedEval (.seq body answerCommand) total a (answerResult b)
        (1232 * bound + 15) ∧
      (answerResult b).stacks ABI.countStack = countWord (SAT.count F) ∧
      (answerResult b).stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      (decide (0 < SAT.count F) = true ↔ SAT.Satisfiable F) := by
  have hb := hbody.final_bound
  have hseq := (DFSCountProgram.boundedEval_mono hbody (by omega)).seq
    (answer_bounded b bound hb)
  refine ⟨steps + (answerSteps b - 1), ?_, hseq, ?_, ?_, ?_⟩
  · have hc := hb ABI.countStack
    have ha := hb ABI.answerStack
    have hs := hb ABI.positivityScratch
    dsimp only [answerSteps]
    omega
  · exact (answerResult_count b).trans hcount
  · rw [answerResult_answer, hcount, countWord_toNat]
  · simp [SAT.count_pos_iff]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed outer instruction sequence composes actual parameter setup,
disjoint counting DFS, and full-word positivity. The existing concrete-leaf
contract remains an explicit development obligation, not a final endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

/-- Every phase uses the same physical state. The setup's proved final bound
supplies the DFS input cap; the final enlargement occurs once, after counting. -/
theorem outer_from_setup_oai {n setupSteps inputBound bound : ℕ}
    (k : ℕ) (hk : 2 ≤ k) (F : SAT.CNF (Fin n)) (hw : SAT.WidthAtMost k F)
    (a b : State 80 1220)
    (hsetup : DFSVisit.BoundedEval (setupAfterFrontend k) setupSteps a b inputBound)
    (ready : SetupReady k F b) (hs : 0 < sparsifySchedule n)
    (leaf : Cmd 80 1220) (leafTime : ℕ)
    (hstartup : 1220 * inputBound +
      8 * (SubexpNormalizationCorrectness.normalizedBody F).length + 17 ≤ bound)
    (hvisit : DFSCountProgram.visitSpace k n F.card (b.stacks 259).length ≤ bound)
    (hleaf : DFSVisit.LeafContract (n := n) k (b.stacks 259) inputBound
      leaf leafTime bound) :
    ∃ visits total final,
      total ≤ setupSteps +
        dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
          (b.stacks 259).length leafTime bound visits +
        12 * outerBoundary inputBound bound n + 14 ∧
      DFSVisit.BoundedEval (outerCommand k leaf) total a final
        (outerSpace inputBound bound n) ∧
      final.stacks ABI.countStack = countWord (SAT.count F) ∧
      final.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      (decide (0 < SAT.count F) = true ↔ SAT.Satisfiable F) ∧
      (visits : ℝ) ≤
        ((SparseCharging.depthConstant k
          (SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((n : ℝ) / sparsifySchedule n) := by
  obtain ⟨visits, t, c, ht, hd, hc, hv⟩ := canonical_dfs_execution k hk F hw b ready hs
    leaf leafTime inputBound bound hsetup.final_bound hstartup hvisit hleaf
  have hp := DFSCountProgram.boundedEval_mono hsetup
    (Nat.le_max_left inputBound (1224 * bound + 7 * n + 19))
  have hq := DFSCountProgram.boundedEval_mono hd
    (Nat.le_max_right inputBound (1224 * bound + 7 * n + 19))
  obtain ⟨total, htotal, he, hcount, hanswer, hsat⟩ := append_answer F
    (.seq (setupAfterFrontend k) (DFSCountProgram.command k leaf)) (hp.seq hq) hc
  refine ⟨visits, total, answerResult c, ?_, he, hcount, hanswer, hsat, hv⟩
  change t ≤ dfsTime k n (SubexpNormalizationCorrectness.normalizedBody F).length
    (b.stacks 259).length leafTime bound visits at ht
  change total ≤ setupSteps + t + 12 * outerBoundary inputBound bound n + 14 at htotal
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup_oai
