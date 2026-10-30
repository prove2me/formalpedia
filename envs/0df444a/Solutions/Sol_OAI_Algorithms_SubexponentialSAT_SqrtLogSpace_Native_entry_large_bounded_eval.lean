-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:17:24.549928+00:00
-- url     : https://prove2.me/submissions/adce93f8-7714-4e89-92bc-f0c3d5cb536a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationCorrectness_normalizedBody_length_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem formulaBitLength_lower {n : ℕ} (F : SAT.CNF (Fin n)) :
    n + F.card + 2 ≤ formulaBitLength F := by
  have h := length_encodeList_lower (encodeList encodeNat) (cnfNumbers F)
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change F.card + 1 ≤ (encodeCNFBody F).length at h
  omega

theorem numVariables_le_formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) :
    n ≤ formulaBitLength F := by
  have := formulaBitLength_lower F
  omega

end SubexponentialSAT.Encoding

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

theorem seq (h : BoundedEval first t a b B) (g : BoundedEval second u b c B) :
    BoundedEval (.seq first second) (t + u) a c B :=
  ⟨h.eval.seq g.eval, StructuredSpace.sequence_stack_bound h.eval g.eval 256 256 h.space g.space
    (compiled (.seq first second) 256 256) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 256 256)⟩

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
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

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

theorem copyWord_eval (src dst scratch : Fin 1220) (a : State 80 1220)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (htd : scratch ≠ dst)
    (hblank : a.stacks scratch = []) :
    Eval (copyWord src dst scratch) (7 * (a.stacks src).length + 5) a
      (copiedWord src dst a) :=
  Eval.call _ (ListRegisterProgram.copy_run src dst scratch 72 73 hsd hst htd
    (by decide) a.regs a.stacks hblank)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FiniteFallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Generic finite scanner selectively adapted from the reviewed canceled source
`CountingDraft/FiniteWordScanner.lean`; no obsolete endpoint or rate is imported.

Fixed finite control for bounded input prefixes and complete binary output words.
The transition table is chosen before any runtime input. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner



open BitProgram

variable {qCount : ℕ}

variable (L : ℕ) (start : Fin qCount) (next : Fin qCount → Bool → Fin qCount)
  (out : Fin qCount → List Bool) (hout : ∀ q, (out q).length ≤ L)

theorem consume (q : Fin qCount) (value present bit : Bool) (word : List Bool) :
    Trace (program L start next out hout) 3
      (cfg L q 0 (by omega) value present (bit :: word))
      (cfg L (next q bit) 0 (by omega) bit true word) := by
  refine .cons (b := cfg L q 1 (by omega) bit true word) ?_
    (.cons (b := cfg L q 2 (by omega) bit true word) ?_ (.cons ?_ (.refl _)))
  · simp [step, program, cfg, execInstr, readRegs]
  · simp [step, program, cfg, execInstr, regs]
  · cases bit <;> simp [step, program, cfg, execInstr, regs]

theorem begin_output (q : Fin qCount) (value present : Bool) :
    Trace (program L start next out hout) 2
      (cfg L q 0 (by omega) value present [])
      (cfg L q 3 (by omega) false false []) := by
  refine .cons (b := cfg L q 1 (by omega) false false []) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr, readRegs]
  · simp [step, program, cfg, execInstr]

theorem finish_output (q : Fin qCount) (value : Bool) :
    Trace (program L start next out hout) 2
      (cfg L q (2 * (out q).length + 3) (by have := hout q; omega)
        value false (out q))
      (terminal (program L start next out hout) (out q)) := by
  refine .cons (b := cfg L q (2 * (out q).length + 4) (by have := hout q; omega)
    false false (out q)) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr]
  · simp [step, program, cfg, execInstr, terminal]

theorem emit_pair (q : Fin qCount) (value bit : Bool) (rest done : List Bool)
    (h : out q = (bit :: rest).reverse ++ done) :
    Trace (program L start next out hout) 2
      (cfg L q (2 * done.length + 3) (by have := hout q; simp [h] at this ⊢; omega)
        value false done)
      (cfg L q (2 * (bit :: done).length + 3)
        (by have := hout q; simp [h] at this ⊢; omega) bit false (bit :: done)) := by
  have hlen : (out q).length = rest.length + 1 + done.length := by simp [h]; omega
  have hbit : ((out q).reverse[done.length]?).getD false = bit := by
    simp [h, List.reverse_append]
  have hfirst : 2 * done.length + 3 < 2 * (out q).length + 3 := by omega
  have hsecond : 2 * done.length + 4 < 2 * (out q).length + 3 := by omega
  refine .cons (b := cfg L q (2 * done.length + 4)
    (by have := hout q; omega) bit false done) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr, hfirst, hbit,
      show 2 * done.length + 3 ≠ 1 by omega,
      show 2 * done.length + 3 ≠ 2 by omega]
  · simp [step, program, cfg, execInstr, hsecond, regs, Nat.mul_add,
      show 2 * done.length + 4 ≠ 1 by omega,
      show 2 * done.length + 4 ≠ 2 by omega]

theorem emit (q : Fin qCount) (rest done : List Bool) (value : Bool)
    (h : out q = rest.reverse ++ done) :
    Trace (program L start next out hout) (2 * rest.length + 2)
      (cfg L q (2 * done.length + 3) (by have := hout q; simp [h] at this ⊢; omega)
        value false done)
      (terminal (program L start next out hout) (out q)) := by
  induction rest generalizing done value with
  | nil => simpa [h] using finish_output L start next out hout q value
  | cons bit rest ih =>
      have hnext : out q = rest.reverse ++ (bit :: done) := by
        simpa [List.reverse_cons, List.append_assoc] using h
      have ht := (emit_pair L start next out hout q value bit rest done h).trans
        (ih (bit :: done) bit hnext)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem trace (q : Fin qCount) (word : List Bool) (value present : Bool) :
    Trace (program L start next out hout)
      (3 * word.length + 2 * (out (word.foldl next q)).length + 4)
      (cfg L q 0 (by omega) value present word)
      (terminal (program L start next out hout) (out (word.foldl next q))) := by
  induction word generalizing q value present with
  | nil =>
      rw [List.foldl_nil]
      have ht := (begin_output L start next out hout q value present).trans
        (emit L start next out hout q (out q).reverse [] false (by simp))
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      simp only [List.length_reverse, List.length_nil]
      omega
  | cons bit word ih =>
      have ht := (consume L start next out hout q value present bit word).trans
        (ih (next q bit) bit true)
      simpa [List.foldl_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ht


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

open BitProgram Scanner
open scoped BigOperators

open StructuredCalls

theorem cutoff_fold_replicate (B n : ℕ) (q : Fin (B + 2)) :
    ((List.replicate n true).foldl (cutoffNext B) q).val = min (B + 1) (q.val + n) := by
  induction n generalizing q with
  | zero => simp; omega
  | succ n ih =>
    simp only [List.replicate_succ, List.foldl_cons, ih, cutoffNext, ite_true, if_true]
    omega

theorem cutoff_fold_header (B n : ℕ) :
    cutoffOut B ((Encoding.encodeNat n).foldl (cutoffNext B) ⟨0, by omega⟩) =
      [decide (n ≤ B)] := by
  have h := cutoff_fold_replicate B n (⟨0, by omega⟩ : Fin (B + 2))
  simp only [Encoding.encodeNat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    cutoffOut, cutoffNext, Bool.false_eq_true, ite_false, Nat.add_zero]
  simp only [Nat.zero_add] at h
  rw [h]
  have he : min (B + 1) (min (B + 1) n) ≤ B ↔ n ≤ B := by omega
  simp only [he]

theorem cutoffScanner_trace (B n : ℕ) (r : Fin 2 → Bool) :
    Trace (cutoffScanner B) (3 * (Encoding.encodeNat n).length + 6)
      ((⟨r, fun _ => Encoding.encodeNat n⟩ : State 2 1).withPC
        (some (cutoffScanner B).entry))
      ((StructuredProgram.ioState 0 [decide (n ≤ B)]).withPC none) := by
  have hr : Scanner.regs (r 0) (r 1) = r := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have h := Scanner.trace 1 (⟨0, by omega⟩ : Fin (B + 2)) (cutoffNext B)
    (cutoffOut B) (by intro q; rfl) ⟨0, by omega⟩ (Encoding.encodeNat n) (r 0) (r 1)
  rw [cutoff_fold_header] at h
  simpa [cutoffScanner, Scanner.cfg, Scanner.program, hr, terminal,
    StructuredProgram.ioState, StructuredProgram.State.withPC] using h

theorem cutoffPrepare_eval (a : State 80 1220) :
    Eval cutoffPrepare (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 6)
      a (cutoffPrepared a) := by
  have h := (Native.clearOutput_eval 270 a).seq
    (Native.clearOutput_eval 271 (Native.clearOutputState 270 a))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  simp [Native.clearOutputState]
  omega

theorem cutoffCommand_eval (B n : ℕ) (a : State 80 1220)
    (hn : a.stacks 258 = Encoding.encodeNat n) :
    Eval (cutoffCommand B)
      (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n + 28)
      a (cutoffResult a (decide (n ≤ B))) := by
  have hcopy := Native.copyWord_eval 258 270 271 (cutoffPrepared a)
    (by decide) (by decide) (by decide)
    (by simp [cutoffPrepared, Native.clearOutputState])
  have hs : Function.Injective (fun _ : Fin 1 => (270 : Fin 1220)) :=
    fun _ _ _ => Subsingleton.elim _ _
  have hp : projectState cutoffRegs (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a) =
      (⟨(cutoffCopied a).regs ∘ cutoffRegs, fun _ => Encoding.encodeNat n⟩ : State 2 1) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      simp [projectState, cutoffCopied, Native.copiedWord, StackRoutines.copyStacks,
        cutoffPrepared, Native.clearOutputState, hn]
  have ht := cutoffScanner_trace B n ((cutoffCopied a).regs ∘ cutoffRegs)
  rw [← hp] at ht
  have hscan := eval_call_from_state (cutoffScanner B) cutoffRegs
    (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a) cutoffRegs.injective hs ht
  have hpop := Eval.base (StructuredProgram.Eval.atom (.pop (270 : Fin 1220) 75 76)
    (cutoffScanned a (decide (n ≤ B))))
  have h := (cutoffPrepare_eval a).seq (hcopy.seq (hscan.seq hpop))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  simp only [cutoffPrepared, Native.clearOutputState, Function.update_of_ne
    (show (258 : Fin 1220) ≠ 271 by decide), Function.update_of_ne
    (show (258 : Fin 1220) ≠ 270 by decide), hn, Encoding.length_encodeNat]
  omega

theorem cutoffScanned_word (a : State 80 1220) (flag : Bool) :
    (cutoffScanned a flag).stacks 270 = [flag] :=
  embedState_stack _ _ _ _ (fun _ _ _ => Subsingleton.elim _ _) 0

@[simp] theorem cutoffResult_flag (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).regs 75 = flag := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word, readRegs]

@[simp] theorem cutoffResult_work (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).stacks 270 = [] := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word]


/-- The complementary branch uses the same actual cutoff scan and preserves
its input frame before entering the fixed large-input command. -/
theorem dispatch_large_eval {B n steps : ℕ} (large : Cmd 80 1220)
    (hn : B < n) (a b : State 80 1220)
    (hheader : a.stacks 258 = Encoding.encodeNat n)
    (he : Eval large steps (cutoffResult a false) b) :
    Eval (dispatchCommand B large)
      (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n + 29 + steps)
      a b := by
  have hcut := cutoffCommand_eval B n a hheader
  have hn' : ¬ n ≤ B := by omega
  simp only [decide_eq_false hn'] at hcut
  have whole := hcut.seq (he.ite_false (yes := framedCommand B) (cutoffResult_flag a false))
  convert whole using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  all_goals omega

/-- A local prefix bound for the dispatcher composes with the proved prefix
bound of its actual large command, independently of the large running time. -/
theorem dispatch_large_space {B n steps D bound : ℕ} (large : Cmd 80 1220)
    (hn : B < n) (a b : State 80 1220)
    (hheader : a.stacks 258 = Encoding.encodeNat n)
    (hframe : ∀ i, (a.stacks i).length ≤ D)
    (hbudget : 1224 * D + 10 * n + 28 ≤ bound)
    (he : Eval large steps (cutoffResult a false) b)
    (hlarge : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled large 256 256) prefixSteps
        ((cutoffResult a false).withPC (some (compiled large 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound) :
    ∀ prefixSteps c,
      prefixSteps ≤ 2 * (a.stacks 270).length + 2 * (a.stacks 271).length +
        10 * n + 29 + steps →
      Trace (compiled (dispatchCommand B large) 256 256) prefixSteps
        (a.withPC (some (compiled (dispatchCommand B large) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  have hcut := cutoffCommand_eval B n a hheader
  have hn' : ¬ n ≤ B := by omega
  simp only [decide_eq_false hn'] at hcut
  have hsize : dataBits
      (a.withPC (some (compiled (cutoffCommand B) 256 256).entry)) ≤ 1220 * D := by
    change ∑ i : Fin 1220, (a.stacks i).length ≤ _
    calc
      _ ≤ ∑ _i : Fin 1220, D := Finset.sum_le_sum (fun i _ => hframe i)
      _ = _ := by simp
  have hcutspace : ∀ prefixSteps c,
      prefixSteps ≤ 2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n + 28 →
      Trace (compiled (cutoffCommand B) 256 256) prefixSteps
        (a.withPC (some (compiled (cutoffCommand B) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro prefixSteps c hp hc i
    have hg := StructuredSpace.local_stack_bound (compiled (cutoffCommand B) 256 256)
      hsize prefixSteps c hp hc i
    have h270 := hframe 270
    have h271 := hframe 271
    omega
  have hbranch := StructuredSpace.conditional_false_stack_bound
    (cutoffResult_flag a false) he 256 256 hlarge
    (compiled (.ite 75 (framedCommand B) large) 256 256)
    (siteAddress (.ite 75 (framedCommand B) large))
    (exitAddress (.ite 75 (framedCommand B) large))
    (compiled_site (.ite 75 (framedCommand B) large) 256 256)
  have whole := StructuredSpace.sequence_stack_bound hcut
    (he.ite_false (yes := framedCommand B) (cutoffResult_flag a false)) 256 256 hcutspace hbranch
    (compiled (dispatchCommand B large) 256 256) (siteAddress (dispatchCommand B large))
    (exitAddress (dispatchCommand B large)) (compiled_site (dispatchCommand B large) 256 256)
  intro prefixSteps c hp hc i
  exact whole prefixSteps c (by omega) hc i


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem frontendBound_polynomial {n : ℕ} (F : SAT.CNF (Fin n)) :
    frontendBound F ≤ 4000 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  have hn := Encoding.numVariables_le_formulaBitLength F
  have hb : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
    rw [Encoding.formulaBitLength_eq]
    omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hb2 := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2
  dsimp [frontendBound, FrontendProgram.initializeBound]
  nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeSetupSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete canonical startup through the disjoint sparsification parameters.
The only large-instance premises concern the numeric schedule. All parsing,
normalization, arithmetic, clearing, and caller storage belong to one run. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic

theorem frontendReady_stack_bound {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a : State 80 1220) (ha : FrontendReady F binary a) (hlen : binary.length ≤ n) :
    ∀ i, (a.stacks i).length ≤ Encoding.formulaBitLength F + 1 := by
  intro i
  have hn := Encoding.numVariables_le_formulaBitLength F
  by_cases hi : i = ABI.countStack
  · subst i
    rw [ha.input]
    exact Nat.le_succ _
  by_cases hu : i = 258
  · subst i
    rw [ha.header, Encoding.length_encodeNat]
    omega
  by_cases hb : i = 265
  · subst i
    rw [ha.body]
    have hl := SubexpNormalizationCorrectness.normalizedBody_length_le F
    have hh : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
      rw [Encoding.formulaBitLength_eq]
      omega
    omega
  by_cases hd : i = 267
  · subst i
    rw [ha.dimension]
    omega
  rw [ha.blank i hi hu hb hd]
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeEntrySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every-prefix space composition for the actual canonical frontend and
fixed-cutoff dispatcher. The large evaluation is a concrete subsequent run;
this module only composes its existing bound with the paid entry instructions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse.DFSVisit

theorem frontend_bounded_eval {n frontSteps bound : ℕ} (F : SAT.CNF (Fin n))
    (a : State 80 1220)
    (he : Eval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a)
    (ht : frontSteps ≤ frontendBound F)
    (hbudget : Encoding.formulaBitLength F +
      4000 * (Encoding.formulaBitLength F + 1) ^ 2 ≤ bound) :
    BoundedEval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a bound := by
  refine ⟨he, ?_⟩
  intro prefixSteps c hp hc i
  have hsize : dataBits
      ((StructuredProgram.ioState (r := 80) ABI.countStack (Encoding.encodeCNF F)).withPC
        (some (compiled frontendCommand 256 256).entry)) ≤ Encoding.formulaBitLength F := by
    change dataBits (initial (compiled frontendCommand 256 256) (Encoding.encodeCNF F)) ≤ _
    simp [Encoding.formulaBitLength]
  have htime := ht.trans (frontendBound_polynomial F)
  exact (StructuredSpace.local_stack_bound (compiled frontendCommand 256 256)
    (steps := 4000 * (Encoding.formulaBitLength F + 1) ^ 2)
    hsize prefixSteps c (hp.trans htime) hc i).trans hbudget

/-- The fixed-cutoff scan has polynomial local space and the same bound is
retained on every prefix of the following actual large-input evaluation. -/
theorem entry_large_bounded_eval_oai {cutoff n frontSteps steps bound : ℕ}
    (large : Cmd 80 1220) (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a b : State 80 1220) (hn : cutoff < n)
    (hfront : Eval frontendCommand frontSteps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) a)
    (hfrontTime : frontSteps ≤ frontendBound F)
    (ready : FrontendReady F binary a) (hlen : binary.length ≤ n)
    (hfrontBudget : Encoding.formulaBitLength F +
      4000 * (Encoding.formulaBitLength F + 1) ^ 2 ≤ bound)
    (hdispatchBudget : 1224 * (Encoding.formulaBitLength F + 1) + 10 * n + 28 ≤ bound)
    (hlarge : BoundedEval large steps (FiniteFallback.cutoffResult a false) b bound) :
    BoundedEval (entryCommand cutoff large) (frontSteps + (10 * n + 29 + steps))
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound := by
  have hf := frontend_bounded_eval F a hfront hfrontTime hfrontBudget
  have hframe := frontendReady_stack_bound F binary a ready hlen
  have hd := FiniteFallback.dispatch_large_eval large hn a b ready.header hlarge.eval
  have hs := FiniteFallback.dispatch_large_space large hn a b ready.header hframe
    hdispatchBudget hlarge.eval hlarge.space
  have h270 := ready.blank 270 (by decide) (by decide) (by decide) (by decide)
  have h271 := ready.blank 271 (by decide) (by decide) (by decide) (by decide)
  rw [h270, h271] at hd hs
  have hb : BoundedEval (FiniteFallback.dispatchCommand cutoff large)
      (10 * n + 29 + steps) a b bound := ⟨by simpa using hd, by simpa using hs⟩
  exact hf.seq hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval_oai
