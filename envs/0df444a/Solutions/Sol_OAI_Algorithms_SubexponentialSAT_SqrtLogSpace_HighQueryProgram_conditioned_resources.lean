-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.conditioned_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:26:44.238634+00:00
-- url     : https://prove2.me/submissions/05538518-2e82-48fd-b4cc-d225bd64ba2c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

end SubexponentialSAT.BankRoutines

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

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CopySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every-prefix storage of the actual preserving copy table. Empty destination
and temporary stacks permit the original per-stack envelope to be reused. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace

open BitProgram

private theorem copyWeight_step {r s : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8}
    (hstep : step (StackRoutines.copyProgram src dst tmp value present) a = some b) :
    copyWeight src dst tmp present b ≤ copyWeight src dst tmp present a := by
  cases hpc : a.pc with
  | none => simp [step, hpc] at hstep
  | some pc =>
      simp only [step, hpc, Option.map, Option.some.injEq] at hstep
      rw [← hstep]
      fin_cases pc
      · cases hx : a.stacks src <;>
          simp [copyWeight, execInstr, hpc, hx, readRegs, hsd.symm, hst.symm]
      · cases hr : a.regs present <;>
          simp [copyWeight, execInstr, hpc, hr]
      · simp [copyWeight, execInstr, hpc, hst, htd.symm]
        omega
      · cases hx : a.stacks tmp <;>
          simp [copyWeight, execInstr, hpc, hx, readRegs, hst, htd.symm]
      · cases hr : a.regs present <;>
          simp [copyWeight, execInstr, hpc, hr]
      · simp [copyWeight, execInstr, hpc, hsd.symm, hst.symm]
        omega
      · simp [copyWeight, execInstr, hpc, hsd, htd]
      · simp [copyWeight, execInstr, hpc]

private theorem copyWeight_trace {r s steps : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8}
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    copyWeight src dst tmp present b ≤ copyWeight src dst tmp present a := by
  induction ht with
  | refl => exact le_rfl
  | cons hs _ ih => exact ih.trans (copyWeight_step src dst tmp value present hsd hst htd hs)

theorem copyProgram_frame {r s steps : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) {a b : Cfg r s 8}
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b)
    (i : Fin s) (his : i ≠ src) (hid : i ≠ dst) (hit : i ≠ tmp) :
    b.stacks i = a.stacks i := by
  have hsingle {a b : Cfg r s 8}
      (hs : step (StackRoutines.copyProgram src dst tmp value present) a = some b) :
      b.stacks i = a.stacks i := by
    cases hpc : a.pc with
    | none => simp [step, hpc] at hs
    | some pc =>
        simp only [step, hpc, Option.map, Option.some.injEq] at hs
        rw [← hs]
        fin_cases pc <;> simp [execInstr, his, hid, hit]
  induction ht with
  | refl => rfl
  | cons hs _ ih => exact ih.trans (hsingle hs)

private theorem ports_le_copyWeight {r s : ℕ} (src dst tmp : Fin s) (present : Fin r)
    (a : Cfg r s 8) :
    (a.stacks src).length ≤ copyWeight src dst tmp present a ∧
    (a.stacks dst).length ≤ copyWeight src dst tmp present a ∧
    (a.stacks tmp).length ≤ copyWeight src dst tmp present a := by
  unfold copyWeight
  cases a.pc with
  | none => dsimp; omega
  | some pc => dsimp; split_ifs <;> omega

/-- Exact local copying never exceeds the source's original word length;
every off-port caller word retains its own independent bound. -/
theorem copyProgram_stack_bound {r s steps frameBound : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8} (hentry : a.pc = some 0)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = [])
    (hframe : ∀ i, i ≠ src → i ≠ dst → i ≠ tmp → (a.stacks i).length ≤ frameBound)
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ max (a.stacks src).length frameBound := by
  have hweight : copyWeight src dst tmp present b ≤ (a.stacks src).length := by
    have h := copyWeight_trace src dst tmp value present hsd hst htd ht
    simpa [copyWeight, hentry, hdst, htmp] using h
  obtain ⟨hsrc, hdst', htmp'⟩ := ports_le_copyWeight src dst tmp present b
  intro i
  by_cases hi : i = src
  · subst i
    exact (hsrc.trans hweight).trans (Nat.le_max_left _ _)
  by_cases hd : i = dst
  · subst i
    exact (hdst'.trans hweight).trans (Nat.le_max_left _ _)
  by_cases hw : i = tmp
  · subst i
    exact (htmp'.trans hweight).trans (Nat.le_max_left _ _)
  rw [copyProgram_frame src dst tmp value present ht i hi hd hw]
  exact (hframe i hi hd hw).trans (Nat.le_max_right _ _)

theorem copyProgram_no_growth {r s steps bound : ℕ} (src dst tmp : Fin s)
    (value present : Fin r) (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    {a b : Cfg r s 8} (hentry : a.pc = some 0)
    (hdst : a.stacks dst = []) (htmp : a.stacks tmp = [])
    (ha : ∀ i, (a.stacks i).length ≤ bound)
    (ht : Trace (StackRoutines.copyProgram src dst tmp value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ bound := by
  intro i
  exact (copyProgram_stack_bound src dst tmp value present hsd hst htd hentry hdst htmp
    (fun j _ _ _ => ha j) ht i).trans (max_le (ha src) le_rfl)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSBoundarySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical storage at the depth-first controller boundary.

Only framed formula bodies occur on the pending stack. The mathematical depth
is a proof index and is not serialized. Both children, the current formula,
the declared-variable word, and the two count words are charged simultaneously.
These bounds apply to the actual fixed frontier and accumulator routines after
injective port relocation. The final DFS must still establish its boundary
invariant and bounds for the concrete selector, splitter, and leaf commands.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace

open BitProgram StructuredCalls

/-- Actual cleanup never increases any stack, at any prefix. No bound on
elapsed time is needed: its finite table contains only pop, branch and halt. -/
theorem clearProgram_stack_length_le {r s steps : ℕ}
    (src : Fin s) (value present : Fin r) {a b : Cfg r s 3}
    (htrace : Trace (StackRoutines.clearProgram src value present) steps a b) :
    ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
  have hstep {a b : Cfg r s 3}
      (hs : step (StackRoutines.clearProgram src value present) a = some b) :
      ∀ i, (b.stacks i).length ≤ (a.stacks i).length := by
    cases hpc : a.pc with
    | none => simp [step, hpc] at hs
    | some label =>
        simp only [step, hpc, Option.map, Option.some.injEq] at hs
        rw [← hs]
        intro i
        fin_cases label
        · by_cases hi : i = src
          · subst i
            simp [execInstr]
          · simp [execInstr, hi]
        · simp [execInstr]
        · simp [execInstr]
  induction htrace with
  | refl => exact fun _ => le_rfl
  | cons hs ht ih => exact fun i => (ih i).trans (hstep hs i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

theorem restoreHighGuard_eval (a : Data) : Eval restoreHighGuard 1 a
    ⟨Function.update a.regs 21 true,a.stacks⟩ :=
  .base (StructuredProgram.Eval.atom (.set 21 true) a)

open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem copyHighCounter_eval (a : Data) :
    Eval copyHighCounter (copyHighCost a) a (copiedHighCounter a) := by
  have h1 := BankRoutines.clear_call_eval (330 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1
    (readRegs a.regs 0 1 none) (clearStacks 330 a.stacks)
  have h3 : Eval (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1))
      (7*(a.stacks 789).length+5)
      ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
        clearStacks 792 (clearStacks 330 a.stacks)⟩
      ⟨readRegs (readRegs (readRegs a.regs 0 1 none) 0 1 none) 0 1 none,
        copyStacks 789 330 (clearStacks 792 (clearStacks 330 a.stacks))⟩ := by
    apply Eval.call
    simpa only [clearStacks_frame 330 789 a.stacks (by decide),
      clearStacks_frame 792 789 (clearStacks 330 a.stacks) (by decide)] using
      ListRegisterProgram.copy_run (789 : Fin 896) 330 792 (0 : Fin 40) 1
        (by decide) (by decide) (by decide) (by decide)
        (readRegs (readRegs a.regs 0 1 none) 0 1 none)
        (clearStacks 792 (clearStacks 330 a.stacks)) (by simp)
  have hs : copyStacks 789 330 (clearStacks 792 (clearStacks 330 a.stacks)) =
      Function.update (Function.update a.stacks 330 (a.stacks 789)) 792 [] := by
    funext i
    by_cases h330 : i=330
    · subst i
      simp [copyStacks,clearStacks]
    · by_cases h792 : i=792
      · subst i
        simp [copyStacks,clearStacks]
      · simp [copyStacks,clearStacks,h330,h792]
  have hx := h1.seq (h2.seq h3)
  simp only [clearStacks_frame 330 792 a.stacks (by decide),hs,readRegs_reset] at hx
  convert hx using 1
  · rfl
  · dsimp [copyHighCost]
    omega
  · rfl


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Separate the retained caller envelope from each physical local input cap.
The local transient bound is never recycled as the next iteration's input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter

theorem clear_bound {r s : ℕ} (src : Fin s) (value present : Fin r)
    (a : State r s) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound)
    (input output : Fin s) :
    ∀ (q : ℕ) z, q ≤ 2 * (a.stacks src).length + 3 →
      Trace (compiled (.call (clearProgram src value present)) input output) q
        (a.withPC (some (compiled (.call (clearProgram src value present)) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have ht : Trace (clearProgram src value present) (2*(a.stacks src).length+3)
      (a.withPC (some (clearProgram src value present).entry))
      ((⟨readRegs a.regs value present none,clearStacks src a.stacks⟩ : State r s).withPC none) :=
    ListRegisterProgram.clear_run src value present a.regs a.stacks
  apply StructuredSpace.call_stack_bound _ _ _ _ (compiled_site (.call (clearProgram src value present)) input output) ht
  intro q z _ hz i
  exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le src value present hz i).trans (hb i)

theorem clear_state_bound {r s : ℕ} (src : Fin s) (value present : Fin r)
    (a : State r s) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((⟨readRegs a.regs value present none,clearStacks src a.stacks⟩ : State r s).stacks i).length≤bound := by
  intro i
  by_cases hi : i=src
  · subst i; simp
  · simpa only [clearStacks_frame src i a.stacks hi] using hb i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighBranchSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual high-condition staging uses a fixed local ten-stack footprint.
The independent physical cap is never identified with a sum of caller words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- Staging the durable counter into the old lower port is a restoring copy
with empty destination and temporary, so its all-stack envelope is unchanged. -/
theorem copy_high_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ (q : ℕ) z, q ≤ copyHighCost a → Trace (compiled copyHighCounter 789 703) q
      (a.withPC (some (compiled copyHighCounter 789 703).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  let b : Data := ⟨readRegs a.regs 0 1 none,clearStacks 330 a.stacks⟩
  let c : Data := ⟨readRegs b.regs 0 1 none,clearStacks 792 b.stacks⟩
  have h1 : Eval (.call (clearProgram (330 : Fin 896) (0 : Fin 40) 1))
      (2*(a.stacks 330).length+3) a b :=
    BankRoutines.clear_call_eval 330 0 1 a.regs a.stacks
  have h2 : Eval (.call (clearProgram (792 : Fin 896) (0 : Fin 40) 1))
      (2*(b.stacks 792).length+3) b c :=
    BankRoutines.clear_call_eval 792 0 1 b.regs b.stacks
  have h3 : Eval (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1))
      (7*(c.stacks 789).length+5) c
      ⟨readRegs c.regs 0 1 none,copyStacks 789 330 c.stacks⟩ :=
    .call _ (ListRegisterProgram.copy_run 789 330 792 0 1
      (by decide) (by decide) (by decide) (by decide) c.regs c.stacks (by simp [c]))
  have hb' : ∀ i, (b.stacks i).length≤bound := HighQuerySpace.clear_state_bound 330 0 1 a bound hb
  have hc' : ∀ i, (c.stacks i).length≤bound := HighQuerySpace.clear_state_bound 792 0 1 b bound hb'
  have hfirst := HighQuerySpace.clear_bound (330 : Fin 896) (0 : Fin 40) 1 a bound hb 789 703
  have hsecond := HighQuerySpace.clear_bound (792 : Fin 896) (0 : Fin 40) 1 b bound hb' 789 703
  have hthird : ∀ (q : ℕ) z, q ≤ 7 * (c.stacks 789).length + 5 →
      Trace (compiled (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1)) 789 703) q
        (c.withPC (some (compiled (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1)) 789 703).entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
    cases h3 with
    | call p tr =>
      apply StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1)) 789 703) tr
      intro q z _ hq
      exact CopySpace.copyProgram_no_growth 789 330 792 0 1
        (by decide) (by decide) (by decide) rfl (by simp [c, b, clearStacks])
        (by simp [c]) hc' hq
  have htail := StructuredSpace.sequence_stack_bound h2 h3 789 703 hsecond hthird
    _ _ _ (compiled_site (.seq (.call (clearProgram 792 0 1))
      (.call (copyProgram 789 330 792 0 1))) 789 703)
  have hwhole := StructuredSpace.sequence_stack_bound h1 (h2.seq h3) 789 703 hfirst htail
    _ _ _ (compiled_site copyHighCounter 789 703)
  have hc789 : c.stacks 789=a.stacks 789 := by simp [c,b,clearStacks]
  have hb792 : b.stacks 792=a.stacks 792 := by simp [b,clearStacks]
  intro q z hq hz
  apply hwhole q z _ hz
  rw [hc789,hb792]
  dsimp [copyHighCost] at hq
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLocalBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-only local costs for the physical high-count controller. Retained
caller words, including the outer marked accumulator322, do not enter them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter

/-- The durable high-counter refresh pays only for its source and destination
words; arbitrarily large retained collector words are irrelevant to time. -/
theorem copy_cost_le (a : Data) (L : ℕ)
    (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
    (h789 : (a.stacks 789).length ≤ L) : copyHighCost a ≤ 11 * L + 11 := by
  unfold copyHighCost
  omega

open HashGreedyProgram.NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
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

/-- This measured physical composition is the branch syntax used by highLoop.
The supplied evaluation is specifically the fixed stream command, not a query
oracle or a callback chosen by the caller. -/
theorem conditioned_eval (a b : Data) (n : ℕ)
    (he : Eval QueryStreamProgram.command n (copiedHighCounter a) b) :
    Eval conditioned (copyHighCost a + (n + 1)) a
      ⟨Function.update b.regs 21 true,b.stacks⟩ :=
  (copyHighCounter_eval a).seq (he.seq (restoreHighGuard_eval b))

open HashGreedyProgram.NativeRound

private theorem restore_space (a : Data) (B : ℕ)
    (hB : ∀ i, (a.stacks i).length ≤ B) : StageSpace restoreHighGuard 1 a B := by
  constructor
  intro k z hk hz i
  have hc : k = 0 ∨ k = 1 := by omega
  rcases hc with rfl | rfl
  · cases hz
    exact hB i
  · rw [trace_same_length_unique hz (compiled_trace (restoreHighGuard_eval a) 778 777)]
    exact hB i

/-- Local composition around the fixed stream command preserves a uniform
prefix envelope; the exponential high-iteration count never enters it. -/
theorem conditioned_resources_oai (a b : Data) (steps L D K : ℕ)
    (he : Eval QueryStreamProgram.command steps (copiedHighCounter a) b)
    (hs : StageSpace QueryStreamProgram.command steps (copiedHighCounter a) K)
    (hD : ∀ i, (a.stacks i).length ≤ D)
    (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
    (h789 : (a.stacks 789).length ≤ L) :
    Eval conditioned (copyHighCost a + (steps + 1)) a
      ⟨Function.update b.regs 21 true,b.stacks⟩ ∧
      copyHighCost a + (steps + 1) ≤ steps + 11 * L + 12 ∧
      StageSpace conditioned (copyHighCost a + (steps + 1) + 1) a (max D K) := by
  have hc : StageSpace copyHighCounter (copyHighCost a) a (max D K) := by
    constructor
    intro k z hk hz i
    exact (HighBranchSpace.copy_high_space a D hD k z hk hz i).trans (Nat.le_max_left _ _)
  have hq : StageSpace QueryStreamProgram.command steps (copiedHighCounter a) (max D K) :=
    ⟨fun k z hk hz i => (hs.bound k z hk hz i).trans (Nat.le_max_right _ _)⟩
  have hb : ∀ i, (b.stacks i).length ≤ max D K := by
    intro i
    exact hq.bound steps _ le_rfl (compiled_trace he 778 777) i
  have hr := restoreHighGuard_eval b
  have htail := StageSpace.seq he hr hq (restore_space b _ hb)
  have hwhole := StageSpace.seq (copyHighCounter_eval a) (he.seq hr) hc htail
  have hout := conditioned_eval a b steps he
  have htime := HighQueryLocalBounds.copy_cost_le a L h330 h792 h789
  exact ⟨hout,by omega,⟨StructuredSpace.compiled_halt_stack_bound hout 778 777 hwhole.bound⟩⟩

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.conditioned_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.conditioned_resources_oai
