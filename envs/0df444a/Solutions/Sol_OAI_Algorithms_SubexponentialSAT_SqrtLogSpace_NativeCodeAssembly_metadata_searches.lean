-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:53:24.101007+00:00
-- url     : https://prove2.me/submissions/21809172-74e8-4cdd-a959-772a1d272c05

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeCode_graph_call
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeCode_local_call

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

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

theorem copy_call_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk htmp

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem route_eval (p : Route) (hp : routeValid p) (a : Data)
    (ht : a.stacks 767 = []) : Eval (route p) (routeCost p a) a (routed p a) := by
  obtain ⟨hsd,hst,hdt⟩ := hp
  have hc := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
  have hsrc : clearStacks p.2 a.stacks p.1 = a.stacks p.1 :=
    clearStacks_frame _ _ _ hsd
  have htmp : clearStacks p.2 a.stacks 767 = [] := by
    rw [clearStacks_frame _ _ _ (Ne.symm hdt),ht]
  have hf := BankRoutines.copy_call_eval p.1 p.2 (767 : Fin 896) (0 : Fin 40) 1
    hsd hst (Ne.symm hdt) (by decide) (readRegs a.regs 0 1 none)
    (clearStacks p.2 a.stacks) htmp
  have he : copyStacks p.1 p.2 (clearStacks p.2 a.stacks) =
      Function.update a.stacks p.2 (a.stacks p.1) := by
    funext i
    by_cases hi : i = p.2
    · subst i; simp [copyStacks,clearStacks,hsd]
    · simp [copyStacks,clearStacks,hi]
  have hcost : 2*(a.stacks p.2).length+3+(7*(a.stacks p.1).length+5) = routeCost p a := by
    unfold routeCost
    omega
  simpa only [route,routed,hsrc,he,readRegs_reset,hcost] using hc.seq hf

theorem routes_eval (ps : List Route) (hp : ∀ p ∈ ps, routeValid p)
    (a : Data) (ht : a.stacks 767 = []) :
    Eval (routes ps) (routesCost ps a) a (routesState ps a) := by
  induction ps generalizing a with
  | nil =>
    have h := BankRoutines.clear_call_eval (767 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
    simpa only [routes,routesCost,routesState,ht,List.length_nil,Nat.mul_zero,
      Nat.zero_add,BankRoutines.clearStacks_eq_self_of_empty _ _ ht] using h
  | cons p ps ih =>
    have h := hp p (by simp)
    have htmp : (routed p a).stacks 767 = [] := by
      simpa only [routed,Function.update_of_ne (Ne.symm h.2.2)] using ht
    exact (route_eval p h a ht).seq (ih (fun q hq => hp q (by simp [hq])) (routed p a) htmp)

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

theorem routes_cost_bound (ps : List Route) (a : Data) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    routesCost ps a ≤ ps.length*(9*B+8)+3 := by
  induction ps generalizing a with
  | nil => simp [routesCost]
  | cons p ps ih =>
    have hb' : ∀ i, ((routed p a).stacks i).length ≤ B := by
      intro i
      by_cases h : i=p.2
      · subst i; simpa [routed] using hb p.1
      · simpa [routed,h] using hb i
    have hh := ih (routed p a) hb'
    have h1 := hb p.1
    have h2 := hb p.2
    simp only [routesCost,routeCost,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeaf
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual adapters for the streamed counting leaf. Both initial code rows
and newly generated rows use the canonical modulus word's exact width. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf

open BitProgram StructuredCalls
open SqrtLog.LeafOuterProgram

/-- Each concrete route clears its destination before copying, so its
temporary and destination fit the original source-word envelope. -/
theorem route_space (p : Route) (hp : routeValid p) {steps B : ℕ} {a b : Data}
    (he : Eval (route p) steps a b) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (route p) 784 788) prefixSteps
        (a.withPC (some (compiled (route p) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  obtain ⟨hsd, hst, hdt⟩ := hp
  cases he with
  | @seq _ _ n m _ middle _ first second =>
      have hclear := BankRoutines.clear_call_eval p.2 (0 : Fin 40) 1 a.regs a.stacks
      have hmiddle := SubexpPrimeProgram.eval_result_unique first hclear 784 788
      subst hmiddle
      have hfirst : ∀ prefixSteps c, prefixSteps ≤ n →
          Trace (compiled (.call (StackRoutines.clearProgram p.2 0 1)) 784 788) prefixSteps
            (a.withPC (some (compiled (.call (StackRoutines.clearProgram p.2 0 1)) 784 788).entry)) c →
          ∀ i, (c.stacks i).length ≤ B := by
        cases first with
        | call routine ht =>
            apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram p.2 0 1)
              (compiled (.call (StackRoutines.clearProgram p.2 0 1)) 784 788)
              (siteAddress (.call (StackRoutines.clearProgram p.2 0 1)))
              (exitAddress (.call (StackRoutines.clearProgram p.2 0 1)))
              (compiled_site (.call (StackRoutines.clearProgram p.2 0 1)) 784 788) ht
            intro prefixSteps c _ hc i
            exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
              p.2 0 1 hc i).trans (ha i)
      have hbound := hfirst _ _ le_rfl (compiled_trace first 784 788)
      have hsecond : ∀ prefixSteps c, prefixSteps ≤ m →
          Trace (compiled (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788) prefixSteps
            ((⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks p.2 a.stacks⟩ : Data).withPC
              (some (compiled (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788).entry)) c →
          ∀ i, (c.stacks i).length ≤ B := by
        cases second with
        | call routine ht =>
            apply StructuredSpace.call_stack_bound (StackRoutines.copyProgram p.1 p.2 767 0 1)
              (compiled (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788)
              (siteAddress (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)))
              (exitAddress (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)))
              (compiled_site (.call (StackRoutines.copyProgram p.1 p.2 767 0 1)) 784 788) ht
            intro prefixSteps c _ hc
            apply CopySpace.copyProgram_no_growth p.1 p.2 767 0 1 hsd hst hdt.symm rfl
              (by simp [StackRoutines.clearStacks])
              (by simpa [StructuredProgram.State.withPC, StackRoutines.clearStacks, hdt.symm] using hs) hbound hc
      exact StructuredSpace.sequence_stack_bound first second 784 788 hfirst hsecond
        (compiled (route p) 784 788) (siteAddress (route p)) (exitAddress (route p))
        (compiled_site (route p) 784 788)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed physical stages for the streamed local-code and graph-code searches.
The retained search state is confined to the lower48 leaf stacks; selected
matrices are saved outside that bank before its paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram

private theorem clear_call_space (port : Fin 896) {steps B : ℕ} {a b : Data}
    (he : Eval (.call (StackRoutines.clearProgram port 0 1)) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ steps →
      Trace (compiled (.call (StackRoutines.clearProgram port 0 1)) 784 788) k
        (a.withPC (some (compiled (.call (StackRoutines.clearProgram port 0 1)) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram port 0 1)
        (compiled (.call (StackRoutines.clearProgram port 0 1)) 784 788)
        (siteAddress (.call (StackRoutines.clearProgram port 0 1)))
        (exitAddress (.call (StackRoutines.clearProgram port 0 1)))
        (compiled_site (.call (StackRoutines.clearProgram port 0 1)) 784 788) ht
      intro k c _ hc i
      exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le
        port 0 1 hc i).trans (ha i)

private theorem clear_bank_space (ports : List (Fin 896)) {steps B : ℕ} {a b : Data}
    (he : Eval (BankRoutines.clearCmd 767 0 1 ports) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ steps →
      Trace (compiled (BankRoutines.clearCmd 767 0 1 ports) 784 788) k
        (a.withPC (some (compiled (BankRoutines.clearCmd 767 0 1 ports) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  induction ports generalizing steps a b with
  | nil => exact clear_call_space 767 he ha
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst := clear_call_space port first ha
          have hmiddle := hfirst _ _ le_rfl (compiled_trace first 784 788)
          exact StructuredSpace.sequence_stack_bound first second 784 788 hfirst
            (ih second hmiddle)
            (compiled (BankRoutines.clearCmd 767 0 1 (port :: rest)) 784 788)
            (siteAddress (BankRoutines.clearCmd 767 0 1 (port :: rest)))
            (exitAddress (BankRoutines.clearCmd 767 0 1 (port :: rest)))
            (compiled_site (BankRoutines.clearCmd 767 0 1 (port :: rest)) 784 788)

theorem lowerPorts_eq : lowerPorts = (List.finRange 48).map (Fin.castAdd 848) :=
  lowerPortsWrapped.2

private theorem mem_lowerPorts (i : Fin 896) : i ∈ lowerPorts ↔ i.val < 48 := by
  rw [lowerPorts_eq]
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem clearLower_eval (a : Data) (hs : a.stacks 767 = []) :
    Eval clearLower (clearLowerSteps a) a (clearedLower a) := by
  have hn : lowerPorts.Nodup := by
    rw [lowerPorts_eq]
    exact List.Nodup.map (Fin.castAdd_injective 48 848) (List.nodup_finRange 48)
  simpa [clearLower, clearedLower, clearLowerSteps, lowerPorts_eq] using
    BankRoutines.clear_eval 767 (0 : Fin 40) 1 lowerPorts hn a.regs a.stacks hs

theorem clearedLower_empty (a : Data) (i : Fin 896) (hi : i.val < 48) :
    (clearedLower a).stacks i = [] := by
  simp [clearedLower, BankRoutines.clearBankStacks, (mem_lowerPorts i).mpr hi]

theorem clearedLower_frame (a : Data) (i : Fin 896) (hi : 48 ≤ i.val) :
    (clearedLower a).stacks i = a.stacks i := by
  simp [clearedLower, BankRoutines.clearBankStacks, mem_lowerPorts, Nat.not_lt.mpr hi]

theorem clearLower_time (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    clearLowerSteps a ≤ 96 * B + 147 := by
  have hsum : (lowerPorts.map (fun i => (a.stacks i).length)).sum ≤ lowerPorts.length * B := by
    simpa only [List.length_map, smul_eq_mul] using
      (List.sum_le_card_nsmul (lowerPorts.map (fun i => (a.stacks i).length)) B (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact ha i))
  have hlen : lowerPorts.length = 48 := by simp [lowerPorts_eq]
  rw [hlen] at hsum
  unfold clearLowerSteps
  omega

theorem clearLower_space (a : Data) (B : ℕ) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ clearLowerSteps a → Trace (compiled clearLower 784 788) k
      (a.withPC (some (compiled clearLower 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B :=
  clear_bank_space lowerPorts (clearLower_eval a hs) ha

theorem routes_bound (ps : List Route) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((routesState ps a).stacks i).length ≤ B := by
  induction ps generalizing a with
  | nil => exact ha
  | cons p ps ih =>
      apply ih
      intro i
      by_cases hi : i = p.2
      · subst i
        simpa [routed] using ha p.1
      · simpa [routed, hi] using ha i

theorem graphInputs_valid : ∀ p ∈ graphInputs, routeValid p := by
  intro p hp
  simp only [graphInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals unfold routeValid; decide

theorem localInputs_valid : ∀ p ∈ localInputs, routeValid p := by
  intro p hp
  simp only [localInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals unfold routeValid; decide

private theorem graphInputs_frame (a : Data) (i : Fin 896)
    (h30 : i ≠ 30) (h31 : i ≠ 31) (h32 : i ≠ 32) (h33 : i ≠ 33) (h46 : i ≠ 46) :
    (routesState graphInputs a).stacks i = a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [graphInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  all_goals apply Ne.symm; assumption

private theorem localInputs_frame (a : Data) (i : Fin 896)
    (h19 : i ≠ 19) (h20 : i ≠ 20) (h21 : i ≠ 21) (h46 : i ≠ 46) :
    (routesState localInputs a).stacks i = a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [localInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals apply Ne.symm; assumption

theorem graph_prepared (a : Data) (D r : ℕ)
    (hblank : ∀ i : Fin 896, i.val < 48 → a.stacks i = [])
    (hD : a.stacks 808 = List.replicate D true)
    (hr : a.stacks 812 = List.replicate r true) :
    CodeChecks.GraphMatrixReady D r (a.stacks 800) (a.stacks 801)
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks
        (routesState graphInputs a)) := by
  have empty (i : Fin 896) (hi : i.val < 48)
      (h30 : i ≠ 30) (h31 : i ≠ 31) (h32 : i ≠ 32) (h33 : i ≠ 33) (h46 : i ≠ 46) :
      (routesState graphInputs a).stacks i = [] :=
    (graphInputs_frame a i h30 h31 h32 h33 h46).trans (hblank i hi)
  constructor
  · intro i
    apply empty _ (by change i.val < 48; omega)
    all_goals intro h; have := congrArg Fin.val h; change i.val = _ at this; omega
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed, hD]
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed]
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed]
  · simp [projectState, SparseCodeSearch.leafStacks, graphInputs, routesState, routed, hr]
  all_goals simp only [projectState, SparseCodeSearch.leafStacks, Function.comp_apply]
  all_goals apply empty
  all_goals decide

theorem local_prepared (a : Data) (t D d : ℕ)
    (hblank : ∀ i : Fin 896, i.val < 48 → a.stacks i = [])
    (ht : a.stacks 809 = List.replicate t true)
    (hd : a.stacks 811 = List.replicate d true)
    (hD : a.stacks 808 = List.replicate D true) :
    CodeChecks.LocalMatrixReady t D d
      (projectState SparseCodeSearch.leafRegisters SparseCodeSearch.leafStacks
        (routesState localInputs a)) := by
  have empty (i : Fin 896) (hi : i.val < 48)
      (h19 : i ≠ 19) (h20 : i ≠ 20) (h21 : i ≠ 21) (h46 : i ≠ 46) :
      (routesState localInputs a).stacks i = [] :=
    (localInputs_frame a i h19 h20 h21 h46).trans (hblank i hi)
  constructor
  · intro i
    apply empty _ (by change i.val < 48; omega)
    all_goals intro h; have := congrArg Fin.val h; change i.val = _ at this; omega
  · simp [projectState, SparseCodeSearch.leafStacks, localInputs, routesState, routed, ht]
  · simp [projectState, SparseCodeSearch.leafStacks, localInputs, routesState, routed, hd]
  · simp [projectState, SparseCodeSearch.leafStacks, localInputs, routesState, routed, hD]
  all_goals simp only [projectState, SparseCodeSearch.leafStacks, Function.comp_apply]
  all_goals apply empty
  all_goals decide


theorem routes_space (ps : List Route) (hp : ∀ p ∈ ps, routeValid p)
    (a : Data) (B : ℕ) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ routesCost ps a → Trace (compiled (routes ps) 784 788) k
      (a.withPC (some (compiled (routes ps) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  induction ps generalizing a with
  | nil => exact clear_call_space 767 (routes_eval [] hp a hs) ha
  | cons p ps ih =>
      have hvalid := hp p (by simp)
      have htail : ∀ q ∈ ps, routeValid q := fun q hq => hp q (by simp [hq])
      have htmp : (routed p a).stacks 767 = [] := by
        simpa [routed, hvalid.2.2.symm] using hs
      have hbound : ∀ i, ((routed p a).stacks i).length ≤ B := by
        intro i
        by_cases hi : i = p.2
        · subst i; simpa [routed] using ha p.1
        · simpa [routed, hi] using ha i
      exact StructuredSpace.sequence_stack_bound
        (route_eval p hvalid a hs) (routes_eval ps htail (routed p a) htmp) 784 788
        (NativeLeaf.route_space p hvalid (route_eval p hvalid a hs) hs ha)
        (ih htail (routed p a) htmp hbound)
        (compiled (routes (p :: ps)) 784 788) (siteAddress (routes (p :: ps)))
        (exitAddress (routes (p :: ps))) (compiled_site (routes (p :: ps)) 784 788)

theorem saveAndClear_eval (source target : Fin 896) (hp : routeValid (source, target))
    (a : Data) (hs : a.stacks 767 = []) :
    Eval (saveAndClear source target) (saveAndClearSteps source target a)
      a (savedAndCleared source target a) := by
  have htmp : (routed (source, target) a).stacks 767 = [] := by
    simpa [routed, hp.2.2.symm] using hs
  exact (route_eval (source, target) hp a hs).seq (clearLower_eval _ htmp)

theorem saveAndClear_bound (source target : Fin 896) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((savedAndCleared source target a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i.val < 48
  · simp [savedAndCleared, clearedLower_empty _ i hi]
  · rw [savedAndCleared, clearedLower_frame _ i (by omega)]
    by_cases hit : i = target
    · subst i; simpa [routed] using ha source
    · simpa [routed, hit] using ha i

theorem saveAndClear_time (source target : Fin 896) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    saveAndClearSteps source target a ≤ 105 * B + 155 := by
  have hr : ∀ i, ((routed (source, target) a).stacks i).length ≤ B := by
    intro i
    by_cases hi : i = target
    · subst i; simpa [routed] using ha source
    · simpa [routed, hi] using ha i
  have hc := clearLower_time (routed (source, target) a) B hr
  have hsrc := ha source
  have htgt := ha target
  dsimp [saveAndClearSteps, routeCost]
  omega

theorem saveAndClear_space (source target : Fin 896) (hp : routeValid (source, target))
    (a : Data) (B : ℕ) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ k c, k ≤ saveAndClearSteps source target a →
      Trace (compiled (saveAndClear source target) 784 788) k
        (a.withPC (some (compiled (saveAndClear source target) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ B := by
  have htmp : (routed (source, target) a).stacks 767 = [] := by
    simpa [routed, hp.2.2.symm] using hs
  have hr : ∀ i, ((routed (source, target) a).stacks i).length ≤ B := by
    intro i
    by_cases hi : i = target
    · subst i; simpa [routed] using ha source
    · simpa [routed, hi] using ha i
  exact StructuredSpace.sequence_stack_bound
    (route_eval (source, target) hp a hs) (clearLower_eval _ htmp) 784 788
    (NativeLeaf.route_space (source, target) hp (route_eval (source, target) hp a hs) hs ha)
    (clearLower_space _ B htmp hr)
    (compiled (saveAndClear source target) 784 788) (siteAddress (saveAndClear source target))
    (exitAddress (saveAndClear source target)) (compiled_site (saveAndClear source target) 784 788)


private theorem run_save_clear (routine : Cmd 40 896) (source target : Fin 896)
    (hslo : source.val < 48) (hthi : 48 ≤ target.val)
    (hp : routeValid (source, target)) {steps A P : ℕ} {a b : Data}
    (he : Eval routine steps a b) (hs : a.stacks 767 = [])
    (hf : ∀ i, i ≠ source → b.stacks i = a.stacks i)
    (hb : ∀ i, (b.stacks i).length ≤ A)
    (hspace : ∀ k c, k ≤ steps → Trace (compiled routine 784 788) k
      (a.withPC (some (compiled routine 784 788).entry)) c → ∀ i, (c.stacks i).length ≤ P) :
    Eval (.seq routine (saveAndClear source target))
      (steps + saveAndClearSteps source target b) a (savedAndCleared source target b) ∧
    (savedAndCleared source target b).stacks target = b.stacks source ∧
    (∀ i : Fin 896, i.val < 48 → (savedAndCleared source target b).stacks i = []) ∧
    (∀ i : Fin 896, 48 ≤ i.val → i ≠ target →
      (savedAndCleared source target b).stacks i = a.stacks i) ∧
    (∀ i, ((savedAndCleared source target b).stacks i).length ≤ A) ∧
    ∀ k c, k ≤ steps + saveAndClearSteps source target b →
      Trace (compiled (.seq routine (saveAndClear source target)) 784 788) k
        (a.withPC (some (compiled (.seq routine (saveAndClear source target)) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ max P A := by
  have htmp : b.stacks 767 = [] := (hf 767 (by intro h; have := congrArg Fin.val h; simp at this; omega)).trans hs
  have he2 := saveAndClear_eval source target hp b htmp
  refine ⟨he.seq he2, ?_, ?_, ?_, saveAndClear_bound source target b A hb, ?_⟩
  · rw [savedAndCleared, clearedLower_frame _ target hthi]
    simp [routed]
  · intro i hi
    exact clearedLower_empty _ i hi
  · intro i hi hne
    rw [savedAndCleared, clearedLower_frame _ i hi]
    change Function.update b.stacks target (b.stacks source) i = a.stacks i
    rw [Function.update_of_ne hne]
    apply hf
    intro h; have := congrArg Fin.val h; omega
  · apply StructuredSpace.sequence_stack_bound he he2 784 788
      (fun k c hk hc i => (hspace k c hk hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (saveAndClear_space source target hp b A htmp hb k c hk hc i).trans
        (Nat.le_max_right _ _))
      (compiled (.seq routine (saveAndClear source target)) 784 788)
      (siteAddress (.seq routine (saveAndClear source target)))
      (exitAddress (.seq routine (saveAndClear source target)))
      (compiled_site (.seq routine (saveAndClear source target)) 784 788)

private theorem route_run_save_clear (inputs : List Route) (routine : Cmd 40 896)
    (source target : Fin 896) (hinputs : ∀ p ∈ inputs, routeValid p)
    (hlower : ∀ p ∈ inputs, p.2.val < 48)
    (hslo : source.val < 48) (hthi : 48 ≤ target.val)
    (hp : routeValid (source, target)) {steps A B P : ℕ} {a b : Data}
    (he : Eval routine steps (routesState inputs a) b) (hs : a.stacks 767 = [])
    (ha : ∀ i, (a.stacks i).length ≤ A)
    (hf : ∀ i, i ≠ source → b.stacks i = (routesState inputs a).stacks i)
    (hb : ∀ i, (b.stacks i).length ≤ B)
    (hspace : ∀ k c, k ≤ steps → Trace (compiled routine 784 788) k
      ((routesState inputs a).withPC (some (compiled routine 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ P) :
    Eval (.seq (routes inputs) (.seq routine (saveAndClear source target)))
      (routesCost inputs a + (steps + saveAndClearSteps source target b))
      a (savedAndCleared source target b) ∧
    (savedAndCleared source target b).stacks target = b.stacks source ∧
    (∀ i : Fin 896, i.val < 48 → (savedAndCleared source target b).stacks i = []) ∧
    (∀ i : Fin 896, 48 ≤ i.val → i ≠ target →
      (savedAndCleared source target b).stacks i = a.stacks i) ∧
    (∀ i, ((savedAndCleared source target b).stacks i).length ≤ B) ∧
    ∀ k c, k ≤ routesCost inputs a + (steps + saveAndClearSteps source target b) →
      Trace (compiled (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788) k
        (a.withPC (some (compiled (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ max A (max P B) := by
  have htmp : (routesState inputs a).stacks 767 = [] := by
    rw [routes_frame inputs a 767 (by
      intro p hp h
      have := hlower p hp
      have := congrArg Fin.val h
      simp at this
      omega)]
    exact hs
  obtain ⟨he2, hout, hblank, hframe, hbound, hprefix⟩ :=
    run_save_clear routine source target hslo hthi hp he htmp hf hb hspace
  refine ⟨(routes_eval inputs hinputs a hs).seq he2, hout, hblank, ?_, hbound, ?_⟩
  · intro i hi hne
    rw [hframe i hi hne]
    apply routes_frame
    intro p hp h
    have := hlower p hp
    have := congrArg Fin.val h
    omega
  · exact StructuredSpace.sequence_stack_bound (routes_eval inputs hinputs a hs) he2 784 788
      (fun k c hk hc i => (routes_space inputs hinputs a A hs ha k c hk hc i).trans
        (Nat.le_max_left _ _))
      (fun k c hk hc i => (hprefix k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788)
      (siteAddress (.seq (routes inputs) (.seq routine (saveAndClear source target))))
      (exitAddress (.seq (routes inputs) (.seq routine (saveAndClear source target))))
      (compiled_site (.seq (routes inputs) (.seq routine (saveAndClear source target))) 784 788)


theorem graph_stage {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hq : BinaryArithmetic.toNat (a.stacks 800) = SparseCode.gapDenom m occurrence)
    (hDb : BinaryArithmetic.toNat (a.stacks 801) = SparseCode.degree m occurrence)
    (hD : a.stacks 808 = List.replicate (SparseCode.degree m occurrence) true)
    (hr : a.stacks 812 = List.replicate (SparseCode.dimension m occurrence) true)
    (hDr : a.stacks 813 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence)),
      steps ≤ graphStageTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
      Eval graphStage steps a out ∧ out.stacks 816 = matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) Q ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 816 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.degree m occurrence * SparseCode.dimension m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled graphStage 784 788) k
        (a.withPC (some (compiled graphStage 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ graphStageSpace A m occurrence
          (a.stacks 800).length (a.stacks 801).length := by
  have h31 : (routesState graphInputs a).stacks 31 = a.stacks 800 := by
    simp [graphInputs, routesState, routed]
  have h32 : (routesState graphInputs a).stacks 32 = a.stacks 801 := by
    simp [graphInputs, routesState, routed]
  have h46 : (routesState graphInputs a).stacks 46 = a.stacks 813 := by
    simp [graphInputs, routesState, routed]
  have hlow (i : Fin 896) (hi : i.val < 48) : a.stacks i = [] := hblank i (by omega)
  have hother (i : Fin 896) (hi : i = 40 ∨ i = 41 ∨ i = 42) :
      (routesState graphInputs a).stacks i = [] := by
    rcases hi with rfl | rfl | rfl
    all_goals rw [graphInputs_frame a _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    all_goals exact hblank _ (by decide)
  obtain ⟨steps, mid, Q, ht, he, hQ, hgood, hframe, hbound, hprefix⟩ :=
    graph_call hm hocc A (routesState graphInputs a) (by rw [h31]; exact hq)
      (by rw [h32]; exact hDb) (by
        rw [h31, h32]
        exact graph_prepared a _ _ hlow hD hr)
      (routes_bound graphInputs a A ha) (h46.trans hDr)
      (hother 40 (Or.inl rfl)) (hother 41 (Or.inr (Or.inl rfl)))
      (hother 42 (Or.inr (Or.inr rfl)))
  have hlower : ∀ p ∈ graphInputs, p.2.val < 48 := by
    intro p hp
    simp only [graphInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  obtain ⟨hexec, hout, hempty, hframe2, hb, hp⟩ := route_run_save_clear graphInputs graphCall
    29 816 graphInputs_valid hlower (by decide) (by decide) (by unfold routeValid; decide)
    he (hblank 767 (by decide)) ha hframe hbound hprefix
  refine ⟨_, _, Q, ?_, hexec, hout.trans hQ, hgood, ?_, ?_, hb, ?_⟩
  · have hroute := routes_cost_bound graphInputs a A ha
    have hsave := saveAndClear_time 29 816 mid _ hbound
    rw [h31, h32] at ht
    simpa only [graphStageTime, graphInputs, List.length_cons, List.length_nil] using
      Nat.add_le_add hroute (Nat.add_le_add ht hsave)
  · intro i hi
    by_cases hlo : i.val < 48
    · exact hempty i hlo
    · rw [hframe2 i (by omega) (by intro h; have := congrArg Fin.val h; simp at this; omega)]
      exact hblank i hi
  · intro i hi hne
    exact hframe2 i (by omega) hne
  · simpa only [graphStage, graphStageSpace, saveAndClear, h31, h32] using hp


theorem local_stage {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (ht : a.stacks 809 = List.replicate (SparseCode.localRows m occurrence) true)
    (hd : a.stacks 811 = List.replicate
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) true)
    (hD : a.stacks 808 = List.replicate (SparseCode.degree m occurrence) true)
    (htD : a.stacks 810 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true) :
    ∃ (steps : ℕ) (out : Data)
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ localStageTime A m occurrence ∧
      Eval localStage steps a out ∧ out.stacks 815 = matrixFrames Q ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ SparseCodeSearch.boundary A
        (SparseCode.localRows m occurrence * SparseCode.degree m occurrence)) ∧
      ∀ k c, k ≤ steps → Trace (compiled localStage 784 788) k
        (a.withPC (some (compiled localStage 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ localStageSpace A m occurrence := by
  have h46 : (routesState localInputs a).stacks 46 = a.stacks 810 := by
    simp [localInputs, routesState, routed]
  have hlow (i : Fin 896) (hi : i.val < 48) : a.stacks i = [] := hblank i (by omega)
  have hother (i : Fin 896) (hi : i = 40 ∨ i = 41 ∨ i = 42) :
      (routesState localInputs a).stacks i = [] := by
    rcases hi with rfl | rfl | rfl
    all_goals rw [localInputs_frame a _ (by decide) (by decide) (by decide) (by decide)]
    all_goals exact hblank _ (by decide)
  obtain ⟨steps, mid, Q, htime, he, hQ, hgood, hframe, hbound, hprefix⟩ :=
    local_call hm hocc A (routesState localInputs a) (local_prepared a _ _ _ hlow ht hd hD)
      (routes_bound localInputs a A ha) (h46.trans htD)
      (hother 40 (Or.inl rfl)) (hother 41 (Or.inr (Or.inl rfl)))
      (hother 42 (Or.inr (Or.inr rfl)))
  have hlower : ∀ p ∈ localInputs, p.2.val < 48 := by
    intro p hp
    simp only [localInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  obtain ⟨hexec, hout, hempty, hframe2, hb, hp⟩ := route_run_save_clear localInputs localCall
    18 815 localInputs_valid hlower (by decide) (by decide) (by unfold routeValid; decide)
    he (hblank 767 (by decide)) ha hframe hbound hprefix
  refine ⟨_, _, Q, ?_, hexec, hout.trans hQ, hgood, ?_, ?_, hb, hp⟩
  · have hroute := routes_cost_bound localInputs a A ha
    have hsave := saveAndClear_time 18 815 mid _ hbound
    simpa only [localStageTime, localInputs, List.length_cons, List.length_nil] using
      Nat.add_le_add hroute (Nat.add_le_add htime hsave)
  · intro i hi
    by_cases hlo : i.val < 48
    · exact hempty i hlo
    · rw [hframe2 i (by omega) (by intro h; have := congrArg Fin.val h; simp at this; omega)]
      exact hblank i hi
  · intro i hi hne
    exact hframe2 i (by omega) hne


/-- Both searched matrices are physically retained for serialization. The
second search starts from the polynomial matrix boundary, independently of
how many losing candidates the first search visited. -/
theorem searches_eval {m occurrence : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (A : ℕ) (a : Data) (ha : ∀ i, (a.stacks i).length ≤ A)
    (hblank : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hq : BinaryArithmetic.toNat (a.stacks 800) = SparseCode.gapDenom m occurrence)
    (hDb : BinaryArithmetic.toNat (a.stacks 801) = SparseCode.degree m occurrence)
    (hD : a.stacks 808 = List.replicate (SparseCode.degree m occurrence) true)
    (ht : a.stacks 809 = List.replicate (SparseCode.localRows m occurrence) true)
    (htD : a.stacks 810 = List.replicate
      (SparseCode.localRows m occurrence * SparseCode.degree m occurrence) true)
    (hd : a.stacks 811 = List.replicate
      (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) true)
    (hr : a.stacks 812 = List.replicate (SparseCode.dimension m occurrence) true)
    (hDr : a.stacks 813 = List.replicate
      (SparseCode.degree m occurrence * SparseCode.dimension m occurrence) true) :
    ∃ (steps : ℕ) (out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ searchesTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
      Eval searches steps a out ∧ out.stacks 816 = matrixFrames shifts ∧
      out.stacks 815 = matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → i ≠ 816 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ searchBoundary A m occurrence) ∧
      ∀ k c, k ≤ steps → Trace (compiled searches 784 788) k
        (a.withPC (some (compiled searches 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ searchesSpace A m occurrence
          (a.stacks 800).length (a.stacks 801).length := by
  obtain ⟨ng, g, shifts, hng, heg, hshifts, hgood, hgb, hgf, hgBound, hgSpace⟩ :=
    graph_stage hm hocc A a ha hblank hq hDb hD hr hDr
  have lg (i : Fin 896) (hi : i ≠ 816) (hhi : 768 ≤ i.val) : g.stacks i = a.stacks i := hgf i hhi hi
  obtain ⟨nl, out, Q, hnl, hel, hQ, hdist, houtblank, houtframe, houtbound, houtspace⟩ :=
    local_stage hm hocc (graphBoundary A m occurrence) g hgBound hgb
      ((lg 809 (by decide) (by decide)).trans ht)
      ((lg 811 (by decide) (by decide)).trans hd)
      ((lg 808 (by decide) (by decide)).trans hD)
      ((lg 810 (by decide) (by decide)).trans htD)
  refine ⟨ng + nl, out, shifts, Q, Nat.add_le_add hng hnl, heg.seq hel,
    (houtframe 816 (by decide) (by decide)).trans hshifts, hQ, hgood, hdist,
    houtblank, ?_, houtbound, ?_⟩
  · intro i hi h815 h816
    exact (houtframe i hi h815).trans (hgf i hi h816)
  · exact StructuredSpace.sequence_stack_bound heg hel 784 788
      (fun k c hk hc i => (hgSpace k c hk hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (houtspace k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled searches 784 788) (siteAddress searches) (exitAddress searches)
      (compiled_site searches 784 788)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

theorem worker_empty (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] := by
  intro i hi
  have h := he ⟨i.val, hi⟩
  simpa [workerStack] using h

theorem metadata_searches_oai {m occurrence A : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (a : Data) (he : WorkerEmpty a) (hmeta : Metadata m occurrence a)
    (ha : ∀ i, (a.stacks i).length ≤ A) :
    ∃ (steps : ℕ) (out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      steps ≤ NativeCode.searchesTime A m occurrence (a.stacks 800).length (a.stacks 801).length ∧
      Eval NativeCode.searches steps a out ∧ out.stacks 816 = CodeSearchProgram.matrixFrames shifts ∧
      out.stacks 815 = CodeSearchProgram.matrixFrames Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, i.val < 768 → out.stacks i = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → i ≠ 816 → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ NativeCode.searchBoundary A m occurrence) ∧
      ∀ k c, k ≤ steps → Trace (compiled NativeCode.searches 784 788) k
        (a.withPC (some (compiled NativeCode.searches 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ NativeCode.searchesSpace A m occurrence
          (a.stacks 800).length (a.stacks 801).length := by
  apply NativeCode.searches_eval hm hocc A a ha (worker_empty a he) hmeta.q
  · exact hmeta.binary 0
  · exact hmeta.unary 0
  · exact hmeta.unary 1
  · exact hmeta.unary 2
  · exact hmeta.unary 3
  · exact hmeta.unary 4
  · have h := hmeta.unary 5
    change a.stacks 813 = List.replicate
      (SparseCode.dimension m occurrence * SparseCode.degree m occurrence) true at h
    simpa only [Nat.mul_comm] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches_oai
