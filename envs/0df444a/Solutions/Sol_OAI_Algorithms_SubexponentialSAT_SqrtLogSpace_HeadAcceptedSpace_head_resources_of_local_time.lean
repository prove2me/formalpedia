-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:26:05.632436+00:00
-- url     : https://prove2.me/submissions/ee3baec7-8131-42fc-8d1e-3b7ac6e822fc

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumSpace_scan_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem clear_eval (d : Data) (src : Fin 896) :
    Eval (clear src) (2*(d.stacks src).length+3) d (clearState d src) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram


theorem seq_space {c e : Code} {n m B : ℕ} {a b d : Data}
    (hc : Eval c n a b) (he : Eval e m b d)
    (hcb : (∀ q z, q ≤ n → Trace (compiled c 860 860) q
      (a.withPC (some (compiled c 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) (heb : (∀ q z, q ≤ m → Trace (compiled e 860 860) q
      (b.withPC (some (compiled e 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B)) :
    (∀ q z, q ≤ (n+m) → Trace (compiled (.seq c e) 860 860) q
      (a.withPC (some (compiled (.seq c e) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) :=
  StructuredSpace.sequence_stack_bound hc he 860 860 hcb heb
    (compiled (.seq c e) 860 860) (siteAddress (.seq c e)) (exitAddress (.seq c e))
    (compiled_site (.seq c e) 860 860)

theorem clear_space {n B : ℕ} {a b : Data} (src : Fin 896)
    (he : Eval (clear src) n a b) (ha : ∀ i, (a.stacks i).length≤B) :
    (∀ q z, q ≤ n → Trace (compiled (clear src) 860 860) q
      (a.withPC (some (compiled (clear src) 860 860).entry)) z → ∀ i, (z.stacks i).length ≤ B) := by
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _
      (compiled_site (clear src) 860 860) tr
    intro q z _ hq i
    exact (DisjointReuse.SparseDFSBoundarySpace.clearProgram_stack_length_le src 0 1 hq i).trans (ha i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Sharp storage bounds for binary head-assignment controllers. Only the
counter's retained word length enters the local controller budget; every other
caller stack retains the same envelope throughout arbitrarily many visits. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

open HeadEvaluationProgram.StagedGate

/-- The complete scan cost is a fixed polynomial factor times `2^h`. -/
theorem scan_budget_le (h bound cost : ℕ) :
    (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) + 2 * bound + 22 * h + 30 ≤
      2 ^ h * (2 * cost + 2 * bound + 54 * h + 96) := by
  have hp : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by decide)
  have hc : cost ≤ 2 ^ h * cost := by nlinarith
  have hb : bound ≤ 2 ^ h * bound := by nlinarith
  have hh : h ≤ 2 ^ h * h := by nlinarith
  nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

private theorem workPorts_eq :
    workPorts = List.ofFn (fun i : Fin 56 => i.castAdd 840) ++ controllerPorts :=
  workPortsData.2

private theorem workPorts_nodup : workPorts.Nodup := by
  rw [workPorts_eq]
  decide

private theorem workPorts_length : workPorts.length = 61 := by
  rw [workPorts_eq]
  decide

theorem mem_workPorts (i : Fin 896) :
    i ∈ workPorts ↔ i.val < 56 ∨ i ∈ controllerPorts := by
  rw [workPorts_eq]
  simp only [List.mem_append]
  apply or_congr_left
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact j.isLt
  · intro hi
    exact List.mem_ofFn.mpr ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem clearWork_eval (a : Data) : Eval clearWork (clearWorkCost a) a (cleared a) := by
  have hfirst := clear_eval a 31
  have hrest := BankRoutines.clear_eval (31 : Fin 896) (0 : Fin 40) 1 workPorts
    workPorts_nodup
    (readRegs a.regs 0 1 none) (clearStacks 31 a.stacks) (by simp)
  have he : BankRoutines.clearBankStacks workPorts (clearStacks 31 a.stacks) =
      BankRoutines.clearBankStacks workPorts a.stacks := by
    funext i
    by_cases hi : i ∈ workPorts
    · simp [BankRoutines.clearBankStacks, hi]
    · have h31 : i ≠ 31 := by
        intro h
        subst i
        exact hi ((mem_workPorts 31).mpr (Or.inl (by decide)))
      simp [BankRoutines.clearBankStacks, clearStacks, hi, h31]
  have hrun := hfirst.seq hrest
  rw [he, readRegs_reset] at hrun
  simpa only [clearWork, clearWorkCost, cleared, workPorts_length] using hrun

theorem cleared_low (a : Data) (i : Fin 56) :
    (cleared a).stacks (i.castAdd 840) = [] :=
  BankRoutines.clearBankStacks_mem _ _ _ ((mem_workPorts _).mpr (Or.inl i.isLt))

theorem cleared_controller (a : Data) (i : Fin 896) (hi : i ∈ controllerPorts) :
    (cleared a).stacks i = [] :=
  BankRoutines.clearBankStacks_mem _ _ _ ((mem_workPorts _).mpr (Or.inr hi))

theorem cleared_frame (a : Data) (i : Fin 896) (hi : 56 ≤ i.val)
    (hc : i ∉ controllerPorts) :
    (cleared a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame _ _ _ (by
    rw [mem_workPorts]
    exact not_or.mpr ⟨by omega, hc⟩)

theorem clearWorkCost_le (a : Data) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound) : clearWorkCost a ≤ 124 * bound + 189 := by
  have hsum : (workPorts.map (fun i => (clearStacks 31 a.stacks i).length)).sum ≤
      61 * bound := by
    apply (List.sum_le_card_nsmul _ bound (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      by_cases hi : i = 31
      · subst i
        simp [clearStacks]
      · simpa [clearStacks, hi] using hb i)).trans_eq
    simp [workPorts_eq, controllerPorts]
  have h31 := hb 31
  unfold clearWorkCost
  omega

private theorem bank_clear_prefix (ports : List (Fin 896)) {steps bound : ℕ}
    {a b : Data} (he : Eval (BankRoutines.clearCmd 31 0 1 ports) steps a b)
    (hb : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled (BankRoutines.clearCmd 31 0 1 ports) 860 860) q
      (a.withPC (some (compiled (BankRoutines.clearCmd 31 0 1 ports) 860 860).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil => exact clear_space 31 he hb
  | cons p ps ih =>
      cases he with
      | seq hfirst hrest =>
          have hs := clear_space p hfirst hb
          have hmiddle := hs _ _ le_rfl (compiled_trace hfirst 860 860)
          exact seq_space hfirst hrest hs (ih hrest hmiddle)

/-- Paid entry cleanup never enlarges any caller stack, at any source prefix. -/
theorem clearWork_prefix {steps bound : ℕ} {a b : Data}
    (he : Eval clearWork steps a b) (hb : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled clearWork 860 860) q
      (a.withPC (some (compiled clearWork 860 860).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  cases he with
  | seq hfirst hrest =>
      have hs := clear_space 31 hfirst hb
      have hmiddle := hs _ _ le_rfl (compiled_trace hfirst 860 860)
      exact seq_space hfirst hrest hs (bank_clear_prefix workPorts hrest hmiddle)

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix bounds for the concrete accepted-head assignment path. Every local
physical cap is independent of the retained caller envelope. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace

open BitProgram StructuredCalls HighQueryAdapter

open CounterPrograms CounterForPrograms

/-- Entry cleanup, every head assignment, and controller reclamation all
share one source trace and one unchanged caller envelope. The complete cost
includes both cleanup phases and has a fixed polynomial factor times `2^h`. -/
theorem head_resources (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
        (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts (HeadSumProgram.seeded (HeadSumAssembly.cleared a)))) :
    ∃ steps e,
      Trace (HeadSumAssembly.headProgram accepted) steps
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      Eval (HeadSumAssembly.head accepted) (steps - 1) a (HeadSumProgram.finalized e) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 * cost + 126 * bound + 54 * h + 286) * 2 ^ h ∧
      ∀ q z, q ≤ steps → Trace (HeadSumAssembly.headProgram accepted) q
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hclear := HeadSumAssembly.clearWork_eval a
  have hclearPrefix := HeadSumAssembly.clearWork_prefix hclear hframe
  have hcleared := hclearPrefix _ _ le_rfl (compiled_trace hclear 860 860)
  have hshape' : (HeadSumAssembly.cleared a).stacks 651 = List.replicate h false := by
    rw [HeadSumAssembly.cleared_frame a 651 (by decide) (by decide)]
    exact hshape
  have hcursor' : (HeadSumAssembly.cleared a).stacks 859 = [] :=
    HeadSumAssembly.cleared_controller a 859 (by decide)
  have hfuel' : (HeadSumAssembly.cleared a).stacks 860 = [] :=
    HeadSumAssembly.cleared_controller a 860 (by decide)
  have hscratch' : (HeadSumAssembly.cleared a).stacks 861 = [] :=
    HeadSumAssembly.cleared_controller a 861 (by decide)
  have htemp' : (HeadSumAssembly.cleared a).stacks 31 = [] :=
    HeadSumAssembly.cleared_low a 31
  obtain ⟨ns, e, hs, hI, hout, h859, h860, h861, htime, hspace⟩ :=
    HeadSumSpace.scan_resources accepted I h bound cost hcursorI hbound hbudget spec
      hcallback (HeadSumAssembly.cleared a) hshape' hcursor' hfuel' hscratch' htemp'
      hcleared hi
  have hcall : Eval (.call (HeadSumProgram.scanProgram accepted)) ns
      (HeadSumAssembly.cleared a) (HeadSumProgram.finalized e) := Eval.call _ hs
  have hcallPrefix : ∀ q z, q ≤ ns →
      Trace (compiled (.call (HeadSumProgram.scanProgram accepted)) 860 860) q
        ((HeadSumAssembly.cleared a).withPC
          (some (compiled (.call (HeadSumProgram.scanProgram accepted)) 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound :=
    StructuredSpace.call_stack_bound _ _ _ _
      (compiled_site (.call (HeadSumProgram.scanProgram accepted)) 860 860) hs hspace
  have hwhole := hclear.seq hcall
  have hfull := StructuredSpace.sequence_stack_bound hclear hcall 860 860
    hclearPrefix hcallPrefix (HeadSumAssembly.headProgram accepted)
    (siteAddress (HeadSumAssembly.head accepted)) (exitAddress (HeadSumAssembly.head accepted))
    (compiled_site (HeadSumAssembly.head accepted) 651 853)
  have hscanTime := htime.trans (HeadSumSpace.scan_budget_le h bound cost)
  have hentryTime := HeadSumAssembly.clearWorkCost_le a bound hframe
  have hp : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by decide)
  have hentryMul : 124 * bound + 190 ≤ (124 * bound + 190) * 2 ^ h := by
    nlinarith
  refine ⟨_, e, compiled_halt_trace hwhole 651 853, ?_, hI, hout, h859, h860, h861, ?_, ?_⟩
  · simpa only [HeadSumAssembly.head, Nat.add_sub_cancel] using hwhole
  · nlinarith
  · exact StructuredSpace.compiled_halt_stack_bound hwhole 651 853 hfull

/-- A single polynomial-time assignment evaluation may charge its bounded
boundary data once. The budget must be discharged by that actual local run;
this estimate is not applied to the exponential head loop. -/
theorem bounded_local_prefix (command : Cmd 40 896) (a : State 40 896)
    {steps inputCap budget bound : ℕ} (htime : steps ≤ budget)
    (hinput : ∀ i, (a.stacks i).length ≤ inputCap)
    (hlocal : 896 * inputCap + budget ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled command 860 860) q
      (a.withPC (some (compiled command 860 860).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  have hin : dataBits (a.withPC (some (compiled command 860 860).entry)) ≤ 896 * inputCap :=
    StreamResources.dataBits_le_mul _ hinput
  intro q z hq hz i
  exact (StructuredSpace.local_stack_bound (compiled command 860 860)
    (steps := budget) hin q z (hq.trans htime) hz i).trans hlocal

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram

/-- A polynomial local body can be charged from its compact semantic boundary.
This discharges the resource callback for the whole exponential scan without
using its accumulated runtime in the space bound. -/
theorem head_resources_of_local_time_oai (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h inputCap bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hcompact : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ inputCap)
    (hlocal : 896 * inputCap + cost ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts
      (HeadSumProgram.seeded (HeadSumAssembly.cleared a)))) :
    ∃ steps e,
      Trace (HeadSumAssembly.headProgram accepted) steps
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      Eval (HeadSumAssembly.head accepted) (steps - 1) a (HeadSumProgram.finalized e) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 * cost + 126 * bound + 54 * h + 286) * 2 ^ h ∧
      ∀ q z, q ≤ steps → Trace (HeadSumAssembly.headProgram accepted) q
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hcap : inputCap ≤ bound := by omega
  apply head_resources accepted I h bound cost hcursorI
    (fun i d hd j => (hcompact i d hd j).trans hcap) hbudget spec
    ?_ a hshape hframe hi
  intro i d e nb hI hs hf he
  obtain ⟨nb', e', ht, he', _, _, _⟩ := spec i d hI hs hf
  have hn := StreamResources.eval_steps_eq (860 : Fin 896) 860 he he'
  exact bounded_local_prefix (HeadSumProgram.body accepted) d
    (by omega : nb ≤ cost) (hcompact i d hI) hlocal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time_oai
