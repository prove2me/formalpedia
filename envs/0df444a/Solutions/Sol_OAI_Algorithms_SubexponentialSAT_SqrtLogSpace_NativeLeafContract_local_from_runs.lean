-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:40:33.722141+00:00
-- url     : https://prove2.me/submissions/2f64e563-679a-4eaa-9d26-2bffeb64f4e9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics_history_count
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
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

theorem count_le (F : CNF V) : count F ≤ 2 ^ Fintype.card V := by
  calc
    count F ≤ (Finset.univ : Finset (Assignment V)).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card V := by simp [Assignment ]

end Finite
end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

theorem masterRoutes_valid : ∀ p ∈ masterRoutes, routeValid p := by
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl <;> unfold routeValid <;> decide

theorem stageFinal_eval (a : Data) (ht : a.stacks 767=[]) :
    Eval stageFinal (stageFinalCost a) a (finalStaged a) :=
  routes_eval masterRoutes masterRoutes_valid a ht

theorem finalStaged_sources (a : Data) :
    (finalStaged a).stacks 700=a.stacks 784 ∧
    (finalStaged a).stacks 701=a.stacks 777 ∧
    (finalStaged a).stacks 707=a.stacks 782 ∧
    (finalStaged a).stacks 708=a.stacks 783 ∧
    (finalStaged a).stacks 709=a.stacks 785 := by
  simp [finalStaged,masterRoutes,routesState,routed]

theorem finalStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (finalStaged a).stacks i=a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact Ne.symm h0
  · exact Ne.symm h7
  · exact Ne.symm h8
  · exact Ne.symm h9
  · exact Ne.symm h1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStaged
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram LeafOuterProgram
open HashMassAdapter

theorem cleanup_eval (a : State 40 896) (ht : a.stacks 767 = []) :
    Eval cleanup (cleanupCost a) a (cleaned a) := by
  simpa only [cleanup, cleanupCost, cleaned, stagedPorts, List.length_cons, List.length_nil] using
    BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 stagedPorts (by decide) a.regs a.stacks ht

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

theorem temporary_eval (a : State 40 896) :
    Eval clearTemporary (2 * (a.stacks 767).length + 3) a (temporaryCleared a) :=
  BankRoutines.clear_call_eval (767 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks

theorem temporary_frame (a : State 40 896) (i : Fin 896) (hi : i ≠ 767) :
    (temporaryCleared a).stacks i = a.stacks i := clearStacks_frame _ _ _ hi

theorem temporary_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((temporaryCleared a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i = 767
  · subst i; simp [temporaryCleared]
  · simpa only [temporary_frame a i hi] using ha i

theorem stage_eval (a : State 40 896) : Eval stage (stageCost a) a (staged a) :=
  (temporary_eval a).seq (LeafOuterNative.stageFinal_eval (temporaryCleared a) (by simp [temporaryCleared]))

theorem cleanup_eval (a : State 40 896) : Eval cleanup (cleanupCost a) a (cleaned a) :=
  (temporary_eval a).seq (HashMassStaged.cleanup_eval (temporaryCleared a) (by simp [temporaryCleared]))

theorem staged_sources (a : State 40 896) :
    (staged a).stacks 700 = a.stacks 784 ∧
    (staged a).stacks 701 = a.stacks 777 ∧
    (staged a).stacks 707 = a.stacks 782 ∧
    (staged a).stacks 708 = a.stacks 783 ∧
    (staged a).stacks 709 = a.stacks 785 := by
  simpa only [staged, temporary_frame _ 784 (by decide), temporary_frame _ 777 (by decide),
    temporary_frame _ 782 (by decide), temporary_frame _ 783 (by decide),
    temporary_frame _ 785 (by decide)] using LeafOuterNative.finalStaged_sources (temporaryCleared a)

theorem staged_frame (a : State 40 896) (i : Fin 896)
    (hi : i ∉ HashMassStaged.stagedPorts) (ht : i ≠ 767) :
    (staged a).stacks i = a.stacks i := by
  have hn : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [HashMassStaged.stagedPorts] using hi
  exact (LeafOuterNative.finalStaged_frame _ i hn.1 hn.2.1
    hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2).trans (temporary_frame a i ht)

theorem staged_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((staged a).stacks i).length ≤ B := by
  intro i
  have h := staged_sources a
  by_cases h0 : i = 700
  · subst i; rw [h.1]; exact ha 784
  by_cases h1 : i = 701
  · subst i; rw [h.2.1]; exact ha 777
  by_cases h7 : i = 707
  · subst i; rw [h.2.2.1]; exact ha 782
  by_cases h8 : i = 708
  · subst i; rw [h.2.2.2.1]; exact ha 783
  by_cases h9 : i = 709
  · subst i; rw [h.2.2.2.2]; exact ha 785
  change ((LeafOuterNative.finalStaged (temporaryCleared a)).stacks i).length ≤ B
  rw [LeafOuterNative.finalStaged_frame _ i h0 h1 h7 h8 h9]
  exact temporary_bound a B ha i

theorem stage_cost_le (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : stageCost a ≤ 47 * B + 46 := by
  have h := routes_cost_bound LeafOuterNative.masterRoutes (temporaryCleared a) B
    (temporary_bound a B ha)
  have ht := ha 767
  change LeafOuterNative.stageFinalCost (temporaryCleared a) ≤ 5 * (9 * B + 8) + 3 at h
  unfold stageCost
  omega

theorem cleaned_frame (a : State 40 896) (i : Fin 896)
    (hi : i ∉ HashMassStaged.stagedPorts) (ht : i ≠ 767) :
    (cleaned a).stacks i = a.stacks i := by
  exact (BankRoutines.clearBankStacks_frame i HashMassStaged.stagedPorts
    (temporaryCleared a).stacks hi).trans (temporary_frame a i ht)

theorem cleaned_count (a : State 40 896) : (cleaned a).stacks 788 = a.stacks 788 :=
  cleaned_frame a 788 (by decide) (by decide)

theorem cleaned_empty (a : State 40 896) (i : Fin 896)
    (hi : i ∈ HashMassStaged.stagedPorts) : (cleaned a).stacks i = [] :=
  BankRoutines.clearBankStacks_mem i HashMassStaged.stagedPorts (temporaryCleared a).stacks hi

theorem cleaned_temporary (a : State 40 896) : (cleaned a).stacks 767 = [] := by
  change BankRoutines.clearBankStacks HashMassStaged.stagedPorts (temporaryCleared a).stacks 767 = []
  rw [BankRoutines.clearBankStacks_frame _ _ _ (by decide)]
  simp [temporaryCleared]

theorem cleaned_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((cleaned a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i ∈ HashMassStaged.stagedPorts
  · rw [cleaned_empty a i hi]; simp
  · change (BankRoutines.clearBankStacks HashMassStaged.stagedPorts
      (temporaryCleared a).stacks i).length ≤ B
    rw [BankRoutines.clearBankStacks_frame i HashMassStaged.stagedPorts
      (temporaryCleared a).stacks hi]
    exact temporary_bound a B ha i

theorem cleanup_cost_le (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : cleanupCost a ≤ 14 * B + 24 := by
  have hc : (HashMassStaged.stagedPorts.map
      (fun i => ((temporaryCleared a).stacks i).length)).sum ≤ 6 * B := by
    have h := List.sum_le_card_nsmul
      (HashMassStaged.stagedPorts.map (fun i => ((temporaryCleared a).stacks i).length)) B
      (by intro x hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact temporary_bound a B ha i)
    simpa [HashMassStaged.stagedPorts] using h
  have ht := ha 767
  unfold cleanupCost HashMassStaged.cleanupCost
  omega

/-- Cleanup removes only the physical staging buffers and temporary. If the
actual query restores its other inputs, the complete count is the sole change. -/
theorem restored_stacks (a b : State 40 896) (count : List Bool)
    (ht : a.stacks 767 = []) (he : ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [])
    (hb : b.stacks = Function.update (staged a).stacks 788 count) :
    (cleaned b).stacks = Function.update a.stacks 788 count := by
  funext i
  by_cases hi : i ∈ HashMassStaged.stagedPorts
  · have hn : i ≠ 788 := by
      intro h; subst i; exact (by decide : (788 : Fin 896) ∉ HashMassStaged.stagedPorts) hi
    rw [cleaned_empty b i hi, Function.update_of_ne hn, he i hi]
  · by_cases ht' : i = 767
    · subst i
      rw [cleaned_temporary, Function.update_of_ne (by decide : (767 : Fin 896) ≠ 788), ht]
    · rw [cleaned_frame b i hi ht', hb]
      by_cases hc : i = 788
      · subst i; simp
      · rw [Function.update_of_ne hc, Function.update_of_ne hc, staged_frame a i hi ht']

private theorem sequence_prefix {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : ∀ p q, p ≤ n → Trace (compiled first 784 788) p
      (a.withPC (some (compiled first 784 788).entry)) q → ∀ i, (q.stacks i).length ≤ bound)
    (hsecond : ∀ p q, p ≤ m → Trace (compiled second 784 788) p
      (b.withPC (some (compiled second 784 788).entry)) q → ∀ i, (q.stacks i).length ≤ bound) :
    ∀ p q, p ≤ n + m → Trace (compiled (.seq first second) 784 788) p
      (a.withPC (some (compiled (.seq first second) 784 788).entry)) q →
      ∀ i, (q.stacks i).length ≤ bound :=
  StructuredSpace.sequence_stack_bound hf hs 784 788 hfirst hsecond
    (compiled (.seq first second) 784 788) (siteAddress _) (exitAddress _)
    (compiled_site _ 784 788)

/-- Actual evaluation and prefix proofs of the chosen query compose without
using its possibly exponential duration as a storage bound. -/
theorem run_of_eval (query : Cmd 40 896) (a b : State 40 896) (n B C : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hb : ∀ i, (b.stacks i).length ≤ B)
    (hq : Eval query n (staged a) b)
    (hspace : ∀ p z, p ≤ n → Trace (compiled query 784 788) p
      ((staged a).withPC (some (compiled query 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ C) :
    let steps := stageCost a + (n + cleanupCost b)
    Eval (command query) steps a (cleaned b) ∧
      steps + 1 ≤ n + 61 * B + 71 ∧
      Trace (compiled (command query) 784 788) (steps + 1)
        (a.withPC (some (compiled (command query) 784 788).entry)) ((cleaned b).withPC none) ∧
      (cleaned b).stacks 788 = b.stacks 788 ∧
      (∀ i, ((cleaned b).stacks i).length ≤ B) ∧
      ∀ p z, p ≤ steps + 1 → Trace (compiled (command query) 784 788) p
        (a.withPC (some (compiled (command query) 784 788).entry)) z →
        ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
  dsimp only
  have hs := stage_eval a
  have hc := cleanup_eval b
  have whole := hs.seq (hq.seq hc)
  have hst := stage_cost_le a B ha
  have hct := cleanup_cost_le b B hb
  have hsbound : ∀ p z, p ≤ stageCost a → Trace (compiled stage 784 788) p
      (a.withPC (some (compiled stage 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
    intro p z hp hz i
    have h := StructuredSpace.local_stack_bound (compiled stage 784 788)
      (steps := 47 * B + 46) (StreamResources.dataBits_le_mul _ ha) p z (hp.trans hst) hz i
    exact h.trans (le_max_of_le_right (by omega))
  have hcbound : ∀ p z, p ≤ cleanupCost b → Trace (compiled cleanup 784 788) p
      (b.withPC (some (compiled cleanup 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
    intro p z hp hz i
    have h := StructuredSpace.local_stack_bound (compiled cleanup 784 788)
      (steps := 14 * B + 24) (StreamResources.dataBits_le_mul _ hb) p z (hp.trans hct) hz i
    exact h.trans (le_max_of_le_right (by omega))
  have hqbound : ∀ p z, p ≤ n → Trace (compiled query 784 788) p
      ((staged a).withPC (some (compiled query 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ max C (1000 * B + 100) := by
    intro p z hp hz i
    exact (hspace p z hp hz i).trans (le_max_left _ _)
  refine ⟨whole, by omega, compiled_halt_trace whole 784 788,
    cleaned_count b, cleaned_bound b B hb, ?_⟩
  exact StructuredSpace.compiled_halt_stack_bound whole 784 788
    (sequence_prefix hs (hq.seq hc) hsbound (sequence_prefix hq hc hqbound hcbound))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

theorem countWord_count_length {n : ℕ} (F : SAT.CNF (Fin n)) :
    (countWord (SAT.count F)).length ≤ n + 1 :=
  countWord_length_le (by simpa using SAT.count_le F)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem ready_low {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] :=
  NativeCodeAssembly.worker_empty a hr.worker

theorem ready_staging {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [] := by
  intro i hi
  apply ready_low hr i
  simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The final query is run on the saved history alone and its complete count
word is retained. The equality below never reads a single count bit as SAT. -/
theorem accepted_count {n B : ℕ} (F : DisjointReuse.RawCNF n)
    (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (query : Cmd 40 896) (base selected middle : State 40 896) (steps L K : ℕ)
    (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
    (hselected : RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
    (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
    (he : Eval query steps (AcceptedQueryStage.staged selected) middle)
    (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
      (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
          (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
    (hp : StageSpace query steps (AcceptedQueryStage.staged selected) K) :
    ∃ t out, t + 1 ≤ steps + 61 * L + 71 ∧
      Eval (AcceptedQueryStage.command query) t selected out ∧
      out.stacks = Function.update selected.stacks 788 (countWord (DisjointReuse.rawCount F)) ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      StageSpace (AcceptedQueryStage.command query) (t + 1) selected (max K (1000 * L + 100)) := by
  have hc := NativeLeafSemantics.history_count F hm hB shifts Q hs hQ
  rw [hc] at hword
  have hb : ∀ i, (middle.stacks i).length ≤ L := by
    intro i
    rw [hword]
    by_cases hi : i = 788
    · subst i
      rw [Function.update_self]
      exact (countWord_count_length (ExecCNF.formulaSet F)).trans hn
    rw [Function.update_of_ne hi]
    exact AcceptedQueryStage.staged_bound selected L ha i
  have ht : selected.stacks 767 = [] :=
    (hselected.frame 767 (by decide) (by decide)).trans (ready_low hr 767 (by decide))
  have hz : ∀ i ∈ HashMassStaged.stagedPorts, selected.stacks i = [] := by
    intro i hi
    have hne : i ≠ 777 ∧ i ≠ 781 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hselected.frame i hne.1 hne.2).trans (ready_staging hr i hi)
  obtain ⟨heval,hcost,_htrace,_hcount,hbound,hprefix⟩ :=
    AcceptedQueryStage.run_of_eval query selected middle steps L K ha hb he hp.bound
  exact ⟨_,_,hcost,heval,AcceptedQueryStage.restored_stacks selected middle _ ht hz hword,
    hbound,⟨hprefix⟩⟩

/-- Compose the real rounds and real final query; each phase contributes its
independent storage cap rather than its duration. -/
theorem afterPreparation_eval (marked accepted : Cmd 40 896)
    (base selected out : State 40 896) (roundSteps querySteps roundCap queryCap : ℕ)
    (hr : Eval (roundsCommand marked) roundSteps base selected)
    (hq : Eval (AcceptedQueryStage.command accepted) querySteps selected out)
    (sr : StageSpace (roundsCommand marked) (roundSteps + 1) base roundCap)
    (sq : StageSpace (AcceptedQueryStage.command accepted) (querySteps + 1) selected queryCap) :
    Eval (afterPreparation marked accepted) (roundSteps + querySteps) base out ∧
      Trace (compiled (afterPreparation marked accepted) 784 788) (roundSteps + querySteps + 1)
        (base.withPC (some (compiled (afterPreparation marked accepted) 784 788).entry))
        (out.withPC none) ∧
      StageSpace (afterPreparation marked accepted) (roundSteps + querySteps + 1) base
        (max roundCap queryCap) := by
  have he := hr.seq hq
  refine ⟨he,compiled_halt_trace he 784 788,⟨?_⟩⟩
  apply StructuredSpace.compiled_halt_stack_bound he 778 777
  exact StructuredSpace.sequence_stack_bound hr hq 778 777
    (fun k c hk hc i => (sr.bound k c (by omega) hc i).trans (Nat.le_max_left _ _))
    (fun k c hk hc i => (sq.bound k c (by omega) hc i).trans (Nat.le_max_right _ _))
    _ _ _ (compiled_site _ 778 777)

/-- The actual preparation prefix and complete count suffix form one source
program. This theorem includes the final source halt before primitive lifting. -/
theorem command_of_evals (marked accepted : Cmd 40 896)
    (a prepared out : State 40 896) (prepareSteps runSteps prepareCap runCap : ℕ)
    (hp : Eval NativeLeafPreparation.command prepareSteps a prepared)
    (hr : Eval (afterPreparation marked accepted) runSteps prepared out)
    (sp : ∀ k c, k ≤ prepareSteps → Trace (compiled NativeLeafPreparation.command 784 788) k
      (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) c →
      ∀ i, (c.stacks i).length ≤ prepareCap)
    (sr : StageSpace (afterPreparation marked accepted) (runSteps + 1) prepared runCap) :
    Eval (command marked accepted) (prepareSteps + runSteps) a out ∧
      Trace (compiled (command marked accepted) 784 788) (prepareSteps + runSteps + 1)
        (a.withPC (some (compiled (command marked accepted) 784 788).entry)) (out.withPC none) ∧
      ∀ k c, k ≤ prepareSteps + runSteps + 1 → Trace (compiled (command marked accepted) 784 788) k
        (a.withPC (some (compiled (command marked accepted) 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max prepareCap runCap := by
  have he := hp.seq hr
  refine ⟨he,compiled_halt_trace he 784 788,?_⟩
  apply StructuredSpace.compiled_halt_stack_bound he 784 788
  exact StructuredSpace.sequence_stack_bound hp hr 784 788
    (fun k c hk hc i => (sp k c hk hc i).trans (Nat.le_max_left _ _))
    (fun k c hk hc i => (sr.bound k c (by omega) hc i).trans (Nat.le_max_right _ _))
    _ _ _ (compiled_site _ 784 788)

/-- Exact raw count, literal tape word, measured source duration and uniform
source-prefix storage for the actual greedy-plus-accepted-query suffix. -/
theorem continuation_count {n B : ℕ} (F : DisjointReuse.RawCNF n)
    (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (marked accepted : Cmd 40 896) (base selected middle : State 40 896)
    (roundSteps querySteps L roundCap queryCap : ℕ)
    (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
    (hselected : RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
    (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
    (er : Eval (roundsCommand marked) roundSteps base selected)
    (sr : StageSpace (roundsCommand marked) (roundSteps + 1) base roundCap)
    (eq : Eval accepted querySteps (AcceptedQueryStage.staged selected) middle)
    (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
      (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
          (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
    (sq : StageSpace accepted querySteps (AcceptedQueryStage.staged selected) queryCap) :
    ∃ steps out, steps + 1 ≤ roundSteps + querySteps + 61 * L + 71 ∧
      Eval (afterPreparation marked accepted) steps base out ∧
      out.stacks = Function.update selected.stacks 788 (countWord (DisjointReuse.rawCount F)) ∧
      out.stacks 788 = countWord (DisjointReuse.rawCount F) ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      Trace (compiled (afterPreparation marked accepted) 784 788) (steps + 1)
        (base.withPC (some (compiled (afterPreparation marked accepted) 784 788).entry))
        (out.withPC none) ∧
      StageSpace (afterPreparation marked accepted) (steps + 1) base
        (max roundCap (max queryCap (1000 * L + 100))) := by
  obtain ⟨t,out,ht,he,hout,hbound,hprefix⟩ :=
    accepted_count F hm hB shifts Q hs hQ accepted base selected middle querySteps L queryCap
      hr hselected ha hn eq hword sq
  obtain ⟨whole,htrace,hspace⟩ := afterPreparation_eval marked accepted base selected out
    roundSteps t roundCap (max queryCap (1000 * L + 100)) er he sr hprefix
  exact ⟨_,out,by omega,whole,hout,by rw [hout,Function.update_self],hbound,htrace,hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform correctness and resources for the fixed native leaf. The final
contract instantiates the actual preparation, marked rounds and accepted
query; only numerical bounds produced by the outer program remain. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

open SqrtLog HashGreedyProgram.NativeRound HashGreedyRound in
/-- The actual preparation, same staged rounds and separate accepted query
produce one fixed local leaf run. The time counts every phase, including the
paid accepted staging/cleanup; space uses the maximum of independent caps.
The queried history is exactly the attained history returned by those rounds. -/
theorem local_from_runs_oai {n B : ℕ} (k : ℕ) (F : RawCNF n)
    (hm : 0 < F.length) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B)
    (hs : WalshExistence.Good (SparseCode.gapDenom F.length B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree F.length B / (100 * B * SparseCode.logSize F.length) + 1))
    (a base selected middle : State 40 896)
    (prepareSteps roundSteps querySteps L prepareCap roundCap queryCap : ℕ)
    (ep : Eval NativeLeafPreparation.command prepareSteps a base)
    (sp : ∀ t z, t ≤ prepareSteps →
      Trace (compiled NativeLeafPreparation.command 784 788) t
        (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) z →
      ∀ i, (z.stacks i).length ≤ prepareCap)
    (hr : NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) base)
    (hselected : RowBoundary base
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
        (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)) selected)
    (ha : ∀ i, (selected.stacks i).length ≤ L) (hn : n + 1 ≤ L)
    (er : Eval (NativeLeafRun.roundsCommand (HighQueryProgram.marked k)) roundSteps base selected)
    (sr : StageSpace (NativeLeafRun.roundsCommand (HighQueryProgram.marked k))
      (roundSteps + 1) base roundCap)
    (eq : Eval (HighQueryProgram.accepted k) querySteps (AcceptedQueryStage.staged selected) middle)
    (hword : middle.stacks = Function.update (AcceptedQueryStage.staged selected).stacks 788
      (countWord (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F) (SparseCode.distanceDenom F.length B)
          (HashGreedyCode.initial shifts Q) (HashSelect.loopCap n F.length)))))
    (sq : StageSpace (HighQueryProgram.accepted k) querySteps
      (AcceptedQueryStage.staged selected) queryCap) :
    ∃ steps out,
      steps + 1 ≤ prepareSteps + roundSteps + querySteps + 61 * L + 71 ∧
      Eval (NativeLeafProgram.localCommand k) steps a out ∧
      out.stacks = Function.update selected.stacks 788 (countWord (rawCount F)) ∧
      out.stacks 788 = countWord (rawCount F) ∧
      (∀ i, (out.stacks i).length ≤ L) ∧
      ∀ t z, t ≤ steps + 1 → Trace (NativeLeafProgram.localProgram k) t
        (a.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
        ∀ i, (z.stacks i).length ≤
          max prepareCap (max roundCap (max queryCap (1000 * L + 100))) := by
  obtain ⟨steps, out, ht, he, hout, hcount, hbound, _, hp⟩ :=
    NativeLeafRun.continuation_count F hm hB shifts Q hs hQ
      (HighQueryProgram.marked k) (HighQueryProgram.accepted k) base selected middle
      roundSteps querySteps L roundCap queryCap hr hselected ha hn er sr eq hword sq
  obtain ⟨whole, _, hprefix⟩ := NativeLeafRun.command_of_evals
    (HighQueryProgram.marked k) (HighQueryProgram.accepted k) a base out
    prepareSteps steps prepareCap (max roundCap (max queryCap (1000 * L + 100))) ep he sp hp
  exact ⟨prepareSteps + steps, out, by omega, whole, hout, hcount, hbound, hprefix⟩

open SqrtLog Filter
open scoped Topology

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs_oai
