-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:42:57.176468+00:00
-- url     : https://prove2.me/submissions/722d6984-9571-438d-a9f7-0f8122374a87

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly_afterMetadata_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_parameters_trace_space

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

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

namespace ZeroCounter

open OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

theorem pairs_add (n k : ℕ) (tail : List Bool) :
    pairs n (pairs k tail) = pairs (n + k) tail := by
  simp only [pairs, List.replicate_add, escaped_append, List.append_assoc]

theorem framed (n : ℕ) :
    true :: pairs n [false, false] = Encoding.encodeList id [List.replicate n false] := by
  simp [pairs, Encoding.encodeList, frame_eq_escaped, List.append_assoc]

theorem peek_eval (regs : Fin 3 → Bool) (scan output count modulus : List Bool) :
    Eval peek 1 (state regs scan output count modulus)
      (state (readRegs regs 0 1 scan.head?) scan output count modulus) :=
  .base (.atom _ _)

theorem bit_eval (regs : Fin 3 → Bool) (b : Bool) (scan output count modulus : List Bool) :
    Eval bit 6 (state regs (b :: scan) output count modulus)
      (state (readRegs regs 0 1 scan.head?) scan (true :: false :: output) count modulus) := by
  let a := state regs (b :: scan) output count modulus
  let c := (StructuredProgram.Atom.pop (r := 3) (s := 6) 0 0 1).eval a
  let d := pushedState 1 0 false c
  let e := pushedState 1 0 true d
  have h := (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 6) (0 : Fin 3) 1) a)).seq
    ((pushConst_eval (1 : Fin 6) (0 : Fin 3) false c).seq
      ((pushConst_eval (1 : Fin 6) (0 : Fin 3) true d).seq
        (Eval.base (StructuredProgram.Eval.atom (.peek (0 : Fin 6) (0 : Fin 3) 1) e))))
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [a, c, d, e, state,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
    · funext i; fin_cases i <;> simp [a, c, d, e, state,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]

theorem bitsLoop_eval (regs : Fin 3 → Bool) (scan output count modulus : List Bool)
    (hf : regs 1 = scan.head?.isSome) :
    ∃ rf, Eval bitsLoop (7 * scan.length + 1)
      (state regs scan output count modulus)
      (state rf [] (pairs scan.length output) count modulus) := by
  induction scan generalizing regs output with
  | nil => exact ⟨regs, .while_false (by simpa [state] using hf)⟩
  | cons b scan ih =>
    obtain ⟨rf, ht⟩ := ih (readRegs regs 0 1 scan.head?) (true :: false :: output)
      (by simp [readRegs])
    have h := Eval.while_true (by simpa [state] using hf)
      (bit_eval regs b scan output count modulus) ht
    refine ⟨rf, ?_⟩
    have hp : pairs scan.length (true :: false :: output) = pairs (scan.length + 1) output := by
      change pairs scan.length (pairs 1 output) = _
      exact pairs_add _ _ _
    rw [hp] at h
    convert h using 1 <;> first | rfl | (simp only [List.length_cons]; omega) | simp only [List.length_cons]

theorem bits_eval (regs : Fin 3 → Bool) (scan output count modulus : List Bool) :
    ∃ rf, Eval bits (7 * scan.length + 2)
      (state regs scan output count modulus)
      (state rf [] (pairs scan.length output) count modulus) := by
  obtain ⟨rf, ht⟩ := bitsLoop_eval (readRegs regs 0 1 scan.head?) scan output count modulus
    (by simp [readRegs])
  refine ⟨rf, ?_⟩
  convert (peek_eval regs scan output count modulus).seq ht using 1
  · rfl
  · omega

theorem body_eval (regs : Fin 3 → Bool) (output count modulus : List Bool) :
    ∃ rf, Eval body (14 * modulus.length + 7)
      (state regs [] output count modulus)
      (state rf [] (pairs modulus.length output) count modulus) := by
  have hc := copy_eval (3 : Fin 6) 0 5 (0 : Fin 3) 1
    (by decide) (by decide) (by decide) (by decide) (state regs [] output count modulus) rfl
  have hout : (⟨readRegs regs 0 1 none,
      StackRoutines.copyStacks 3 0 (state regs [] output count modulus).stacks⟩ : State 3 6) =
      state (readRegs regs 0 1 none) modulus output count modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state, StackRoutines.copyStacks]
  change Eval _ (7 * modulus.length + 5) _ _ at hc
  change Eval _ _ _ (⟨readRegs regs 0 1 none, _⟩ : State 3 6) at hc
  rw [hout] at hc
  obtain ⟨rf, he⟩ := bits_eval (readRegs regs 0 1 none) modulus output count modulus
  refine ⟨rf, ?_⟩
  convert hc.seq he using 1
  · rfl
  · omega

theorem loop_eval (regs : Fin 3 → Bool) (count modulus : List Bool) :
    ∃ n ≤ CounterPrograms.value count * (14 * modulus.length + 7) +
        (CounterPrograms.value count + 1) * (16 * count.length + 16),
      ∃ rf finalCount,
        Eval loop n (state regs [] [false, false] count modulus)
          (state rf [] (pairs (CounterPrograms.value count * modulus.length) [false, false])
            finalCount modulus) ∧ finalCount.length = count.length := by
  let I := fun (i : ℕ) (d : State 3 6) =>
    d.stacks 0 = [] ∧ d.stacks 1 = pairs (i * modulus.length) [false, false] ∧
      d.stacks 3 = modulus ∧ d.stacks 5 = []
  have stable : CounterForPrograms.FrameStable ports I := by
    intro i a b hab hi
    exact ⟨(hab 0 (by decide) (by decide)).symm.trans hi.1,
      (hab 1 (by decide) (by decide)).symm.trans hi.2.1,
      (hab 3 (by decide) (by decide)).symm.trans hi.2.2.1,
      (hab 5 (by decide) (by decide)).symm.trans hi.2.2.2⟩
  have spec : CounterForPrograms.BodySpec ports body I (fun _ => 14 * modulus.length + 7) := by
    intro i d hi hs _
    have hd : d = state d.regs [] (pairs (i * modulus.length) [false, false])
        (d.stacks 2) modulus := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j; fin_cases j <;> simp_all [I, ports]
    obtain ⟨rf, he⟩ := body_eval d.regs (pairs (i * modulus.length) [false, false])
      (d.stacks 2) modulus
    refine ⟨_, state rf [] (pairs modulus.length
      (pairs (i * modulus.length) [false, false])) (d.stacks 2) modulus,
      le_rfl, ?_, rfl, rfl, ?_⟩
    · rw [← hd] at he
      exact he
    · refine ⟨rfl, ?_, rfl, rfl⟩
      simp [state, pairs_add, Nat.add_mul, Nat.add_comm]
  obtain ⟨n, e, he, hi, _, hlen, hs, hn⟩ := CounterForPrograms.for_correct ports body I
    (fun _ => 14 * modulus.length + 7) stable spec
    (state regs [] [false, false] count modulus) rfl (by simp [I, state])
  have heq : e = state e.regs []
      (pairs (CounterPrograms.value count * modulus.length) [false, false]) (e.stacks 2) modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;> simp_all [state, I, ports]
  refine ⟨n, ?_, e.regs, e.stacks 2, ?_, hlen⟩
  · simpa [ports, state, CounterForPrograms.budgetSum_const] using hn
  · rw [heq] at he
    exact he

theorem command_eval (regs : Fin 3 → Bool) (count modulus : List Bool) :
    ∃ n ≤ budget count modulus, ∃ rf,
      Eval command n (state regs [] [] count modulus)
        (state rf [] (Encoding.encodeList id
          [List.replicate (CounterPrograms.value count * modulus.length) false]) [] modulus) := by
  let a := state regs [] [] count modulus
  let b := pushedState 1 0 false a
  let c := pushedState 1 0 false b
  have hc : c = state c.regs [] [false, false] count modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;> simp [a, b, state]
  obtain ⟨n, hn, rf, finalCount, he, hlen⟩ := loop_eval c.regs count modulus
  rw [← hc] at he
  let d := state rf []
    (pairs (CounterPrograms.value count * modulus.length) [false, false]) finalCount modulus
  have hp := pushConst_eval (1 : Fin 6) (0 : Fin 3) true d
  have hclear := clear_eval (2 : Fin 6) (0 : Fin 3) 1 (pushedState 1 0 true d)
  have hfinal : (⟨readRegs (pushedState 1 0 true d).regs 0 1 none,
      StackRoutines.clearStacks 2 (pushedState 1 0 true d).stacks⟩ : State 3 6) =
      state (readRegs (pushedState 1 0 true d).regs 0 1 none) []
        (Encoding.encodeList id [List.replicate
          (CounterPrograms.value count * modulus.length) false]) [] modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;> simp [d, state, StackRoutines.clearStacks, framed]
  rw [hfinal] at hclear
  refine ⟨2 + (2 + (n + (2 + (2 * finalCount.length + 3)))), ?_,
    readRegs (pushedState 1 0 true d).regs 0 1 none, ?_⟩
  · rw [hlen]
    unfold budget
    nlinarith
  · exact (pushConst_eval (1 : Fin 6) (0 : Fin 3) false a).seq
      ((pushConst_eval (1 : Fin 6) (0 : Fin 3) false b).seq (he.seq (hp.seq hclear)))

theorem program_runs (regs : Fin 3 → Bool) (count modulus : List Bool) :
    ∃ rf, RunsIn program (budget count modulus + 1)
      ((state regs [] [] count modulus).withPC (some program.entry))
      ((state rf [] (Encoding.encodeList id
        [List.replicate (CounterPrograms.value count * modulus.length) false]) [] modulus).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval regs count modulus
  exact ⟨rf, n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 2 1⟩

end ZeroCounter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

namespace Initialize

open LeafOuterProgram

private theorem register_injective : Function.Injective registers :=
  Fin.castAdd_injective 3 37

theorem clearCore_eval (a : Data) (L : ℕ)
    (hL : ∀ i ∈ corePorts, (a.stacks i).length ≤ L) (ht : a.stacks 767 = []) :
    ∃ n ≤ 18 * L + 30, Eval clearCore n a (coreCleared a) := by
  have h := BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 corePorts
    (by decide) a.regs a.stacks ht
  have sumBound (ps : List (Fin 896)) (hw : ∀ i ∈ ps, (a.stacks i).length ≤ L) :
      (ps.map (fun i => (a.stacks i).length)).sum ≤ ps.length * L := by
    induction ps with
    | nil => simp
    | cons i ps ih =>
      have hi := hw i (by simp)
      have hh := ih (fun j hj => hw j (by simp [hj]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  refine ⟨_, ?_, h⟩
  have hh := sumBound corePorts hL
  have hl : corePorts.length = 9 := rfl
  rw [hl] at hh ⊢
  omega

theorem saveShape_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval saveShape (routeCost (781,818) a) a (routed (781,818) a) :=
  route_eval (781,818) (by unfold routeValid; decide) a ht

theorem finishSetup_eval (a : Data) (L : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (ht : a.stacks 767 = []) :
    ∃ n ≤ 27 * L + 38, ∃ b,
      Eval finishSetup n a b ∧ b.stacks = finishedStacks a := by
  let c := routed (781,818) a
  have hc := saveShape_eval a ht
  have hwidth : ∀ i ∈ corePorts, (c.stacks i).length ≤ L := by
    intro i hi
    by_cases heq : i = 818
    · subst i
      simpa [c, routed] using hL 781
    · simpa [c, routed, heq] using hL i
  obtain ⟨q, hq, hclear⟩ := clearCore_eval c L hwidth (by simp [c, routed, ht])
  refine ⟨routeCost (781,818) a + q, ?_, coreCleared c, hc.seq hclear, rfl⟩
  have hsource := hL 781
  have htarget := hL 818
  change 2 * (a.stacks 818).length + 7 * (a.stacks 781).length + 8 + q ≤ 27 * L + 38
  omega

/-- No width product is materialized in binary or used as a host-language
loop: the finite constructor scans the modulus once for each binary depth
counter iteration, and charges every copied and emitted bit. -/
theorem zero_eval (a : Data) (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = []) (ht : a.stacks 767 = []) :
    ∃ n ≤ 100 * (CounterPrograms.value (a.stacks 817) + 1) *
        ((a.stacks 780).length + (a.stacks 817).length + (a.stacks 778).length + 1),
      ∃ b, Eval zeroCommand n a b ∧
        b.stacks = Function.update a.stacks 778 (zeroWord a) := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 778 a.stacks⟩
  have he1 := Subexp.TupleProgram.clear_eval (778 : Fin 896) (0 : Fin 40) 1 a
  let a2 := routed (817,0) a1
  have he2 := route_eval (817,0) (by unfold routeValid; decide) a1
    (by simp [a1, StackRoutines.clearStacks, ht])
  let d := projectState registers zeroStacks a2
  have hs : Function.Injective zeroStacks := by decide
  have hd : d = HashCandidateProgram.ZeroCounter.state d.regs [] []
      (a.stacks 817) (a.stacks 780) := by
    apply CounterForPrograms.data_ext (a := d)
      (b := HashCandidateProgram.ZeroCounter.state d.regs [] [] (a.stacks 817) (a.stacks 780)) rfl
    funext i
    fin_cases i <;> simp [d, projectState, zeroStacks, a2, routed, a1,
      StackRoutines.clearStacks, HashCandidateProgram.ZeroCounter.state, h1, h2, h3]
  obtain ⟨rf, q, hq, htrace⟩ := HashCandidateProgram.ZeroCounter.program_runs d.regs
    (a.stacks 817) (a.stacks 780)
  rw [← hd] at htrace
  let out := HashCandidateProgram.ZeroCounter.state rf [] (zeroWord a) [] (a.stacks 780)
  have he3 : Eval (.call (ProgramLinking.liftProgram HashCandidateProgram.ZeroCounter.program
      registers zeroStacks)) q a2 (embedState registers zeroStacks a2 out) :=
    eval_call_from_state _ _ _ a2 register_injective hs htrace
  refine ⟨2 * (a.stacks 778).length + 3 + (routeCost (817,0) a1 + q), ?_,
    embedState registers zeroStacks a2 out, he1.seq (he2.seq he3), ?_⟩
  · simp only [routeCost, a1, StackRoutines.clearStacks,
      Function.update_of_ne (by decide : (0 : Fin 896) ≠ 778),
      Function.update_of_ne (by decide : (817 : Fin 896) ≠ 778), h0, List.length_nil,
      Nat.mul_zero, Nat.zero_add]
    dsimp only [HashCandidateProgram.ZeroCounter.budget] at hq
    nlinarith [Nat.zero_le (CounterPrograms.value (a.stacks 817) * (a.stacks 778).length),
      Nat.zero_le (CounterPrograms.value (a.stacks 817) * (a.stacks 817).length),
      Nat.zero_le (CounterPrograms.value (a.stacks 817) * (a.stacks 780).length)]
  · have hout : out.stacks = Function.update (Function.update d.stacks 2 []) 1 (zeroWord a) := by
      funext i
      fin_cases i <;> simp [out, d, projectState, zeroStacks, a2, routed, a1,
        StackRoutines.clearStacks, HashCandidateProgram.ZeroCounter.state, h1, h2, h3]
    change Function.extend zeroStacks out.stacks a2.stacks = _
    rw [hout, ProgramLinking.extend_update hs, ProgramLinking.extend_update hs]
    have hf : Function.extend zeroStacks d.stacks a2.stacks = a2.stacks :=
      congrArg StructuredProgram.State.stacks
        (embedState_project registers zeroStacks a2 register_injective hs)
    rw [hf]
    funext i
    by_cases hi0 : i = 0
    · subst i
      simp [zeroStacks, a2, routed, a1, StackRoutines.clearStacks, h0]
    by_cases hi778 : i = 778
    · subst i
      simp [zeroStacks]
    simp [zeroStacks, a2, routed, a1, StackRoutines.clearStacks, hi0, hi778]

theorem zeroWord_length (a : Data) :
    (zeroWord a).length =
      2 * (CounterPrograms.value (a.stacks 817) * (a.stacks 780).length) + 3 := by
  simp [zeroWord, Encoding.encodeList, Encoding.length_frame]

theorem zeroWord_of_parameters (a : Data) (m depth : ℕ)
    (hdepth : CounterPrograms.value (a.stacks 817) = depth)
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m) :
    zeroWord a = Encoding.encodeList id
      [List.replicate (HashCandidates.payloadWidth m depth) false] := by
  simp only [zeroWord, hdepth, hwidth, HashCandidates.payloadWidth]

end Initialize

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual supplied-code row payloads initialize_ the streamed selector. Raw
slot bounds retain repeated indices and zero coefficients, as the physical
assembler does; they do not substitute semantic support for retained data. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

/-- Exact bytes at the serializer-to-history port; no unpaid reversal. -/
theorem initial_encoding {m B : ℕ} (shifts : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) :
    HashGreedyProgram.encodedHistory (initial shifts Q) =
      CodeRowsProgram.rowStream (HashCandidates.digitWidth m) m shifts Q := by
  unfold initial LeafScopeResourceBounds.initialPayloads CodeRowsProgram.rowStream
    HashGreedyProgram.encodedHistory
  induction CodeRowsProgram.serializedRows m shifts Q with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, List.reverse_reverse, Encoding.encodeList]
    simpa only [List.map_map, id_eq] using congrArg
      (fun tail => true :: (Encoding.frame (CodeRowsProgram.rowPayload (HashCandidates.digitWidth m) m row) ++ tail)) ih

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
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


/-- All physical services in code construction are instantiated. The exposed
intermediate state is the actual metadata-stage result and carries its proved
word cap for the later uniform numerical comparison. -/
theorem command_eval {m occurrence W : ℕ} (hm : 0 < m) (hocc : 0 < occurrence)
    (a : Data) (he : WorkerEmpty a) (ha : ∀ i, (a.stacks i).length ≤ W)
    (hmword : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hoccword : BinaryArithmetic.toNat (a.stacks 786) = occurrence)
    (hwidth : BinaryArithmetic.toNat (a.stacks 768) = 3*m) :
    ∃ (steps : ℕ) (prepared out : Data)
      (shifts : Fin (SparseCode.degree m occurrence) → Cayley.Cube (SparseCode.dimension m occurrence))
      (Q : Fin (SparseCode.localRows m occurrence) → Fin (SparseCode.degree m occurrence) → SparseCode.F3),
      let P := NativeLeafSetup.parameterTime m occurrence W (a.stacks 782).length (a.stacks 786).length
      let A := W + P
      steps ≤ P + afterTime A m occurrence (prepared.stacks 800).length
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768) ∧
      Eval command steps a out ∧
      Metadata m occurrence prepared ∧
      (∀ i, (prepared.stacks i).length ≤ A) ∧
      (prepared.stacks 800).length ≤ (a.stacks 782).length + (a.stacks 786).length + 11 ∧
      (prepared.stacks 801).length ≤ 4*(a.stacks 782).length + 2*(a.stacks 786).length + 30 ∧
      out.stacks 777 = CodeRowsProgram.rowStream (a.stacks 768).length m shifts Q ∧
      WalshExistence.Good (SparseCode.gapDenom m occurrence) shifts ∧
      SparseCode.HasDistance Q
        (SparseCode.degree m occurrence / (100 * occurrence * SparseCode.logSize m) + 1) ∧
      WorkerEmpty out ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → i.val < 800 ∨ 816 < i.val →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ afterBoundary A m occurrence
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768)) ∧
      ∀ k c, k ≤ steps → Trace (compiled command 784 788) k
        (a.withPC (some (compiled command 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (A + 1)
          (afterSpace A m occurrence (prepared.stacks 800).length
            (prepared.stacks 801) (a.stacks 782) (a.stacks 768)) := by
  obtain ⟨np, p, hnp, hep, hpempty, _, hmeta, hql, hDl, hpf, hpbound, _, hpspace⟩ :=
    NativeLeafSetup.parameters_trace_space a hm hocc he hmword hoccword ha
  have hp782 : p.stacks 782 = a.stacks 782 := hpf 782 (by decide) (Or.inl (by decide))
  have hp768 : p.stacks 768 = a.stacks 768 := hpf 768 (by decide) (Or.inl (by decide))
  have hpm : BinaryArithmetic.toNat (p.stacks 782) = m := by rw [hp782]; exact hmword
  have hpw : BinaryArithmetic.toNat (p.stacks 768) = 3*m := by rw [hp768]; exact hwidth
  obtain ⟨ns, out, shifts, Q, hns, hes, hrows, hgood, hdist, hempty, hframe, hbound, hspace⟩ :=
    afterMetadata_eval hm hocc p hpempty hmeta hpbound hpm hpw
  simp only [hp782, hp768] at hns hrows hbound hspace
  refine ⟨np + ns, p, out, shifts, Q, Nat.add_le_add hnp hns, hep.seq hes,
    hmeta, hpbound, hql, hDl, hrows, hgood, hdist, hempty, ?_, hbound, ?_⟩
  · intro i hi h777 hrange
    have h815 : i ≠ 815 := by
      intro h; have hv := congrArg Fin.val h
      change i.val = 815 at hv
      omega
    have h816 : i ≠ 816 := by
      intro h; have hv := congrArg Fin.val h
      change i.val = 816 at hv
      omega
    exact (hframe i hi h777 h815 h816).trans (hpf i hi (by omega))
  · exact StructuredSpace.sequence_stack_bound hep hes 784 788
      (fun k c hk hc i => (hpspace k c (Nat.le_succ_of_le hk) hc i).trans (Nat.le_max_left _ _))
      (fun k c hk hc i => (hspace k c hk hc i).trans (Nat.le_max_right _ _))
      (compiled command 784 788) (siteAddress command) (exitAddress command)
      (compiled_site command 784 788)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual physical preparation of the streamed greedy selector. The final
suffix clears the argmin bank, preserves the serialized code history, and
constructs the single retained zero candidate using the runtime depth word. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram
open HashGreedyProgram

theorem finished_frame (a : Data) (i : Fin 896)
    (hcore : i ∉ Initialize.corePorts) (h778 : i ≠ 778) (h779 : i ≠ 779) (h818 : i ≠ 818) :
    finishedWords a i = a.stacks i := by
  simp [finishedWords, Initialize.finishedStacks, BankRoutines.clearBankStacks,
    hcore, h778, h779, h818]

private theorem core_ge (i : Fin 896) (hi : i ∈ Initialize.corePorts) : 768 ≤ i.val := by
  simp only [Initialize.corePorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem finished_core (a : Data) (i : Fin 896) (hi : i ∈ Initialize.corePorts) :
    finishedWords a i = [] := by
  by_cases h779 : i = 779
  · subst i
    simp [finishedWords]
  have hne : i ≠ 778 := by
    intro h
    subst i
    simp [Initialize.corePorts] at hi
  simp [finishedWords, Initialize.finishedStacks, BankRoutines.clearBankStacks, hi, hne, h779]

theorem finished_low (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → finishedWords a i = [] := by
  intro i hi
  have hneq (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  rw [finished_frame a i (fun h => (Nat.not_le_of_lt hi) (core_ge i h))
    (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 818 (by decide))]
  exact NativeCodeAssembly.worker_empty a he i hi

/-- The final suffix has one actual execution, exact full-store readback,
a fixed local polynomial cost, and an all-port bound on that same trace. -/
theorem afterCode_eval (a : Data) (depth L : ℕ)
    (he : WorkerEmpty a) (ha : ∀ i, (a.stacks i).length ≤ L)
    (hd : BinaryArithmetic.toNat (a.stacks 817) = depth) :
    ∃ steps b, steps ≤ finishTime depth L ∧ Eval afterCode steps a b ∧
      b.stacks = finishedWords a ∧
      (∀ i, (b.stacks i).length ≤ max L (2 * (depth * (a.stacks 780).length) + 3)) ∧
      ∀ k c, k ≤ steps → Trace (compiled afterCode 784 788) k
        (a.withPC (some (compiled afterCode 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ L + finishTime depth L := by
  have hlo := NativeCodeAssembly.worker_empty a he
  obtain ⟨nf, hnf, f, hef, hf⟩ := Initialize.finishSetup_eval a L ha (hlo 767 (by decide))
  have hff (i : Fin 896) (hc : i ∉ Initialize.corePorts) (h818 : i ≠ 818) :
      f.stacks i = a.stacks i := by
    simp [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks, hc, h818]
  have hfl (i : Fin 896) (hi : i.val < 768) : f.stacks i = [] := by
    have hn (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    rw [hff i (fun h => (Nat.not_le_of_lt hi) (core_ge i h)) (hn 818 (by decide))]
    exact hlo i hi
  have hfb : ∀ i, (f.stacks i).length ≤ L := by
    intro i
    by_cases hc : i ∈ Initialize.corePorts
    · simp [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks, hc]
    by_cases hi : i = 818
    · subst i
      simpa [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks,
        Initialize.corePorts] using ha 781
    simpa [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks, hc, hi] using ha i
  obtain ⟨nz, hnz, b, hez, hz⟩ := Initialize.zero_eval f
    (hfl 0 (by decide)) (hfl 1 (by decide)) (hfl 2 (by decide))
    (hfl 3 (by decide)) (hfl 767 (by decide))
  have hf817 : f.stacks 817 = a.stacks 817 := hff 817 (by decide) (by decide)
  have hf780 : f.stacks 780 = a.stacks 780 := hff 780 (by decide) (by decide)
  have hfd : CounterPrograms.value (f.stacks 817) = depth := by
    rw [CounterPrograms.value_eq_toNat, hf817, hd]
  have hzero : Initialize.zeroWord f = Initialize.zeroWord a := by
    simp only [Initialize.zeroWord, hf817, hf780]
  have hnz' : nz ≤ 100 * (depth + 1) * (3 * L + 1) := by
    rw [hfd] at hnz
    apply hnz.trans
    apply Nat.mul_le_mul_left
    have := hfb 780
    have := hfb 817
    have := hfb 778
    omega
  have hz779 : b.stacks 779 = a.stacks 779 := by
    rw [hz, Function.update_of_ne (by decide), hff 779 (by decide) (by decide)]
  let out : Data := ⟨readRegs b.regs 0 1 none, StackRoutines.clearStacks 779 b.stacks⟩
  have heclear := Subexp.TupleProgram.clear_eval (779 : Fin 896) (0 : Fin 40) 1 b
  have hsteps : nf + (nz + (2 * (b.stacks 779).length + 3)) ≤ finishTime depth L := by
    have h779 := ha 779
    rw [hz779]
    dsimp only [finishTime]
    omega
  have heval : Eval afterCode (nf + (nz + (2 * (b.stacks 779).length + 3))) a out :=
    hef.seq (hez.seq heclear)
  have hwords : out.stacks = finishedWords a := by
    dsimp only [out, StackRoutines.clearStacks]
    rw [hz, hzero, hf]
    rfl
  refine ⟨_, out, hsteps, heval, hwords, ?_, ?_⟩
  · intro i
    by_cases hi779 : i = 779
    · subst i
      simp [out, StackRoutines.clearStacks]
    change ((StackRoutines.clearStacks 779 b.stacks) i).length ≤ _
    rw [StackRoutines.clearStacks, Function.update_of_ne hi779]
    by_cases hi : i = 778
    · subst i
      rw [hz, Function.update_self, Initialize.zeroWord_length, hfd, hf780]
      exact Nat.le_max_right _ _
    rw [hz, Function.update_of_ne hi]
    exact (hfb i).trans (Nat.le_max_left _ _)
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := ha i
    omega

/-- The concrete final preparation changes no formula, count, or saved
parameter word; it preserves the history produced by the actual serializer. -/
theorem finished_parameters (a : Data) :
    finishedWords a 777 = a.stacks 777 ∧
    finishedWords a 780 = a.stacks 780 ∧
    finishedWords a 781 = a.stacks 781 ∧
    finishedWords a 782 = a.stacks 782 ∧
    finishedWords a 783 = a.stacks 783 ∧
    finishedWords a 784 = a.stacks 784 ∧
    finishedWords a 785 = a.stacks 785 ∧
    finishedWords a 786 = a.stacks 786 ∧
    finishedWords a 788 = a.stacks 788 ∧
    finishedWords a 817 = a.stacks 817 ∧
    finishedWords a 818 = a.stacks 781 ∧
    finishedWords a 778 = Initialize.zeroWord a ∧ finishedWords a 779 = [] := by
  simp [finishedWords, Initialize.finishedStacks, BankRoutines.clearBankStacks,
    Initialize.corePorts]

/-- This exact store implication is used with the actual suffix execution,
so no readiness field is left as an implementation assumption. -/
theorem finished_ready (a b : Data) {n m B : ℕ} (initial : List (List Bool))
    (he : WorkerEmpty a) (hb : b.stacks = finishedWords a)
    (hh : a.stacks 777 = encodedHistory initial)
    (hm : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hl : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hr : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true)
    (hc : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hw : a.stacks 783 = a.stacks 780)
    (hd : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B) :
    Ready n m B initial b := by
  have hp := finished_parameters a
  rcases hp with ⟨h777,h780,h781,h782,h783,_h784,_h785,_h786,_h788,h817,h818,h778,h779⟩
  constructor
  · intro i
    rw [hb]
    exact finished_low a he (workerStack i) (by simp [workerStack])
  · intro i hi
    rw [hb]
    exact finished_core a i hi
  · exact (congrFun hb 777).trans (h777.trans hh)
  · rw [hb, h778]
    exact Initialize.zeroWord_of_parameters a m (SparseCode.distanceDenom m B)
      (by rw [CounterPrograms.value_eq_toNat]; exact hd) hl
  · exact (congrFun hb 779).trans h779
  · simpa only [hb, h780] using hm
  · simpa only [hb, h780] using hl
  · exact (congrFun hb 781).trans (h781.trans hr)
  · simpa only [hb, h782] using hc
  · simpa only [hb, h783, h780] using hw
  · simpa only [hb, h817] using hd
  · exact (congrFun hb 818).trans (h818.trans hr)

/-- Code construction and initialization expose their actual intermediate
metadata state for the fixed numerical envelopes, never an assumed layout. -/
theorem afterCanonical_eval_oai (a : Data) {n m B L : ℕ}
    (hm : 0 < m) (hB : 0 < B) (he : WorkerEmpty a)
    (ha : ∀ i, (a.stacks i).length ≤ L)
    (hc : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B)
    (hwidth : a.stacks 768 = a.stacks 780)
    (hmod : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmodlen : (a.stacks 780).length = HashCandidates.digitWidth m)
    (h783 : a.stacks 783 = a.stacks 780)
    (hdepth : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B)
    (hrounds : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true) :
    ∃ (steps : ℕ) (prepared out : Data)
      (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
      let A := L + P
      let R := NativeCodeAssembly.afterBoundary A m B
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
      steps ≤ P + NativeCodeAssembly.afterTime A m B (prepared.stacks 800).length
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768) +
          finishTime (SparseCode.distanceDenom m B) R ∧
      Eval afterCanonical steps a out ∧
      Metadata m B prepared ∧ (∀ i, (prepared.stacks i).length ≤ A) ∧
      Ready n m B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom m B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ max R
        (2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3)) ∧
      ∀ k c, k ≤ steps → Trace (compiled afterCanonical 784 788) k
        (a.withPC (some (compiled afterCanonical 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (max (A + 1) (NativeCodeAssembly.afterSpace A m B
            (prepared.stacks 800).length (prepared.stacks 801) (a.stacks 782) (a.stacks 768)))
            (R + finishTime (SparseCode.distanceDenom m B) R) := by
  have hv : BinaryArithmetic.toNat (a.stacks 768) = 3 * m := hwidth ▸ hmod
  obtain ⟨nc,p,c,shifts,Q,hnc,hec,hmeta,hp,_hq,_hD,hrows,hgood,hdist,hce,hcf,hcb,hcs⟩ :=
    NativeCodeAssembly.command_eval hm hB a he ha hc hBword hv
  have frame (i : Fin 896) (hi : 768 ≤ i.val) (h777 : i ≠ 777)
      (hr : i.val < 800 ∨ 816 < i.val) : c.stacks i = a.stacks i := hcf i hi h777 hr
  have cd : BinaryArithmetic.toNat (c.stacks 817) = SparseCode.distanceDenom m B := by
    rw [frame 817 (by decide) (by decide) (Or.inr (by decide))]
    exact hdepth
  obtain ⟨nf,out,hnf,hef,hwords,hout,hfs⟩ := afterCode_eval c _ _ hce hcb cd
  have history : c.stacks 777 = encodedHistory (HashGreedyCode.initial shifts Q) := by
    rw [hrows, hwidth, hmodlen]
    exact (HashGreedyCode.initial_encoding shifts Q).symm
  have hready := finished_ready c out (HashGreedyCode.initial shifts Q) hce hwords history
    (by rw [frame 780 (by decide) (by decide) (Or.inl (by decide))]; exact hmod)
    (by rw [frame 780 (by decide) (by decide) (Or.inl (by decide))]; exact hmodlen)
    (by rw [frame 781 (by decide) (by decide) (Or.inl (by decide))]; exact hrounds)
    (by rw [frame 782 (by decide) (by decide) (Or.inl (by decide))]; exact hc)
    (by rw [frame 783 (by decide) (by decide) (Or.inl (by decide)),
      frame 780 (by decide) (by decide) (Or.inl (by decide))]; exact h783) cd
  refine ⟨nc+nf,p,out,shifts,Q,Nat.add_le_add hnc hnf,hec.seq hef,hmeta,hp,
    hready,hgood,hdist,?_,?_,?_⟩
  · intro i hi hr
    have hn (j : Fin 896) (hj : j.val < 784) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    have hi818 : i ≠ 818 := by
      intro h
      subst i
      change 818 < 800 ∨ 818 < 818 at hr
      omega
    rw [hwords, finished_frame c i (by
      intro hm
      simp only [Initialize.corePorts, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      (hn 778 (by decide)) (hn 779 (by decide)) hi818]
    exact frame i (by omega) (hn 777 (by decide)) (by omega)
  · simpa only [frame 780 (by decide) (by decide) (Or.inl (by decide)), hmodlen] using hout
  · exact StructuredSpace.sequence_stack_bound hec hef 784 788
      (fun k c hk ht i => (hcs k c hk ht i).trans (Nat.le_max_left _ _))
      (fun k c hk ht i => (hfs k c hk ht i).trans (Nat.le_max_right _ _))
      (compiled afterCanonical 784 788) (siteAddress afterCanonical) (exitAddress afterCanonical)
      (compiled_site afterCanonical 784 788)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval_oai
