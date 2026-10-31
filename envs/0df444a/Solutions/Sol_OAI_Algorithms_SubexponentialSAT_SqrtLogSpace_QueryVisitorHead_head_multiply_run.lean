-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:47:49.353982+00:00
-- url     : https://prove2.me/submissions/455eae8e-58b0-4d46-9154-11777775fb21

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect_accepted_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedProgram_register_frame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedSpace_head_resources_of_local_time
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram_StagedGate_bodyBudget_uniform
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumCorrect_gate_source_iff
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumCorrect_prepared_head_update
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumNative_Accumulator_advance
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumNative_Accumulator_initial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumNative_actual_product_value
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_body_cursor_next
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_body_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_finalize_prefix
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryAdapter_NativeOverlay_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram_multiply_run

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

/-- Every off-counter caller stack is preserved, including cleared scratch. -/
theorem incrementResult_stacks {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    (incrementResult p d).stacks =
      Function.update d.stacks p.counter (ripple true (d.stacks p.counter)) := by
  funext i
  by_cases hc : i = p.counter
  · subst i
    simp
  · by_cases hi : i = p.scratch
    · subst i
      simp [hc, hs]
    · rw [Function.update_of_ne hc]
      exact install_other_stack p d _ _ _ _ _ i hc hi

theorem powerTwo_value (width : ℕ) :
    value (List.replicate width false ++ [true]) = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ, ih, pow_succ, Nat.mul_comm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem basePort_protected (i : Fin 768) :
    basePort i ≠ 640 ∧ basePort i ≠ 641 ∧ basePort i ≠ 642 ∧ basePort i ≠ 647 ∧
      basePort i ≠ 650 ∧ basePort i ≠ 651 ∧ basePort i ≠ 670 ∧ basePort i ≠ 671 := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

theorem basePort_outside (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    ¬ ∃ j, basePort j = i := by
  rintro ⟨j, hj⟩
  rcases hi with hi | hi
  · simp only [protectedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hp := basePort_protected j
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.1 hj
    · exact hp.2.1 hj
    · exact hp.2.2.1 hj
    · exact hp.2.2.2.1 hj
    · exact hp.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.2 hj
  · have hm := basePort_high j
    rw [hj] at hm
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


theorem selected_true_length (mask xs : List Bool) (hlen : mask.length = xs.length) :
    (selected true mask xs).length = Subexp.PaddedCompletion.trueCount mask := by
  induction mask generalizing xs with
  | nil => simp [selected, Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful]
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have ht : mask.length = xs.length := by simpa using hlen
          cases b <;> simp [selected, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful] at * <;> exact ih xs ht

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask traverses original coordinates in descending order.
This explicit order, rather than an arbitrary finite-type equivalence,
identifies each odometer position with its actual original variable. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

theorem selected_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    Restriction.selected true (xs.map p) (xs.map x) = (xs.filter p).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [Restriction.selected, hp, ih]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem result_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  by_cases hn : ∃ j, stackMap j=i
  · obtain ⟨j,rfl⟩ := hn
    rw [show (result a rf).stacks (stackMap j)=
      (Overlay.state rf (a.stacks 859) (a.stacks 670)
        (a.stacks 869) (a.stacks 870) (a.stacks 871) [] [] [] [] []
        (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge (a.stacks 670) (a.stacks 859))
          (a.stacks 670) (a.stacks 869)) []).stacks j from
      embedState_stack regMap stackMap a _ (by decide) j]
    fin_cases j <;> simp_all [stackMap,changed,Overlay.state]
  · exact embedState_stack_frame regMap stackMap a _ i hn

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (875 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (875 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (StackRoutines.clearStacks 875 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (StackRoutines.clearStacks 875 a.stacks) =
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i ∈ changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i ≠ 875 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=7 from rfl,
    hs,StackRoutines.readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi



@[simp] theorem prepared_assignment (a : Data) (rf : Fin 8 → Bool) :
    (result (resetState a) rf).stacks 145=LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (a.stacks 670) (a.stacks 859)) (a.stacks 670) (a.stacks 869) := by
  rw [result_assignment,reset_frame a 670 (by decide),reset_frame a 859 (by decide),
    reset_frame a 869 (by decide)]

theorem prepared_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result (resetState a) rf).stacks i=a.stacks i :=
  (result_frame (resetState a) rf i hi).trans (reset_frame a i hi)

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

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

namespace DenseWord

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {port : Fin 896}
    {value : Dense (q.p.model.O q.p.t) q.p.t q.J} {a b : Data}
    (h : DenseWord q port value a) (hf : b.stacks port=a.stacks port) :
    DenseWord q port value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end DenseWord

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The real initializer and paid cache setup establish the physical boundary
for the actual stored-ID fold. Bounds are fixed before that fold; the current
Good-empty-support seed is serialized on151, the unread suffix on150 and the
reversed original ID on149. No execution service is a field below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem table_entry_written (i : Fin 896) (hi : i ∈ FactorTableProgram.entryPorts) :
    i ∈ FactorTableSpace.writtenPorts := by
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j,(List.mem_filter.mp hj).1,rfl⟩)
  · exact List.mem_append_right _ hi

/-- Numeric support of the actual relocated source writes. -/
theorem written_bounds (i : Fin 896) (hi : i ∈ FactorTableSpace.writtenPorts) :
    i.val = 62 ∨ (340 ≤ i.val ∧ i.val ≤ 684) ∨
      i.val = 881 ∨ i.val = 882 ∨ (885 ≤ i.val ∧ i.val ≤ 892) := by
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hjb := Incidence.mem_workerPorts j |>.mp hj
    unfold FactorTableProgram.basePort
    split_ifs
    all_goals simp only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd]
    all_goals omega
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.coe_ofNat_eq_mod]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem headOrder_ids (p : ℕ → Bool) (n : ℕ) :
    HeadScatterProgram.headIds (headOrder p n)=chosenIds p n := by
  simp [HeadScatterProgram.headIds, headOrder, count]

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadRepresentativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HeadIdentifierProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- The actual chosen-ID word fixes the ascending selection order. -/
theorem headOrder_stream (p : ℕ → Bool) (n : ℕ) :
    (List.finRange n).filter (fun v => p v.val)=List.ofFn (headOrder p n) := by
  apply (List.map_injective_iff.mpr (Fin.val_injective : Function.Injective (Fin.val (n:=n))))
  rw [List.map_ofFn]
  change _=HeadScatterProgram.headIds (headOrder p n)
  rw [headOrder_ids]
  simpa only [List.map_coe_finRange,chosenIds,Function.comp_def] using
    (List.filter_map (f:=(Fin.val : Fin n → ℕ)) (p:=p) (l:=List.finRange n)).symm

/-- The native selected-bit scan emits exactly the current head's ambient
coordinates in the already emitted headOrder, including the empty head. -/
theorem selected_headOrder (p : ℕ → Bool) (n : ℕ) (x : Fin n → Bool) :
    Restriction.selected true (List.ofFn (fun v : Fin n => p v.val)) (List.ofFn x) =
      List.ofFn (fun i => x (headOrder p n i)) := by
  rw [List.ofFn_eq_map,List.ofFn_eq_map,Order.selected_map,headOrder_stream,List.map_ofFn]
  rfl

/-- The physical selected-mask population is the actual emitted head width. -/
theorem headOrder_highCount (p : ℕ → Bool) (n : ℕ) :
    Restriction.highCount (List.ofFn (fun v : Fin n => p v.val))=count p n := by
  have hh := Restriction.selected_true_length (List.ofFn (fun v : Fin n => p v.val))
    (List.ofFn (fun _ : Fin n => true)) (by simp)
  rw [selected_headOrder,List.length_ofFn] at hh
  exact hh.symm

/-- The concrete local correction word is the support indicator at the
same ascending head positions used by the cursor and full matrix columns. -/
theorem selected_supportBits (p : ℕ → Bool) (n : ℕ) (E : Finset (Fin n)) :
    Restriction.selected true (List.ofFn (fun v : Fin n => p v.val))
        (LeafWeightProgram.supportBits ⟨E⟩) =
      LeafWeightProgram.supportBits
        ⟨Finset.univ.filter (fun i => headOrder p n i∈E)⟩ := by
  rw [LeafWeightProgram.supportBits,selected_headOrder]
  simp [LeafWeightProgram.supportBits]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadRepresentativeSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

theorem Cursor.word {h i : ℕ} {d : Data} (hc : Cursor h i d)
    (hp : 0 < value (d.stacks 860)) :
    d.stacks 859 = (Counters.wordEquiv h ⟨i, hc.index_lt hp⟩).val := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · exact (hc.activeWidth (hc.index_lt hp)).trans (Counters.wordEquiv h _).property.symm
  · change value (d.stacks 859) = value (ExecCNFTupleEnumeration.fixedBits h i)
    rw [ExecCNFTupleEnumeration.fixedBits_value h i (hc.index_lt hp)]
    exact hc.rank

theorem Cursor.initial (h : ℕ) (d : Data)
    (hw : d.stacks 859 = List.replicate h false)
    (hf : d.stacks 860 = List.replicate h false ++ [true]) (hs : d.stacks 861 = []) :
    Cursor h 0 d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hs⟩
  · simp [hw]
  · simpa [hf] using Counters.powerTwo_value h
  · simp [hf]
  · simp [hw]
  · intro _; simp [hw]

theorem powerResult_frame (d : Data) (j : Fin 896) (h0 : j ≠ 860) (h1 : j ≠ 861) :
    (powerResult d).stacks j = d.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  fin_cases i <;> simp_all [powerStacks]

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )

theorem seeded_stacks (d : Data) (h : ℕ)
    (hshape : d.stacks 651 = List.replicate h false)
    (hcursor : d.stacks 859 = []) (hscratch : d.stacks 861 = []) :
    (seeded d).stacks = Function.update (Function.update (Function.update d.stacks
      859 (List.replicate h false)) 860 (List.replicate h false ++ [true])) 853 [] := by
  funext j
  by_cases h853 : j = 853
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks]
  by_cases h860 : j = 860
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks, copyState,
      StackRoutines.copyStacks, hshape, hscratch]
  by_cases h861 : j = 861
  · subst j; simp [seeded, clearState, StackRoutines.clearStacks, hscratch]
  simp [seeded, clearState, StackRoutines.clearStacks, h853, h860,
    powerResult_frame _ j h860 h861, copyState, StackRoutines.copyStacks, h861,
    hshape, hcursor]


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

/-- Numeric bit-counter order covers every head assignment exactly once. -/
theorem range_sum_eq_assignments {R : Type*} [AddCommMonoid R]
    (h : ℕ) (f : (Fin h → Bool) → R) :
    (∑ i ∈ Finset.range (2 ^ h), if hi : i < 2 ^ h then
      f (AttainedSignatures.assignmentEquiv h ⟨i, hi⟩) else 0) =
      ∑ a : Fin h → Bool, f a := by
  rw [Finset.sum_range]
  have hh := (AttainedSignatures.assignmentEquiv h).sum_comp f
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]


/-- The actual numeric cursor denotes the assignment used by the full-key gate. -/
theorem Cursor.assignment_word {h i : ℕ} {a : Data} (hc : Cursor h i a)
    (hp : 0 < value (a.stacks 860)) :
    a.stacks 859 = List.ofFn (AttainedSignatures.assignmentEquiv h ⟨i, hc.index_lt hp⟩) := by
  rw [AttainedSignatures.assignment_word]
  exact hc.word hp

theorem finalize_eval (a : Data) :
    Eval finalize (2 * (a.stacks 859).length + 2 * (a.stacks 860).length + 7)
      a (finalized a) := by
  have he := eval_liftCommand_from_state (SubexpSetupStorage.clearMany [859, 860]) 859 853
    FactorEnvironment.registerMap id a (Fin.castAdd_injective _ _) Function.injective_id
    (SubexpSetupStorage.clearMany_eval [859, 860]
      (projectState FactorEnvironment.registerMap id a))
  convert he using 1
  · rfl
  · simp [SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, projectState]
    omega
  · rfl

theorem finalized_stacks (a : Data) :
    (finalized a).stacks = Function.update (Function.update a.stacks 859 []) 860 [] := by
  funext i
  rw [show (finalized a).stacks i =
      (SubexpSetupStorage.clearManyState [859, 860]
        (projectState FactorEnvironment.registerMap id a)).stacks i from
    embedState_stack FactorEnvironment.registerMap id a _ Function.injective_id i]
  simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState, projectState]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
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

theorem cleared_controller (a : Data) (i : Fin 896) (hi : i ∈ controllerPorts) :
    (cleared a).stacks i = [] :=
  BankRoutines.clearBankStacks_mem _ _ _ ((mem_workPorts _).mpr (Or.inr hi))

theorem cleared_frame (a : Data) (i : Fin 896) (hi : 56 ≤ i.val)
    (hc : i ∉ controllerPorts) :
    (cleared a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame _ _ _ (by
    rw [mem_workPorts]
    exact not_or.mpr ⟨by omega, hc⟩)

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed accepted branch physically overlays the current assignment,
computes its whole specialized factor product, and adds that same dictionary
to the head sum. Its compact return cap is independent of its transient cost. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState
open HighQueryAdapter TruncatedRingProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem frame_not_entry (i : Fin 896) (hi : i ∈ framePorts) :
    i ∉ entryScratch := by
  have small : ∀ i ∈ framePorts,
      i ∉ ([149,150,151,159,854] ++ callbackScratch.map lowStack : List (Fin 896)) :=
    List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  have outside : ∀ i ∈ framePorts,
      i ∈ FactorTableProgram.protectedPorts ∨
      (i.val ≠ 62 ∧ (i.val < 340 ∨ 684 < i.val) ∧ i.val ≠ 881 ∧ i.val ≠ 882 ∧
        (i.val < 885 ∨ 892 < i.val)) := List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  have tail : ∀ i ∈ framePorts,
      i ∉ ([62,680,681,682,683,684,881,882] : List (Fin 896)) :=
    List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · exact small i hi hm
  · rcases outside i hi with hp | ho
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
        exact FactorTableProgram.basePort_outside i (Or.inl hp) ⟨j,hj⟩
      · exact tail i hi hm
    · have hw := written_bounds i (table_entry_written i hm)
      omega

theorem frame_exclusions (i : Fin 896) (hi : i ∈ framePorts) :
    i ∉ NativeOverlay.changed ∧ i ∉ entryScratch ∧
    i ∉ cachePorts.map lowStack ∧ i ∉ FactorEnvironment.environmentPorts ∧
    i ≠ 853 ∧ i ≠ 854 := by
  have small : ∀ i ∈ framePorts,
      i ∉ NativeOverlay.changed ∧ i ∉ cachePorts.map lowStack ∧
      i ∉ FactorEnvironment.environmentPorts ∧ i ≠ 853 ∧ i ≠ 854 :=
    List.forall_iff_forall_mem.mp (by
      simp only [framePorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  obtain ⟨ho,hc,he,hs,hp⟩ := small i hi
  exact ⟨ho,frame_not_entry i hi,hc,he,hs,hp⟩

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Semantic correctness of the concrete head accumulator. Native dictionary
witnesses are retained only for the current partial sum, and their meaning is
proved using the actual finite-ring normalization program. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open scoped BigOperators

/-- The first semantic loop state is produced by the paid cleanup and seed.
The head accumulator is the actual empty dictionary, and only the named
counter words are installed in addition to the reclaimed workspace. -/
theorem initial_stacks (a : Data) (h : ℕ)
    (hshape : a.stacks 651 = List.replicate h false) :
    (CounterForPrograms.testResult fuelPorts (seeded (HeadSumAssembly.cleared a))).stacks =
      Function.update (Function.update (Function.update (HeadSumAssembly.cleared a).stacks
        859 (List.replicate h false)) 860 (List.replicate h false ++ [true])) 853 [] := by
  have hshape' : (HeadSumAssembly.cleared a).stacks 651 = List.replicate h false := by
    rw [HeadSumAssembly.cleared_frame a 651 (by decide) (by decide)]
    exact hshape
  have hc := HeadSumAssembly.cleared_controller a 859 (by decide)
  have hs := HeadSumAssembly.cleared_controller a 861 (by decide)
  have he := seeded_stacks (HeadSumAssembly.cleared a) h hshape' hc hs
  have hz : (seeded (HeadSumAssembly.cleared a)).stacks 861 = [] := by simp [he, hs]
  rw [CounterForPrograms.testResult_stacks fuelPorts _ hz, he]


open HeadIdentifierProgram

/-- Reindex the semantic head sum along the already proved source order.
Only the finite mathematical sum is transported; the machine still uses its
single bounded-width bit counter. -/
theorem counter_sum_eq_head {R : Type*} [AddCommMonoid R] {n r : ℕ}
    (H : Finset (Fin n)) (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r)
    (p : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds p n ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)
    (f : (Moments.Head head g → Bool) → R) :
    (∑ i ∈ Finset.range (2 ^ count p n), if hi : i < 2 ^ count p n then
      f ((BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
        (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm
          (AttainedSignatures.assignmentEquiv (count p n) ⟨i, hi⟩)) else 0) =
      ∑ a : Moments.Head head g → Bool, f a := by
  rw [range_sum_eq_assignments (count p n) (fun bits =>
    f ((BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
      (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm bits))]
  exact (BucketTupleProgram.Concrete.freeAssignmentEquiv H head g (chosenIds p n)
    (chosenIds_bound p n) (chosenIds_nodup p n) hs).symm.sum_comp f

open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical frames for the native head rescan. Read-and-restore source words
are framed at command endpoints. The pair accumulator has the stronger static
property that no controller, overlay or dense-add instruction writes it. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames

open OAI BitProgram StructuredCalls HeadSumProgram
open HeadEvaluationProgram.StagedGate (copy clear)

/-- The concrete overlay restores all source masks, baseline and query words
outside its precisely named assignment/output scratch. -/
theorem overlay_frame {steps : ℕ} {a b : Data}
    (hh : (a.stacks 859).length =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (he : Eval HighQueryAdapter.NativeOverlay.prepare steps a b)
    (i : Fin 896) (hi : i ∉ HighQueryAdapter.NativeOverlay.changed) :
    b.stacks i = a.stacks i := by
  open HighQueryAdapter.NativeOverlay in
    obtain ⟨rf, hc⟩ := command_eval (resetState a)
      (fun j hj => BankRoutines.clearBankStacks_mem j changed a.stacks hj)
      (by simpa only [reset_frame a 859 (by decide), reset_frame a 670 (by decide)] using hh)
      (by simpa only [reset_frame a 670 (by decide), reset_frame a 869 (by decide)] using hm)
    have hb := Eval.final_unique (853 : Fin 896) he ((reset_eval a).seq hc)
    subst b
    exact prepared_frame a rf i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed head rescan. The invariant retains the current
normalized dictionary and the actual immutable source words. Its compact
boundary is reused after every candidate; no execution service is assumed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open HeadIdentifierProgram BucketTupleProgram.Concrete
open QueryTupleState (masterPorts QueryMasterFrame QueryReady)
open scoped BigOperators

noncomputable section

private theorem retained_exclusions (j : Fin 896) (hj : j ∈ retainedPorts) :
    56 ≤ j.val ∧ j ∉ HeadSumAssembly.controllerPorts ∧ j ≠ 853 ∧
      j ≠ 859 ∧ j ≠ 860 ∧ j ≠ 861 := by
  have h : ∀ j ∈ retainedPorts, 56 ≤ j.val ∧ j ∉ HeadSumAssembly.controllerPorts ∧
      j ≠ 853 ∧ j ≠ 859 ∧ j ≠ 860 ∧ j ≠ 861 :=
    List.forall_iff_forall_mem.mp (by
      simp only [retainedPorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  exact h j hj

private theorem retained_accepted (j : Fin 896) (hj : j ∈ retainedPorts) :
    j ∈ HeadAcceptedCorrect.framePorts := by
  have h : ∀ j ∈ retainedPorts, j ∈ HeadAcceptedCorrect.framePorts :=
    List.forall_iff_forall_mem.mp (by
      simp only [retainedPorts,masterPorts,List.forall_append,List.forall_cons]
      repeat' apply And.intro
      all_goals decide)
  exact h j hj

namespace Accumulator
variable {r Q n d : ℕ} {q : Factor.Spec r Q n d}
  {origin : HeadSumProgram.Data} {contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J}
  {P i : ℕ} {a b : HeadSumProgram.Data}

theorem query {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool}
    {E U : Finset (Fin n)} {M : ℕ}
    (ha : Accumulator q origin contribution P i a)
    (hq : QueryReady q node H high E U M origin) :
    QueryReady q node H high E U M a :=
  hq.frame ⟨fun j hj => ha.retained j (List.mem_append_left _ hj)⟩

theorem register_change (ha : Accumulator q origin contribution P i a)
    (regs : Fin 40 → Bool) : Accumulator q origin contribution P i ⟨regs,a.stacks⟩ :=
  ⟨ha.compact,ha.retained,ha.low,ha.scratch0,ha.scratch1,ha.partialSum⟩

end Accumulator

/-- The fixed head program produces the exact restricted signature-fiber sum.
Both resource bounds refer to this same run; every retained stack is counted. -/
theorem run {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
          ((chosenIds pick n).get i))
    (ids : List ℕ) (a : HeadSumProgram.Data)
    (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length ≤ P)
    (hshape : a.stacks 651 = List.replicate (count pick n) false)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
    (hW : a.stacks 864 = W)
    (hmatrix : a.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hcount : count pick n+1 ≤ P) (hrows : q.ps.length ≤ P)
    (hcoeff : ∀ j i, (c j i).length ≤ P)
    (hcache : 4*M+6 ≤ P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
    (hradius : q.p.R+1 ≤ Q) (width : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hdegree : d * baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z)
    (B : ℕ)
    (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
      HeadAcceptedCorrect.budget q P S Z ≤ B)
    (hcounter : 9*(count pick n+1)+8 ≤ B) :
    ∃ steps b, ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
      Trace HeadAcceptedProgram.program steps
        (a.withPC (some HeadAcceptedProgram.program.entry)) (b.withPC none) ∧
      Eval (HeadSumAssembly.head HeadSumAssembly.accepted) (steps-1) a b ∧
      Good ∅ q.u q.J entries ∧ b.stacks 853 = Product.bytes entries ∧
      rawValue q.u q.J q.p.ops.decode entries =
        (∑ x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool,
          if HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g x =
              HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g (reps g) ∧
              (∀ v, v.val.val ∈ E → x v = true) then
            QueryEvaluation.specializeDense q.u q.J
              (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
              (HeadSourceLocality.sourceProduct q H high
                (HeadSourceLocality.stateFor H high
                  (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
                    (Function.update reps g x))) ids) else 0) ∧
      (∀ j ∈ retainedPorts, b.stacks j = a.stacks j) ∧
      (∀ j, (b.stacks j).length ≤ P) ∧
      b.stacks 859 = [] ∧ b.stacks 860 = [] ∧ b.stacks 861 = [] ∧
      steps ≤ (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial P +
        HeadAcceptedCorrect.budget q P S Z)+126*B+54*count pick n+286)*2^(count pick n) ∧
      ∀ elapsed z, elapsed ≤ steps → Trace HeadAcceptedProgram.program elapsed
        (a.withPC (some HeadAcceptedProgram.program.entry)) z →
        ∀ j, (z.stacks j).length ≤ B := by
  classical
  let h := count pick n
  let rows := List.ofFn (fun j => List.ofFn (c j))
  let order := freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
    (chosenIds_bound pick n) (chosenIds_nodup pick n) hs
  let candidate (i : Fin (2^h)) := order.symm (AttainedSignatures.assignmentEquiv h i)
  let value (x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :=
    QueryEvaluation.specializeDense q.u q.J
      (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
      (HeadSourceLocality.sourceProduct q H high (HeadSourceLocality.stateFor H high
        (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
          (Function.update reps g x))) ids)
  let selected (x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :=
    HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g x =
      HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g (reps g) ∧
      ∀ v, v.val.val ∈ E → x v = true
  let contribution (i : ℕ) := if hi : i < 2^h then
    if selected (candidate ⟨i,hi⟩) then value (candidate ⟨i,hi⟩) else 0 else 0
  let I := fun i b => Cursor h i b ∧ Accumulator q a contribution P i b
  let C := HeadEvaluationProgram.StagedGate.bodyPolynomial P + HeadAcceptedCorrect.budget q P S Z
  have hi : I 0 (CounterForPrograms.testResult fuelPorts (seeded (HeadSumAssembly.cleared a))) := by
    refine ⟨?_,Accumulator.initial q a contribution h P hshape ha hcount⟩
    have hst := HeadSumCorrect.initial_stacks a h hshape
    apply Cursor.initial
    · simp [hst]
    · simp [hst]
    · simp only [hst,Function.update_of_ne (by decide : (861 : Fin 896) ≠ 853),
        Function.update_of_ne (by decide : (861 : Fin 896) ≠ 860),
        Function.update_of_ne (by decide : (861 : Fin 896) ≠ 859)]
      exact HeadSumAssembly.cleared_controller a 861 (by decide)
  have spec : ∀ i state, I i state → state.stacks 861 = [] →
      0 < CounterPrograms.value (state.stacks 860) →
      ∃ nb e, nb ≤ C ∧ Eval (body HeadSumAssembly.accepted) nb state e ∧
        e.stacks 860 = state.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i+1) (CounterForPrograms.nextState fuelPorts e) := by
    intro i state hi hscratch hfuel
    obtain ⟨hcur,hacc⟩ := hi
    have hrank := hcur.index_lt hfuel
    let x := candidate ⟨i,hrank⟩
    have hbits : state.stacks 859 = List.ofFn (order x) := by
      have horder : order x = AttainedSignatures.assignmentEquiv h ⟨i, hrank⟩ := by
        dsimp only [x, candidate]
        exact Equiv.apply_symm_apply order _
      rw [horder]
      exact hcur.assignment_word hfuel
    have hfixed (j : Fin 896) (hj : j ∈ retainedPorts) := hacc.retained j hj
    have hmat : state.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
        (rows.map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words) := (hfixed 865 (by decide)).trans hmatrix
    have hlen : ∀ row ∈ rows, row.length = (state.stacks 859).length := by
      intro row hrow
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
      simp [hcur.activeWidth hrank,h]
    have hEl : (state.stacks 859).length = (state.stacks 867).length := by
      rw [hfixed 867 (by decide),hE,HeadRepresentativeSemantics.selected_supportBits]
      simp [LeafWeightProgram.supportBits,hcur.activeWidth hrank,h]
    have hHl : (state.stacks 859).length = (state.stacks 868).length := by
      rw [hfixed 868 (by decide),hH,List.length_replicate,hcur.activeWidth hrank]
    have hgate : gateValue state rows = true ↔ selected x :=
      HeadSumCorrect.gate_source_iff q.p q.ps q.packing owner head H E node g pick hs W c hc
        x (reps g) state ((hfixed 864 (by decide)).trans hW) hbits
        ((hfixed 866 (by decide)).trans hkey) ((hfixed 867 (by decide)).trans hE)
        ((hfixed 868 (by decide)).trans hH)
    obtain ⟨nb,b,hnb,he,h859,h860,h861,hnext⟩ := body_eval HeadSumAssembly.accepted
      state rows (HeadAcceptedCorrect.budget q P S Z)
      (Accumulator q a contribution P (i+1))
      (fun j => hacc.low (j.castAdd 24)) hmat hlen hEl hHl hscratch
      (by
        intro hg out hout
        let start : HeadSumProgram.Data := ⟨out,state.stacks⟩
        have hsacc := hacc.register_change out
        obtain ⟨seed,hgood,hseed,hpartial⟩ := hsacc.partialSum
        have hsmask : start.stacks 670 = List.ofFn (fun v : Fin n => pick v.val) :=
          (hfixed 670 (by decide)).trans hmask
        have hsbase : start.stacks 869 = List.ofFn (HighIncidence.glue H high
            (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)) :=
          (hfixed 869 (by decide)).trans hbase
        have hh : (start.stacks 859).length = HighIncidenceProgram.Restriction.highCount (start.stacks 670) := by
          rw [hsmask,HeadRepresentativeSemantics.headOrder_highCount]
          exact hcur.activeWidth hrank
        have hm : (start.stacks 670).length = (start.stacks 869).length := by simp [hsmask,hsbase]
        have hn : (start.stacks 670).length = n := by simp [hsmask]
        obtain ⟨no,o,ns,b,entries,hover,haccepted,ht,hgood',hword,hvalue,hbound,hquery,
          hlow,h854,hframe,_,_,_⟩ := HeadAcceptedCorrect.accepted_eval
            (hsacc.query hq) hsacc.compact seed hgood hseed hsacc.low hsacc.scratch0 hsacc.scratch1
            hh hm hn hcache hcapacity hsize hradius ids
            ((hfixed 175 (by decide)).trans hids) width Z hwidth hZ hP hbit hdegree hhashScale hmarkScale
        have hom : QueryMasterFrame start o := ⟨fun j hj =>
          HeadSumFrames.overlay_frame hh hm hover j
            (HeadAcceptedCorrect.frame_exclusions j (List.mem_append_left _ hj)).1⟩
        have hoq := (hsacc.query hq).frame hom
        have h145 := HeadSumCorrect.prepared_head_update H high (head node) g pick hs reps x
          start o hover hbits hsmask hsbase
        have hv := actual_product_value q H high U
          (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
            (Function.update reps g x)) o ids hoq.highMask hoq.highBits hoq.inner h145 hzero
        have hcontribution : contribution i = value x := by simp [contribution,hrank,hgate.mp hg,x]
        refine ⟨ns,b,ht,haccepted,hframe 859 (by decide),hframe 860 (by decide),
          (hframe 861 (by decide)).trans hscratch,?_⟩
        refine ⟨hbound,fun j hj => (hframe j (retained_accepted j hj)).trans (hacc.retained j hj),
          hlow,(hframe 883 (by decide)).trans hacc.scratch0,
          (hframe 884 (by decide)).trans hacc.scratch1,entries,hgood',hword,?_⟩
        rw [hpartial,hv] at hvalue
        simpa only [Finset.sum_range_succ,hcontribution] using hvalue)
      (by
        intro hg out
        have hn : ¬ selected x := by intro hx; have := hgate.mpr hx; simp [hg] at this
        have hcontribution : contribution i = 0 := by simp [contribution,hrank,hn,x]
        obtain ⟨entries,hgood,hword,hvalue⟩ := hacc.partialSum
        refine ⟨hacc.compact,hacc.retained,hacc.low,hacc.scratch0,hacc.scratch1,
          entries,hgood,hword,?_⟩
        simpa only [Finset.sum_range_succ,hcontribution,add_zero] using hvalue)
    have hcost : bodyBudget state rows (HeadAcceptedCorrect.budget q P S Z) ≤ C := by
      apply HeadEvaluationProgram.StagedGate.bodyBudget_uniform state rows P _ hmat hlen
      · intro row hrow word hword
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hword
        exact hcoeff j k
      · simpa [rows] using hrows
      · exact hacc.compact
    refine ⟨nb,Counters.incrementResult cursorPorts b,hnb.trans hcost,he,?_,?_,
      body_cursor_next hcur hfuel h859 h860 h861,
      Accumulator.advance hcur hfuel h859 h860 h861 hnext hcount⟩
    · rw [Counters.incrementResult_stacks cursorPorts b h861]
      simpa [cursorPorts] using h860
    · exact Counters.incrementResult_scratch cursorPorts b
  obtain ⟨steps,e,hrun,heval,hfinal,hsum,h859,h860,h861,htime,hspace⟩ :=
    HeadAcceptedSpace.head_resources_of_local_time HeadSumAssembly.accepted I h P B C
      (fun _ _ hi => hi.1) (fun _ _ hi => hi.2.compact) (by omega) hcounter spec
      a hshape (fun j => (ha j).trans (by omega)) hi
  obtain ⟨entries,hgood,hword,hvalue⟩ := hfinal.2.partialSum
  have hreindex := HeadSumCorrect.counter_sum_eq_head H
    (fun v : ResidualEmbedding.Free H => head node v.val) g pick hs
    (fun x => if selected x then value x else 0)
  have hout : rawValue q.u q.J q.p.ops.decode entries =
      ∑ x, if selected x then value x else 0 := hvalue.trans (by
        simpa only [contribution,candidate,order,h] using hreindex)
  refine ⟨steps,finalized e,entries,hrun,heval,hgood,hsum.trans hword,hout,?_,?_,
    h859,h860,h861,htime,hspace⟩
  · intro j hj
    obtain ⟨_,_,_,hj859,hj860,_⟩ := retained_exclusions j hj
    simpa only [finalized_stacks,Function.update_of_ne hj860,Function.update_of_ne hj859]
      using hfinal.2.retained j hj
  · have hb := finalize_prefix (finalize_eval e) hfinal.2.compact
    exact hb _ _ le_rfl (compiled_trace (finalize_eval e) 854 853)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorHead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete one-head visitor composes its actual loader, paid key setup,
restricted head rescan and tuple multiplication. Exponential work is kept
separate from the reusable boundary and all-prefix storage bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram
open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage
open scoped BigOperators
noncomputable section

private theorem retained_head (i : Fin 896) (hi : i∈retainedPorts) :
    i∈HeadSumNative.retainedPorts := by
  simp only [retainedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

private theorem retained_multiply (i : Fin 896) (hi : i∈retainedPorts) :
    i∉QueryAssembler.pairScratch ∧ i≠61 ∧ i≠70 ∧ i≠852 ∧ i≠853 := by
  simp only [retainedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- This is the fixed head rescan followed by the actual native dense
multiplication. Its semantic hypotheses are source-word identities and
numerical bounds, never an evaluator or successful-layout service. -/
theorem head_multiply_run_oai {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
          ((chosenIds pick n).get i))
    (ids : List ℕ) (a : HeadSumProgram.Data)
    (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length  ≤  P)
    (hshape : a.stacks 651 = List.replicate (count pick n) false)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
    (hW : a.stacks 864 = W)
    (hmatrix : a.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hcount : count pick n+1  ≤  P) (hrows : q.ps.length  ≤  P)
    (hcoeff : ∀ j i, (c j i).length  ≤  P)
    (hcache : 4*M+6  ≤  P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J  ≤  P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1  ≤  S)
    (hradius : q.p.R+1  ≤  Q) (width : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length  ≤  width)
    (hZ : 1  ≤  Z) (hP : P  ≤  Z) (hbit : q.bitWidth  ≤  Z)
    (hdegree : d * baseWidth 3 q.p.t  ≤  Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length  ≤  Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0  ≤  Z)
    (B : ℕ)
    (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
      HeadAcceptedCorrect.budget q P S Z  ≤  B)
    (hcounter : 9*(count pick n+1)+8  ≤  B)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hpair : PairAccumulatorMeaning q pairValue a)
    (htuple : DenseWord q 852 tupleValue a)
    (hmul : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P) :
    ∃ steps b,
      Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) steps a b ∧
      QueryReady q node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (tupleValue*headValue q node H E U high owner head g reps ids) b ∧
      b.stacks 853=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈retainedPorts,b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ sumBudget q P S Z B (count pick n)+multiplyBudget q P ∧
      QueryExecution.PrefixBound (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) steps a (max B (896*P+multiplyBudget q P)) := by
  obtain ⟨nh,b,entries,htrace,he,hgood,hbytes,hvalue,hframe,hbound,_,_,_,htime,hspace⟩ :=
    HeadSumNative.run q node H E U high owner head g pick hs reps W c hc ids a hq ha
      hshape hmask hbase hW hmatrix hkey hE hH hids hzero hcount hrows hcoeff hcache
      hcapacity hsize hradius width hwidth hZ hP hbit hdegree hhashScale hmarkScale B hlocal hcounter
  have hmasters : QueryMasterFrame a b := ⟨fun j hj =>
    hframe j (List.mem_append_left _ hj)⟩
  have hhead : DenseWord q 853 (headValue q node H E U high owner head g reps ids) b := by
    refine ⟨entries,hbytes,?_,?_⟩
    · simpa only [hq.lifting] using hgood
    · exact Eq.mp (congrArg (fun u => rawValue u q.J q.p.ops.decode entries =
        fiberValue q u node H E U high owner head g reps ids) hq.lifting) hvalue
  have htuple' := htuple.frame (hframe 852 (by decide))
  have hpair' := hpair.frame (hframe 851 (by decide))
  obtain ⟨nm,out,hm,hquery,hpairout,hproduct,hzeroout,hmframe,hout,hf,hregs,hcost,hprefix⟩ :=
    QueryVisitorProgram.multiply_run (hq.frame hmasters) hpair' htuple' hhead hbound hmul
  have hp : QueryExecution.PrefixBound (HeadSumAssembly.head HeadSumAssembly.accepted)
      (nh-1) a B := by
    constructor
    intro elapsed z hle hz
    exact hspace elapsed z (hle.trans (Nat.sub_le _ _)) hz
  have hmp : QueryExecution.PrefixBound QueryAssembler.TupleMultiply.command nm b
      (896*P+multiplyBudget q P) :=
    ⟨fun elapsed z hle hz i => by
      simpa only [multiplyBudget,Nat.add_assoc] using hprefix.bound elapsed z (by omega) hz i⟩
  refine ⟨nh-1+nm,out,he.seq hm,hquery,hpairout,hproduct,hzeroout,
    hmasters.trans hmframe,hout,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hp,h61,h70,h852,h853⟩ := retained_multiply i hi
    exact (hf i hp h61 h70 h852 h853).trans (hframe i (retained_head i hi))
  · intro i hi
    exact (hregs i hi).trans (HeadAcceptedProgram.register_frame htrace i hi)
  · exact Nat.add_le_add ((Nat.sub_le _ _).trans htime)
      (by simpa [multiplyBudget] using Nat.le_of_succ_le hcost)
  · exact QueryExecution.prefix_seq he hm (hp.mono (Nat.le_max_left _ _))
      (hmp.mono (Nat.le_max_right _ _))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run_oai
