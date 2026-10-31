-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:31:11.004377+00:00
-- url     : https://prove2.me/submissions/2d1b6c53-bd24-4033-ba53-5d17e0ca6fb1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S004
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S016
import Definitions.Def_OAIQ081S020
import Definitions.Def_OAIQ081S021
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S037
import Definitions.Def_OAIQ081S038
import Definitions.Def_OAIQ081S042
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S064
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S077
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S146
import Definitions.Def_OAIQ081S151
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S165
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S171
import Definitions.Def_OAIQ081S172
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S176
import Definitions.Def_OAIQ081S178
import Definitions.Def_OAIQ081S182
import Definitions.Def_OAIQ081S183
import Definitions.Def_OAIQ081S185
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryCount_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryExecution_markedReturn_trace_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySetup_PreparedRun_guard_loop
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

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
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

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual per-mark staging and return adapters. Each reference is copied and
reversed into the frontend marker words. Each completed high-assignment count
is moved to the marked collector, with its temporary words reclaimed and parser
registers reset by real instructions. Fresh high-query setup remains mandatory. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter

open BitProgram StructuredCalls SqrtLog LeafOuterProgram

theorem finishState_stacks (a : Data) :
    (finishState a).stacks = BankRoutines.clearBankStacks cleanupPorts
      (Function.update a.stacks 323 (a.stacks 788)) := by
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
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

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace CanonicalHigh
open DisjointReuse

theorem result_frame (a : Data) (i : Fin 896) (h788 : i≠788) (h793 : i≠793) (h794 : i≠794) :
    (result a).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,rfl⟩
  fin_cases j <;> simp_all [stackMap]

open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem final_frame (a : Data) (i : Fin 896) (h788 : i≠788) (h793 : i≠793) (h794 : i≠794) :
    (result (resetState a)).stacks i=a.stacks i := by
  rw [result_frame _ i h788 h793 h794]
  simp [resetState,clearStacks,h793,h794]

end CanonicalHigh


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reclamation after one marked or accepted query. The port list is part
of the fixed program syntax. Only the collector, immutable formula/row inputs,
and the outer caller's high ports survive. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

theorem cleanupPorts_eq :
    cleanupPorts =
      (List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699)) :=
  cleanupPortsWrapped.2

@[simp] theorem mem_cleanupPorts (i : Fin 768) :
    i∈cleanupPorts ↔ ¬Protected i ∧ i≠699 := by
  rw [cleanupPorts_eq]
  simp

theorem cleaned_stacks (a : Data) (i : Fin 768) :
    (cleaned a).stacks i=if Protected i then a.stacks i else [] := by
  by_cases hp : Protected i
  · have hn : i≠699 := by
      intro h
      subst i
      exact (by decide : ¬Protected (699 : Fin 768)) hp
    simp [cleaned,BankRoutines.clearBankStacks,hp,hn]
  · by_cases hn : i=699
    · subst i
      simp [cleaned,BankRoutines.clearBankStacks,show ¬Protected (699 : Fin 768) from by decide]
    · simp [cleaned,BankRoutines.clearBankStacks,hp,hn]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog

theorem result_upper_frame (a : Data) (b : LeafProgram.Query.Data) (i : Fin 896)
    (hi : (768 : ℕ) ≤ i.val) : (result a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

@[simp] theorem cleaned_lower (a : Data) (i : Fin 768) :
    (cleaned a).stacks (stackMap i)=
      if LeafProgram.Query.Protected i then a.stacks (stackMap i) else [] := by
  rw [cleaned,result_stack,LeafProgram.Query.cleaned_stacks]
  rfl

theorem cleaned_upper (a : Data) (i : Fin 896) (hi : (768 : ℕ) ≤ i.val) :
    (cleaned a).stacks i=a.stacks i := result_upper_frame _ _ _ hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedReturn
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete return from a completed marked high-assignment count. All fresh
query workspace is reclaimed, the complete count is moved to323, and the
collector parser registers are reset after cleanup. The compact boundary cap
is distinct from the transient query cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

open BitProgram StructuredCalls RecordPrograms SqrtLog
open HashMarkedQueryAdapter
open HashGreedyProgram.NativeRound

theorem upperPorts_eq :
    upperPorts =
      (List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895)) :=
  upperPortsWrapped.2

@[simp] theorem mem_upperPorts (i : Fin 896) :
    i ∈ upperPorts ↔ 832 ≤ i.val ∧ i.val < 895 := by
  rw [upperPorts_eq]
  simp

/-- Every erased port has an actual clear operation. The single returned word
is the complete high-assignment count, with no Boolean or low-bit conversion. -/
private theorem parserReset_stacks (a : Data) : (parserReset a).stacks=a.stacks := rfl

private theorem kept_lower (j : Fin 768) :
    kept (HighMarkedFrontend.stackMap j)=decide (LeafProgram.Query.Protected j ∧ j≠323) := by
  unfold kept
  rw [decide_eq_decide]
  have hj := j.isLt
  simp only [LeafProgram.Query.Protected,HighMarkedFrontend.stackMap,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod, Fin.castAdd, Fin.val_castLE]
  norm_num only [Nat.reduceMod,Nat.reduceAdd]
  omega

private theorem protected_not_finish (j : Fin 768) (hp : LeafProgram.Query.Protected j) :
    HighMarkedFrontend.stackMap j ∉ cleanupPorts := by
  have hj := j.isLt
  simp only [LeafProgram.Query.Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
  simp only [cleanupPorts, List.mem_cons, List.not_mem_nil, or_false,
    HighMarkedFrontend.stackMap, Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.castAdd,
    Fin.val_castLE]
  norm_num only [Nat.reduceMod,Nat.reduceAdd] at hp ⊢
  omega

theorem result_stacks (a : Data) (i : Fin 896) :
    (result a).stacks i = if i=323 then a.stacks 788 else if kept i then a.stacks i else [] := by
  rw [result,parserReset_stacks]
  simp only [upperCleared]
  by_cases hu : i ∈ upperPorts
  · have hv := mem_upperPorts i |>.mp hu
    have hnot : i ≠ 323 := by intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hv
    have hk : kept i=false := by
      simp only [kept,decide_eq_false_iff_not,Fin.ext_iff]
      omega
    simp [BankRoutines.clearBankStacks,hu,hnot,hk]
  · rw [BankRoutines.clearBankStacks_frame i upperPorts _ hu]
    by_cases hl : i.val < 768
    · let j : Fin 768 := ⟨i.val,hl⟩
      have hij : i=HighMarkedFrontend.stackMap j := rfl
      have heq : HighMarkedFrontend.stackMap j=323 ↔ j=323 := by
        simp only [HighMarkedFrontend.stackMap,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
          Fin.castAdd, Fin.val_castLE]
      rw [hij,HighMarkedFrontend.cleaned_lower,kept_lower]
      by_cases hp : LeafProgram.Query.Protected j
      · rw [ite_eq_left hp, finishState_stacks,
          BankRoutines.clearBankStacks_frame _ _ _ (protected_not_finish j hp)]
        by_cases hj : j=323
        · rw [hj]
          simp [HighMarkedFrontend.stackMap]
        · have hn : HighMarkedFrontend.stackMap j≠323 := heq.not.mpr hj
          simp [hp,hj,hn]
      · have hj : j≠323 := by intro h; apply hp; rw [h]; decide
        have hn : HighMarkedFrontend.stackMap j≠323 := heq.not.mpr hj
        simp [hp,hj,hn]
    · rw [HighMarkedFrontend.cleaned_upper _ i (by omega),finishState_stacks]
      have hv : ¬(832 ≤ i.val ∧ i.val < 895) := (mem_upperPorts i).not.mp hu
      simp only [BankRoutines.clearBankStacks, cleanupPorts, List.mem_cons,
        List.not_mem_nil, or_false, Function.update_apply, kept, Fin.ext_iff]
      split_ifs <;> simp_all <;> omega

@[simp] theorem result_count (a : Data) : (result a).stacks 323=a.stacks 788 := by
  simp [result_stacks]

@[simp] theorem result_collector_source (a : Data) : (result a).stacks 320=a.stacks 320 := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

@[simp] theorem result_accumulator (a : Data) : (result a).stacks 322=a.stacks 322 := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

@[simp] theorem result_payload (a : Data) : (result a).stacks 321=[] := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

@[simp] theorem result_add_scratch (a : Data) : (result a).stacks 324=[] := by
  simp [result_stacks,kept,Fin.coe_ofNat_eq_mod]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid entry to one disjoint high-assignment count. Internal empty binary
words represent zero; the final CanonicalHigh routine emits canonical [false].
The high odometer is copied from the actual encoded seed, never reconstructed
from an assumed family of successful branch states. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

open BitProgram StructuredCalls StackRoutines HighQueryAdapter

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem frame (a : Data) (i : Fin 896) (hi : i∉changed) : (result a).stacks i=a.stacks i := by
  have hn : i≠789 := by intro h; subst i; exact hi (by decide)
  simp [result,copied,copyStacks,hn,reset_frame a i hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountSeed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem result_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  have hn : ¬∃ j,stackMap j=i := by
    rintro ⟨j,rfl⟩
    fin_cases j <;> simp [stackMap,changed] at hi
  rw [show (result a rf).stacks i=(copied a).stacks i from
    embedState_stack_frame regMap stackMap (copied a) _ i hn]
  have h792 : i≠792 := by intro h; subst i; exact hi (by decide)
  simp [copied,copyStacks,h792,reset_frame a i hi]

theorem initialized_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : i∉([330,788,789,790,323,791,792] : List (Fin 896))) :
    (initialized a rf).stacks i=a.stacks i := by
  have hinit : i∉HighCountInit.changed := by simp only [HighCountInit.changed] ; simpa using
    (fun (h : i∈([788,789,790,323,791,792] : List (Fin 896))) => hi (List.mem_cons_of_mem _ h))
  have hseed : i∉changed := by
    simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at *
    tauto
  exact (HighCountInit.frame (result a rf) i hinit).trans (result_frame a rf i hseed)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete outer count execution. The final canonicalization and marked
return consume the entire accumulated binary count. Their compact boundary is
proved separately from the transient workspace used by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution

open OAI BitProgram StructuredCalls HighQueryAdapter DisjointReuse
open HashGreedyProgram.NativeRound

theorem canonicalized_frame (a : Data) (i : Fin 896)
    (h788 : i ≠ 788) (h793 : i ≠ 793) (h794 : i ≠ 794) :
    (canonicalized a).stacks i = a.stacks i := CanonicalHigh.final_frame a i h788 h793 h794

@[simp] theorem returned_count (a : Data) :
    (returned a).stacks 323 = countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  rw [returned,HashMarkedReturn.result_count,canonicalized_count]

/-- Cleanup preserves exactly the caller words in the fixed marked-query ABI.
The high accumulator is first normalized and copied in full, then reclaimed. -/
theorem returned_stacks (a : Data) (i : Fin 896) :
    (returned a).stacks i =
      if i = 323 then countWord (BinaryArithmetic.toNat (a.stacks 788))
      else if HashMarkedReturn.kept i then a.stacks i else [] := by
  rw [returned,HashMarkedReturn.result_stacks,canonicalized_count]
  split_ifs with hc hk
  · rfl
  · have hi : i ≠ 788 ∧ i ≠ 793 ∧ i ≠ 794 := by
      simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff] at hk ⊢
      omega
    exact canonicalized_frame a i hi.1 hi.2.1 hi.2.2
  · rfl

theorem returned_bound (a : Data) (n B : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ B)
    (hkept : ∀ i, HashMarkedReturn.kept i = true → (a.stacks i).length ≤ B) :
    ∀ i, ((returned a).stacks i).length ≤ B := by
  intro i
  rw [returned_stacks]
  split_ifs with hc hk
  · exact (countWord_length_le hcount).trans hn
  · exact hkept i hk
  · exact Nat.zero_le _

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem installAccepted_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval installAccepted
      (2 * (a.stacks 788).length + 9 * (a.stacks 323).length + 11) a (installedAccepted a) := by
  have hr := route_eval (323,788) (by unfold routeValid; decide) a ht
  have hc := BankRoutines.clear_call_eval (323 : Fin 896) (0 : Fin 40) 1
    (routed (323,788) a).regs (routed (323,788) a).stacks
  simp only [routed,Function.update_of_ne (by decide : (323 : Fin 896) ≠ 788),
    readRegs_reset] at hc
  convert hr.seq hc using 1
  · rfl
  · dsimp [routeCost]
    omega
  · rfl

/-- The accepted-query ABI returns only788. All marker, high-iterator and
query-owned scratch ports have paid cleanup instructions. -/
theorem accepted_stacks (a : Data) (i : Fin 896) :
    (accepted a).stacks i =
      if i = 788 then countWord (BinaryArithmetic.toNat (a.stacks 788))
      else if HashMarkedReturn.kept i then a.stacks i else [] := by
  simp only [accepted,installedAccepted,Function.update_apply]
  by_cases h323 : i = 323
  · subst i
    simp [HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod]
  · by_cases h788 : i = 788
    · subst i
      simp [returned_count]
    · simp only [ite_eq_right h323, ite_eq_right h788, returned_stacks]

@[simp] theorem accepted_count (a : Data) :
    (accepted a).stacks 788 = countWord (BinaryArithmetic.toNat (a.stacks 788)) := by
  simp [accepted_stacks]

theorem accepted_exact_frame (entry a : Data)
    (hframe : ∀ i, HashMarkedReturn.kept i = true → a.stacks i = entry.stacks i)
    (hblank : ∀ i, i ≠ 788 → HashMarkedReturn.kept i = false → entry.stacks i = []) :
    (accepted a).stacks = Function.update entry.stacks 788
      (countWord (BinaryArithmetic.toNat (a.stacks 788))) := by
  funext i
  rw [accepted_stacks,Function.update_apply]
  split_ifs with hc hk
  · rfl
  · exact hframe i hk
  · exact (hblank i hc (Bool.eq_false_iff.mpr hk)).symm

private theorem installAccepted_space (a : Data) (D : ℕ)
    (hD : ∀ i, (a.stacks i).length ≤ D) :
    StageSpace installAccepted
      (2 * (a.stacks 788).length + 9 * (a.stacks 323).length + 11) a (931 * D + 54) := by
  constructor
  intro k z hk hz i
  have hin : dataBits (a.withPC (some (compiled installAccepted 778 777).entry)) ≤ 896 * D :=
    StreamResources.dataBits_le_mul _ hD
  have ht : k ≤ 11 * D + 11 := by
    have h788 := hD 788
    have h323 := hD 323
    omega
  have hi := StructuredSpace.local_stack_bound (compiled installAccepted 778 777)
    (steps := 11 * D + 11) hin k z ht hz i
  omega

/-- Final unmarked readback uses the same actual canonicalization and paid
cleanup, then a measured copy and clear. The transient cap is uniform. -/
theorem acceptedReturn_trace_space (a : Data) (n D : ℕ)
    (hcount : BinaryArithmetic.toNat (a.stacks 788) ≤ 2 ^ n) (hn : n + 1 ≤ D)
    (hD : ∀ i, (a.stacks i).length ≤ D) (ht : a.stacks 767 = []) :
    ∃ steps, Eval acceptedReturn steps a (accepted a) ∧
      steps + 1 ≤ 3430 * D + 5147 ∧
      Trace (compiled acceptedReturn 778 777) (steps + 1)
        (a.withPC (some (compiled acceptedReturn 778 777).entry)) ((accepted a).withPC none) ∧
      StageSpace acceptedReturn (steps + 1) a (931 * D + 54) := by
  obtain ⟨nm,hem,hmt,htrace,hmspace⟩ := markedReturn_trace_space a n D hcount hn hD ht
  have hrb := returned_bound a n D hcount hn (fun i _ => hD i)
  have hrt : (returned a).stacks 767 = [] := by
    simpa [returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod] using ht
  have hr788 : (returned a).stacks 788 = [] := by
    simp [returned_stacks,HashMarkedReturn.kept,Fin.coe_ofNat_eq_mod]
  have hei := installAccepted_eval (returned a) hrt
  have hit : 2 * ((returned a).stacks 788).length +
      9 * ((returned a).stacks 323).length + 11 ≤ 9 * D + 11 := by
    rw [hr788]
    have h323 := hrb 323
    simp only [List.length_nil,Nat.mul_zero,zero_add]
    omega
  have hispace := installAccepted_space (returned a) D hrb
  have he := hem.seq hei
  have hmspace' : StageSpace markedReturn nm a (931 * D + 54) :=
    ⟨fun k z hk hz => hmspace.bound k z (by omega) hz⟩
  have hs := StageSpace.seq hem hei hmspace' hispace
  refine ⟨_,he,by omega,compiled_halt_trace he 778 777,?_⟩
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hs.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete high-loop interfaces: the original ternary source count, exact
physical rank order, the fixed stream's durable frame, and its actual native
accumulator. The full loop still requires the actual stream semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

theorem full_count_le {n : ℕ} (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) :
    fullCount hashes marked clause ≤ 2 ^ n := by
  classical
  calc
    _ ≤ ∑ _x : Fin n → Bool, 1 := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = _ := by simp

open HashGreedyProgram.NativeRound


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

theorem PreparedRun.time {q k hg front padding S B cost}
    (run : PreparedRun q k hg front padding S B cost) :
    run.packingSteps + run.arithmeticSteps + 1 + run.seedSteps ≤
      cost + 110 * localBound S cost + 81 := by
  have hpreparation : run.packingSteps + run.arithmeticSteps ≤ cost :=
    run.preparation_time
  have hseed : run.seedSteps ≤ 110 * localBound S cost + 80 := run.seed_time
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual produced ring, parked layout and source bytes at the current-query
high-loop entry. Every field is derived from the same executed preparation
and initializer; no new evaluator or preparation service is supplied. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryPreparedSource

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HighMarkedFrontend HighQuerySetup

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {front : State 40 896} {padding : Fin 8 → ℕ} {S B cost : ℕ}
    (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs

/-- The current physical mask, rather than a mask shared by other marks,
remains available to each actual high decoder. -/
theorem mask : (seeded).stacks 338 =
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask (highSet q) := by
  rw [HighCountSeed.initialized_frame _ _ 338 (by decide)]
  change (preparedOutput front run.data.output).stacks 338 = _
  exact run.mask.trans (physical_high_mask q)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryPreparedSource
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The persistent physical boundary for the actual high-assignment loop.
The ring, source and parked layout words are produced once for this query and
retained across each rank. No execution or evaluator is part of this invariant. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI BitProgram StructuredCalls SqrtLog LeafProgram
open HighQueryAdapter

/-- The high counter and exact accumulator fit the compact boundary from
an independent ambient source cap. No prefix allowance enters this bound. -/
theorem compact_width {n A : ℕ} (H : Finset (Fin n)) (hn : n≤A) :
    4*H.card+1≤QueryHeadBudgets.compact A ∧ n+1≤QueryHeadBudgets.compact A := by
  have hh : H.card≤n := by simpa using Finset.card_le_univ H
  have hs := QueryHeadBudgets.original_le_scalar A
  change 4*H.card+1≤HeadSumBudgets.compactCap (QueryHeadBudgets.scalarCap A) ∧
    n+1≤HeadSumBudgets.compactCap (QueryHeadBudgets.scalarCap A)
  unfold HeadSumBudgets.compactCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual whole-query composition after the high iterator. The two joins
below consume the fixed iterator's measured execution, preserve the same
prepared witnesses, and execute the existing complete return and cleanup.
The public marked and accepted theorems instantiate HighQueryCount directly. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect

open BitProgram StructuredCalls HighMarkedFrontend HighQuerySetup
open HashGreedyProgram.NativeRound

private theorem input_prefix (command : Cmd 40 896) (a : Data) (steps A bound : ℕ)
    (ht : steps  ≤  bound) (ha : ∀ i, (a.stacks i).length  ≤  A) :
    StageSpace command steps a (A + bound) := by
  constructor
  intro t z ht' hz i
  have h := trace_selectedStackBits (compiled command 778 777) {i} hz
  have h' : (z.stacks i).length  ≤  (a.stacks i).length + t := by
    simpa only [selectedStackBits,Finset.sum_singleton] using h
  have := ha i
  omega

section Return

variable {q : SqrtLog.LeafQueryFrontend.Query} {k : ℕ}
  {hg : SqrtLog.LeafParametersProgram.Guard (q.input k)}
  {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
  (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs

/-- The actual accepted query has the same complete sequence but its paid
return leaves the canonical whole word on788 and restores every other word. -/
theorem accepted_of_loop (input last : Data) (frontSteps frontCost loopSteps A D K n count : ℕ)
    (hfront : Eval (HighMarkedFrontend.acceptedCommand k) frontSteps input front)
    (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i, (input.stacks i).length  ≤  A)
    (hloop : Eval HighQueryProgram.highLoop loopSteps seeded last)
    (hloopSpace : StageSpace HighQueryProgram.highLoop loopSteps seeded K)
    (hcount : BinaryArithmetic.toNat (last.stacks 788) = count)
    (hcountBound : count  ≤  2 ^ n) (hn : n + 1  ≤  D)
    (hbound : ∀ i, (last.stacks i).length  ≤  D)
    (hkept : ∀ i, HashMarkedReturn.kept i = true → last.stacks i = input.stacks i)
    (hblank : ∀ i, i  ≠  788 → HashMarkedReturn.kept i = false → input.stacks i = [])
    (hscratch : input.stacks 767 = []) :
    ∃ steps,
      Eval (HighQueryProgram.accepted k) steps input (HighQueryExecution.accepted last) ∧
      steps + 1  ≤  acceptedBudget frontCost S cost loopSteps D ∧
      (HighQueryExecution.accepted last).stacks = Function.update input.stacks 788 (countWord count) ∧
      StageSpace (HighQueryProgram.accepted k) (steps+1) input
        (space q A frontCost S B cost K D) := by
  have hc : BinaryArithmetic.toNat (last.stacks 788)  ≤  2^n := hcount.trans_le hcountBound
  have ht : last.stacks 767 = [] := (hkept 767 (by decide)).trans hscratch
  let ng := run.packingSteps + run.arithmeticSteps + 1 + (run.seedSteps + loopSteps) + 1
  obtain ⟨heg,hsg⟩ := run.guard_loop last loopSteps K hloop hloopSpace
  obtain ⟨nr,her,hrt,_htr,hsr⟩ := HighQueryExecution.acceptedReturn_trace_space last n D hc hn hbound ht
  have he : Eval (HighQueryProgram.accepted k) (frontSteps+(ng+nr)) input
      (HighQueryExecution.accepted last) := hfront.seq (heg.seq her)
  have hfs : StageSpace (HighMarkedFrontend.acceptedCommand k) frontSteps input
      (space q A frontCost S B cost K D) := by
    have h := input_prefix (HighMarkedFrontend.acceptedCommand k) input frontSteps A frontCost hfrontCost hinput
    exact ⟨fun t z ht hz i => (h.bound t z ht hz i).trans (Nat.le_max_left _ _)⟩
  have hgs : StageSpace HighQueryProgram.guardedCount ng front
      (space q A frontCost S B cost K D) := by
    exact ⟨fun t z ht hz i => (hsg.bound t z (by omega) hz i).trans
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))⟩
  have hrs : StageSpace HighQueryExecution.acceptedReturn nr last
      (space q A frontCost S B cost K D) := by
    exact ⟨fun t z ht hz i => (hsr.bound t z (by omega) hz i).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))⟩
  have hpref := StageSpace.seq hfront (heg.seq her) hfs (StageSpace.seq heg her hgs hrs)
  refine ⟨_,he,?_,?_,?_⟩
  · have hp := run.time
    dsimp only [acceptedBudget]
    omega
  · rw [HighQueryExecution.accepted_exact_frame input last hkept hblank,hcount]
  · exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hpref.bound⟩

end Return

section Complete

open SqrtLog LeafParametersProgram LeafProgram PreparedSource PreparedBranchCount

attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {front : Data} {padding : Fin 8 → ℕ} {S B cost : ℕ}
  (run : PreparedRun q k hg front padding S B cost)

local notation "seeded" => HighCountSeed.initialized (result front run.output) run.seedRegs
local notation "model" => Execute.guardedModel (q.input k) padding
local notation "n" => BinaryArithmetic.toNat q.ambient

variable (RB RC RD RI RE : ℕ) (hv : q.Valid)
  (frontBase : Query.Data) (bw : Bank.Words)
  (hfrontState : Query.FrontState q k frontBase (project front) padding bw)
  (hready : q.Ready frontBase) (hindex : q.index=Encoding.encodeNat (markIndex q))
  (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
  (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
  (hwidth : ∀ clause∈source,clause.length ≤ k)
  (A T : ℕ)
  (hwords : ∀ i,((HighCountSeed.initialized (result front run.output) run.seedRegs).stacks i).length ≤ A)
  (hvalues : ∀ i,(Execute.guardedModel (q.input k) padding).val i ≤ A)
  (hAT : A ≤ T) (hqsize : 3^((Execute.guardedModel (q.input k) padding).val 34) ≤ T)

local notation "hashes" => List.map
  (fun terms => List.map (fun term =>
    (Prod.snd term,HashInputProgram.Expansion.originalClause source (Prod.fst term))) terms)
  (castRows (congrArg List.length hsource) (LeafQueryFrontend.Query.rows q))
local notation "count" => fullCount hashes (Option.isSome (LeafQueryFrontend.Query.mark q))
  (List.getD source (markIndex q) [])
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient q)
  (ProducedQueryResources.ofPacking q k RB RC RD RI RE hg run.first run.rest)
local notation "highCost" => loopBudget n (Finset.card (highSet q)) (Circuit.Model.val model 33)
  (Circuit.Model.val model 34) (Circuit.Model.val model 21) (Circuit.Model.val model 42) A T work
local notation "highSpace" => loopSpace n (Finset.card (highSet q)) (Circuit.Model.val model 33)
  (Circuit.Model.val model 34) (Circuit.Model.val model 42) A T

include hv hfrontState hready hindex hwidth hwords hvalues hAT hqsize in
/-- Complete fixed accepted query executes the same actual high-count loop,
then leaves exactly the canonical full count788 and restores all other words. -/
theorem accepted_oai (input : Data) (frontSteps frontCost inputCap : ℕ)
    (hfront : Eval (HighMarkedFrontend.acceptedCommand k) frontSteps input front)
    (hfrontCost : frontSteps  ≤  frontCost) (hinput : ∀ i,(input.stacks i).length ≤ inputCap)
    (hkept : ∀ i,HashMarkedReturn.kept i= true → (seeded).stacks i=input.stacks i)
    (hblank : ∀ i,i ≠ 788 → HashMarkedReturn.kept i= false → input.stacks i=[])
    (hscratch : input.stacks 767=[]) :
    ∃ steps output,
      Eval (HighQueryProgram.accepted k) steps input output ∧
      steps+1 ≤ acceptedBudget frontCost S cost highCost (QueryHeadBudgets.compact A) ∧
      output.stacks=Function.update input.stacks 788 (countWord count) ∧
      StageSpace (HighQueryProgram.accepted k) (steps+1) input
        (space q inputCap frontCost S B cost highSpace (QueryHeadBudgets.compact A)) := by
  change ∀ i : Fin 64, (Execute.guardedModel (q.input k) padding).val i ≤ A at hvalues
  have complete := @HighQueryCount.run q k hg front padding S B cost run
    RB RC RD RI RE hv frontBase bw hfrontState hready hindex
    source hsource hwidth A T hwords
  specialize complete hvalues hAT hqsize
  obtain ⟨nl,last,he,ht,hcount,_hwidth,_h323,_h791,_h789,_h790,_hguard,hframe,hbound,_htrace,hs⟩ := complete
  have htime : nl+1 ≤ highCost := by
    dsimp only [loopBudget]
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hn : n ≤ A := by
    have hh := hwords 338
    rw [HighQueryPreparedSource.mask run] at hh
    simpa [HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using hh
  have hw := (HighQueryCount.compact_width (highSet q) hn).2
  have hp : StageSpace HighQueryProgram.highLoop nl seeded highSpace :=
    ⟨fun t z ht hz i => hs.bound t z (by omega) hz i⟩
  obtain ⟨steps,whole,hcost,hword,hspace⟩ :=
    accepted_of_loop run input last frontSteps frontCost nl inputCap
      (QueryHeadBudgets.compact A) highSpace n count hfront hfrontCost hinput he hp hcount
      (HighQueryLoop.full_count_le _ _ _) hw hbound
      (fun i hi => (hframe i hi).trans (hkept i hi)) hblank hscratch
  refine ⟨steps,_,whole,?_,hword,hspace⟩
  exact hcost.trans (by dsimp only [acceptedBudget]; omega)

end Complete
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted_oai
