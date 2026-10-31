-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialize_trace_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:29:56.982983+00:00
-- url     : https://prove2.me/submissions/2ccd61ea-e04a-4380-9314-3acd61f4144f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighCountSeed_trace_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySpace_clear_bank_bound

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

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (792 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (clearStacks 792 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (clearStacks 792 a.stacks)=
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i∈changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i≠792 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=6 from rfl,
    hs,readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem reset_blank (a : Data) (i : Fin 896) (hi : i∈changed) :
    (resetState a).stacks i=[] := BankRoutines.clearBankStacks_mem i changed a.stacks hi

theorem copy_eval (a : Data) : Eval copy (7*(a.stacks 330).length+5) (resetState a) (copied a) := by
  unfold copy copied
  apply Eval.call
  simpa only [reset_frame a 330 (by decide)] using
    ListRegisterProgram.copy_run (330 : Fin 896) 789 792 (0 : Fin 40) 1
      (by decide) (by decide) (by decide) (by decide)
      (resetState a).regs (resetState a).stacks (reset_blank a 792 (by decide))

theorem command_eval (a : Data) : Eval command (cost a) a (result a) := by
  simpa only [command, cost, result, Nat.add_assoc] using
    (reset_eval a).seq ((copy_eval a).seq (restoreHighGuard_eval (copied a)))

@[simp] theorem counter (a : Data) : (result a).stacks 789=a.stacks 330 := by
  simp [result,copied,copyStacks,reset_frame a 330 (by decide),reset_blank a 789 (by decide)]

@[simp] theorem blank (a : Data) (i : Fin 896)
    (hi : i∈([788,790,323,791,792] : List (Fin 896))) : (result a).stacks i=[] := by
  have hn : i≠789 := by intro h; subst i; simp at hi
  have hc : i∈changed := by simpa [changed,List.mem_cons,or_assoc,or_left_comm,or_comm] using
    (show i=789 ∨ i∈([788,790,323,791,792] : List (Fin 896)) from Or.inr hi)
  simp [result,copied,copyStacks,hn,reset_blank a i hc]

private theorem reset_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((resetState a).stacks i).length≤bound := by
  intro i
  by_cases hi : i∈changed
  · rw [reset_blank a i hi]; exact Nat.zero_le _
  · rw [reset_frame a i hi]; exact hb i

private theorem reset_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ q z, q ≤ resetCost a → Trace (compiled reset 330 788) q
      (a.withPC (some (compiled reset 330 788).entry)) z → ∀ i, (z.stacks i).length≤bound := by
  let middle : Data := ⟨readRegs a.regs 0 1 none,clearStacks 792 a.stacks⟩
  have first := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (792 : Fin 896) (0 : Fin 40) 1 changed
    (by decide) middle.regs middle.stacks (by simp [middle])
  have hfirst := HighQuerySpace.clear_bound (792 : Fin 896) (0 : Fin 40) 1 a bound hb 330 788
  have hrest := HighQuerySpace.clear_bank_bound (792 : Fin 896) (0 : Fin 40) 1 changed
    (by decide) middle (by simp [middle]) bound
    (HighQuerySpace.clear_state_bound 792 0 1 a bound hb) 330 788
  exact StructuredSpace.sequence_stack_bound first rest 330 788 hfirst hrest
    _ _ _ (compiled_site reset 330 788)

private theorem copy_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ q z, q≤7*(a.stacks 330).length+5 → Trace (compiled copy 330 788) q
      ((resetState a).withPC (some (compiled copy 330 788).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have he := copy_eval a
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _ (compiled_site copy 330 788) tr
    intro q z _ hq
    exact CopySpace.copyProgram_no_growth 330 789 792 0 1 (by decide) (by decide) (by decide)
      rfl (reset_blank a 789 (by decide)) (reset_blank a 792 (by decide)) (reset_bound a bound hb) hq

/-- Every prefix retains the same caller envelope; both cleanup and copy are
proved without a time-based amplification of all retained caller stacks. -/
theorem trace_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    Trace program (cost a+1) (a.withPC (some program.entry)) ((result a).withPC none) ∧
      cost a+1≤21*bound+31 ∧
      ∀ q z, q ≤ cost a+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  have hcopy := copy_space a bound hb
  have hmiddle := hcopy _ _ le_rfl (compiled_trace (copy_eval a) 330 788)
  have hset : ∀ q z, q≤1 → Trace (compiled restoreHighGuard 330 788) q
      ((copied a).withPC (some (compiled restoreHighGuard 330 788).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
    intro q z hq hz
    have hcases : q=0 ∨ q=1 := by omega
    rcases hcases with rfl|rfl
    · cases hz; exact hmiddle
    · rw [trace_same_length_unique hz (compiled_trace (restoreHighGuard_eval (copied a)) 330 788)]
      exact hmiddle
  have htail := StructuredSpace.sequence_stack_bound (copy_eval a) (restoreHighGuard_eval (copied a))
    330 788 hcopy hset _ _ _ (compiled_site (.seq copy restoreHighGuard) 330 788)
  have hbody := StructuredSpace.sequence_stack_bound (reset_eval a)
    ((copy_eval a).seq (restoreHighGuard_eval (copied a))) 330 788
    (reset_space a bound hb) htail _ _ _ (compiled_site command 330 788)
  have hsum : (changed.map (fun i => ((clearStacks 792 a.stacks) i).length)).sum≤6*bound := by
    apply (List.sum_le_card_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=792
      · subst i; simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [changed]
  have htime : cost a+1≤21*bound+31 := by
    have ht := hb 792
    have hs := hb 330
    dsimp [cost,resetCost]
    omega
  refine ⟨compiled_halt_trace (command_eval a) 330 788,htime,?_⟩
  exact StructuredSpace.compiled_halt_stack_bound (command_eval a) 330 788 hbody

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

@[simp] theorem initialized_counter (a : Data) (rf : Fin 2 → Bool) :
    (initialized a rf).stacks 789=Encoding.encodeList id
      (List.replicate (Branches.trueCount (a.stacks 338)) [false]) := by
  rw [initialized,HighCountInit.counter,result_counter]

@[simp] theorem initialized_blank (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : i∈([788,790,323,791,792] : List (Fin 896))) :
    (initialized a rf).stacks i=[] := HighCountInit.blank (result a rf) i hi

/-- No supplied zero counter appears in this concrete entry theorem. Both
resource bounds belong to the very same actual complete source run. -/
theorem initialize_trace_space_oai (a : Data) (localCap bound : ℕ)
    (hm : (a.stacks 338).length≤localCap) (hbudget : 12*localCap+5≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ steps rf, Trace initializeProgram steps (a.withPC (some initializeProgram.entry))
      ((initialized a rf).withPC none) ∧
      steps ≤ 29 * bound + 18 * (a.stacks 338).length + 58 ∧
      ∀ (q : ℕ) z, q ≤ steps → Trace initializeProgram q
        (a.withPC (some initializeProgram.entry)) z → ∀ i, (z.stacks i).length≤bound := by
  obtain ⟨rf,hs,hstime,hsp⟩ := trace_space a localCap bound hm hbudget hb
  have hb' := hsp _ _ le_rfl hs
  obtain ⟨hi,hitime,hip⟩ := HighCountInit.trace_space (result a rf) bound hb'
  have hes := Eval.call program hs
  have hei := Eval.call HighCountInit.program hi
  have hfirst := StructuredSpace.call_stack_bound _ _ _ _
    (compiled_site (.call program) 338 789) hs hsp
  have hsecond := StructuredSpace.call_stack_bound _ _ _ _
    (compiled_site (.call HighCountInit.program) 338 789) hi hip
  have hwhole := StructuredSpace.sequence_stack_bound hes hei 338 789 hfirst hsecond
    _ _ _ (compiled_site initializeCmd 338 789)
  have heval := hes.seq hei
  exact ⟨_,rf,compiled_halt_trace heval 338 789,by omega,
    StructuredSpace.compiled_halt_stack_bound heval 338 789 hwhole⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialize_trace_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed.initialize_trace_space_oai
