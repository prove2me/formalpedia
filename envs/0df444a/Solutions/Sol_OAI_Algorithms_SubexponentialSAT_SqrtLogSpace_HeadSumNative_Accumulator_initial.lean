-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.initial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:40:05.813959+00:00
-- url     : https://prove2.me/submissions/d6ad6dd7-bf90-44f0-adee-f078d7cbec3c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

end Good


end NativeValidity

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

theorem powerResult_frame (d : Data) (j : Fin 896) (h0 : j ≠ 860) (h1 : j ≠ 861) :
    (powerResult d).stacks j = d.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  fin_cases i <;> simp_all [powerStacks]

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState clear_eval)

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

/-- The paid initial state restores the compact boundary used between all
assignments. The transient source-prefix envelope is not fed into this bound. -/
theorem initial_word_bound (a : Data) (h P : ℕ)
    (hshape : a.stacks 651 = List.replicate h false)
    (ha : ∀ i, (a.stacks i).length ≤ P) (hh : h + 1 ≤ P) :
    ∀ i, ((CounterForPrograms.testResult fuelPorts
      (seeded (HeadSumAssembly.cleared a))).stacks i).length ≤ P := by
  have hclear := HeadSumAssembly.clearWork_prefix
    (HeadSumAssembly.clearWork_eval a) ha
  have hb : ∀ i, ((HeadSumAssembly.cleared a).stacks i).length ≤ P :=
    hclear _ _ le_rfl (compiled_trace (HeadSumAssembly.clearWork_eval a) 860 860)
  intro i
  rw [initial_stacks a h hshape]
  by_cases h853 : i = 853
  · subst i
    simp
  by_cases h860 : i = 860
  · subst i
    simpa using hh
  by_cases h859 : i = 859
  · subst i
    simp
    omega
  simpa [h853, h860, h859] using hb i


open HeadIdentifierProgram

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

/-- Initial cleanup, copying and the first fuel test restore every retained
word outside the actual workspace and three initialized arrays. -/
theorem initial_frame (a : Data) (h : ℕ)
    (hshape : a.stacks 651 = List.replicate h false) (i : Fin 896)
    (hlow : 56 ≤ i.val) (hc : i ∉ HeadSumAssembly.controllerPorts)
    (hsum : i ≠ 853) :
    (CounterForPrograms.testResult fuelPorts
      (seeded (HeadSumAssembly.cleared a))).stacks i = a.stacks i := by
  have h859 : i ≠ 859 := by intro he; subst i; exact hc (by decide)
  have h860 : i ≠ 860 := by intro he; subst i; exact hc (by decide)
  have hc0 := HeadSumAssembly.cleared_controller a 859 (by decide)
  have hs0 := HeadSumAssembly.cleared_controller a 861 (by decide)
  have hshape' : (HeadSumAssembly.cleared a).stacks 651 = List.replicate h false :=
    (HeadSumAssembly.cleared_frame a 651 (by decide) (by decide)).trans hshape
  have hseed := seeded_stacks (HeadSumAssembly.cleared a) h hshape' hc0 hs0
  have hs : (seeded (HeadSumAssembly.cleared a)).stacks 861 = [] := by simp [hseed, hs0]
  rw [CounterForPrograms.testResult_stacks fuelPorts _ hs, hseed]
  simp only [Function.update_of_ne hsum, Function.update_of_ne h860,
    Function.update_of_ne h859]
  exact HeadSumAssembly.cleared_frame a i hlow hc

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
open QueryTupleState (masterPorts QueryMasterFrame )
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

namespace Accumulator
variable {r Q n d : ℕ} {q : Factor.Spec r Q n d}
  {origin : HeadSumProgram.Data} {contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J}
  {P i : ℕ} {a b : HeadSumProgram.Data}

theorem initial_oai (q : Factor.Spec r Q n d) (a : HeadSumProgram.Data)
    (contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J) (h P : ℕ)
    (hshape : a.stacks 651 = List.replicate h false)
    (ha : ∀ j, (a.stacks j).length ≤ P) (hh : h+1 ≤ P) :
    Accumulator q a contribution P 0
      (CounterForPrograms.testResult fuelPorts (seeded (HeadSumAssembly.cleared a))) := by
  have hs := HeadSumCorrect.initial_stacks a h hshape
  refine ⟨HeadSumCorrect.initial_word_bound a h P hshape ha hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hl,hc,hsum,_,_,_⟩ := retained_exclusions j hj
    exact HeadSumFrames.initial_frame a h hshape j hl hc hsum
  · intro j
    rw [hs]
    have hv := j.isLt
    have h0 : j.castAdd 840 ≠ (853 : Fin 896) := by intro he; have := congrArg Fin.val he; simp at this; omega
    have h1 : j.castAdd 840 ≠ (860 : Fin 896) := by intro he; have := congrArg Fin.val he; simp at this; omega
    have h2 : j.castAdd 840 ≠ (859 : Fin 896) := by intro he; have := congrArg Fin.val he; simp at this; omega
    simp only [Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h2]
    exact HeadSumAssembly.cleared_low a j
  · rw [hs]
    simp only [Function.update_of_ne (by decide : (883 : Fin 896) ≠ 853),
      Function.update_of_ne (by decide : (883 : Fin 896) ≠ 860),
      Function.update_of_ne (by decide : (883 : Fin 896) ≠ 859)]
    exact HeadSumAssembly.cleared_controller a 883 (by decide)
  · rw [hs]
    simp only [Function.update_of_ne (by decide : (884 : Fin 896) ≠ 853),
      Function.update_of_ne (by decide : (884 : Fin 896) ≠ 860),
      Function.update_of_ne (by decide : (884 : Fin 896) ≠ 859)]
    exact HeadSumAssembly.cleared_controller a 884 (by decide)
  · exact ⟨[],Good.nil,by rw [hs]; rfl,by simp⟩

end Accumulator

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.initial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.initial_oai
