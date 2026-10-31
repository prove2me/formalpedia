-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:26:56.579379+00:00
-- url     : https://prove2.me/submissions/6cc05cda-75cf-4af3-9c56-6dac2db615c0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S162
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQuerySpace_clear_bank_bound
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

theorem copyStacks_frame {S : Type u} [DecidableEq S] (src dst j : S)
    (stk : Stacks S) (hj : j ≠ dst) : copyStacks src dst stk j = stk j := by
  simp [copyStacks, hj]

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

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

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

namespace HeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem pop_eval (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool) :
    Eval pop 1 (state regs mask bits rev out ones) (popped regs mask bits rev out ones) := by
  convert Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 5) (0 : Fin 4) 1)
    (state regs mask bits rev out ones)) using 1
  · rfl
  · apply congrArg (StructuredProgram.State.mk _)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem iteration (regs : Fin 4 → Bool) (b x : Bool) (mask bits rev out ones : List Bool) :
    ∃ rf, Eval body 5 (popped regs (b::mask) (x::bits) rev out ones)
      (popped rf mask bits (if b then x::rev else rev) out (if b then true::ones else ones)) := by
  let a := popped regs (b::mask) (x::bits) rev out ones
  let r := readRegs (readRegs regs 0 1 (some b)) 2 3 (some x)
  have hp : Eval (.base (.atom (.pop (1 : Fin 5) (2 : Fin 4) 3))) 1 a
      (state r mask bits rev out ones) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 5) (2 : Fin 4) 3) a) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> simp [a, popped, state, readRegs,
      StructuredProgram.Atom.instr, execInstr]
  have hs : Eval (.ite (0 : Fin 4) keep drop) 3 (state r mask bits rev out ones)
      (state r mask bits (if b then x::rev else rev) out (if b then true::ones else ones)) := by
    cases b with
    | false =>
        apply Eval.ite_false (by simp [r,readRegs,state])
        have h := (Eval.base (StructuredProgram.Eval.atom (.copy (2 : Fin 4) 2)
          (state r mask bits rev out ones))).seq
          (Eval.base (StructuredProgram.Eval.atom (.copy (3 : Fin 4) 3) _))
        simpa [drop,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.withPC,StructuredProgram.State.ofCfg,execInstr] using h
    | true =>
        apply Eval.ite_true (by simp [r,readRegs,state])
        have h := (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 5) (2 : Fin 4))
          (state r mask bits rev out ones))).seq
          (Eval.base (StructuredProgram.Eval.atom (.push (4 : Fin 5) (3 : Fin 4)) _))
        convert h using 1
        · rfl
        · apply congrArg (StructuredProgram.State.mk _)
          funext i
          fin_cases i <;> simp [state, r, readRegs, StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  exact ⟨r,hp.seq (hs.seq (pop_eval r mask bits
    (if b then x::rev else rev) out (if b then true::ones else ones)))⟩

theorem loop_eval (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool)
    (hlen : mask.length=bits.length) :
    ∃ rf, Eval loop (6*mask.length+1) (popped regs mask bits rev out ones)
      (state rf [] [] ((Restriction.selected true mask bits).reverse++rev) out
        (List.replicate (Restriction.highCount mask) true++ones)) := by
  induction mask generalizing regs bits rev ones with
  | nil =>
      have he : bits=[] := List.eq_nil_of_length_eq_zero hlen.symm
      subst bits
      exact ⟨readRegs regs 0 1 none,Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases bits with
      | nil => simp at hlen
      | cons x bits =>
          obtain ⟨ri,hi⟩ := iteration regs b x mask bits rev out ones
          obtain ⟨rf,hr⟩ := ih ri bits (if b then x::rev else rev)
            (if b then true::ones else ones) (by simpa using hlen)
          have h := Eval.while_true (show (popped regs (b::mask) (x::bits) rev out ones).regs 1=true by rfl) hi hr
          have hlen' : mask.length = bits.length := by simpa using hlen
          refine ⟨rf,?_⟩
          cases b with
          | false =>
              convert h using 1
              · rfl
              · simp only [List.length_cons] at *
                omega
              · simp [Restriction.selected, Restriction.highCount,
                  Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful]
          | true =>
              convert h using 1
              · rfl
              · simp only [List.length_cons] at *
                omega
              · simp [Restriction.selected, Restriction.highCount,
                  Subexp.PaddedCompletion.trueCount, Subexp.PaddedCompletion.successful,
                  List.reverse_cons, List.append_assoc, List.replicate_succ']

theorem command_eval (regs : Fin 4 → Bool) (mask bits : List Bool)
    (hlen : mask.length=bits.length) :
    ∃ rf, Eval command (6*mask.length+3*Restriction.highCount mask+5)
      (state regs mask bits [] [] [])
      (state rf [] [] [] (Restriction.selected true mask bits)
        (List.replicate (Restriction.highCount mask) true)) := by
  obtain ⟨rs,hl⟩ := loop_eval regs mask bits [] [] [] hlen
  simp only [List.append_nil] at hl
  have ht := ListRegisterProgram.transfer_run (2 : Fin 5) 3 (0 : Fin 4) 1
    (by decide) (by decide) rs
    (state rs [] [] (Restriction.selected true mask bits).reverse []
      (List.replicate (Restriction.highCount mask) true)).stacks
  have hs : transferStacks 2 3
      (state rs [] [] (Restriction.selected true mask bits).reverse []
        (List.replicate (Restriction.highCount mask) true)).stacks =
      (state (readRegs rs 0 1 none) [] [] [] (Restriction.selected true mask bits)
        (List.replicate (Restriction.highCount mask) true)).stacks := by
    funext i; fin_cases i <;> simp [transferStacks,state]
  have hc : Eval (.call (transferProgram (2 : Fin 5) 3 (0 : Fin 4) 1))
      (3*Restriction.highCount mask+3)
      (state rs [] [] (Restriction.selected true mask bits).reverse []
        (List.replicate (Restriction.highCount mask) true))
      (state (readRegs rs 0 1 none) [] [] [] (Restriction.selected true mask bits)
        (List.replicate (Restriction.highCount mask) true)) := by
    apply Eval.call
    change Trace _ (3*(Restriction.selected true mask bits).reverse.length+3) _ _ at ht
    rw [hs] at ht
    simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, state,
      Restriction.highCount, List.length_reverse,
      Restriction.selected_true_length mask bits hlen] using ht
  refine ⟨readRegs rs 0 1 none,?_⟩
  convert (pop_eval regs mask bits [] [] []).seq (hl.seq hc) using 1
  · rfl
  · omega

end HeadSelect

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem command_eval (a : Data)
    (he : ∀ i ∈ changed, a.stacks i=[])
    (hlen : (a.stacks 670).length=(a.stacks 858).length) :
    ∃ rf, Eval command (20*(a.stacks 670).length+3*Restriction.highCount (a.stacks 670)+16)
      a (result a rf) := by
  have ht : a.stacks 880=[] := he 880 (by simp [changed])
  have h1 : Eval (copy 858 878) (7*(a.stacks 858).length+5) a
      ⟨readRegs a.regs 0 1 none,copyStacks 858 878 a.stacks⟩ :=
    .call _ (ListRegisterProgram.copy_run 858 878 880 0 1 (by decide) (by decide)
      (by decide) (by decide) a.regs a.stacks ht)
  have h2 : Eval (copy 670 879) (7*(a.stacks 670).length+5)
      ⟨readRegs a.regs 0 1 none,copyStacks 858 878 a.stacks⟩ (copied a) := by
    apply Eval.call
    simpa only [copied, StackRoutines.readRegs_reset,
      copyStacks_frame 858 878 670 a.stacks (by decide)] using
      ListRegisterProgram.copy_run (670 : Fin 896) 879 880 (0 : Fin 40) 1
        (by decide) (by decide) (by decide) (by decide)
        (readRegs a.regs 0 1 none) (copyStacks 858 878 a.stacks)
        (by simpa only [copyStacks_frame 858 878 880 a.stacks (by decide)] using ht)
  have hp : projectState regs stackMap (copied a) =
      HeadSelect.state ((copied a).regs ∘ regs) (a.stacks 670) (a.stacks 858) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [copied, stackMap, copyStacks,
        he 867 (by simp [changed]),he 868 (by simp [changed]),he 877 (by simp [changed]),
        he 878 (by simp [changed]),he 879 (by simp [changed])]
  obtain ⟨rf,hs⟩ := HeadSelect.command_eval ((copied a).regs ∘ regs)
    (a.stacks 670) (a.stacks 858) hlen
  have hx := compiled_halt_trace hs 0 3
  rw [← hp] at hx
  have h3 := eval_call_from_state HeadSelect.program regs stackMap (copied a)
    (Fin.castAdd_injective _ _) (by decide) hx
  refine ⟨rf,?_⟩
  have hh := h1.seq (h2.seq h3)
  rw [← hlen] at hh
  convert hh using 1
  · rfl
  · omega
  · rfl

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (880 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (880 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (StackRoutines.clearStacks 880 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (StackRoutines.clearStacks 880 a.stacks) =
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i ∈ changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i ≠ 880 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=6 from rfl,
    hs,StackRoutines.readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi


/-- Repeated calls pay to discard every old output and work buffer before the
new head projection. The only input shape condition is equal ambient lengths. -/
theorem prepare_trace_space (a : Data) (bound : ℕ)
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hb : ∀ i, (a.stacks i).length≤bound) :
    ∃ (steps : ℕ), ∃ rf, Trace prepareProgram steps (a.withPC (some prepareProgram.entry))
      ((result (resetState a) rf).withPC none) ∧ steps ≤ 37*bound+41 ∧
      ∀ (prefixSteps : ℕ) intermediate, Nat.le prefixSteps steps →
        Trace prepareProgram prefixSteps (a.withPC (some prepareProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length≤933*bound+41 := by
  have hm : (resetState a).stacks 670=a.stacks 670 := reset_frame a 670 (by decide)
  have he : (resetState a).stacks 858=a.stacks 858 := reset_frame a 858 (by decide)
  obtain ⟨rf,hs⟩ := command_eval (resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i changed a.stacks hi)
    (by simpa only [hm,he] using hlen)
  have hsum : (changed.map (fun i => ((clearStacks 880 a.stacks) i).length)).sum≤6*bound := by
    apply (List.sum_le_card_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=880
      · subst i
        simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [changed]
  have hc : resetCost a≤14*bound+24 := by
    dsimp [resetCost]
    have := hb 880
    omega
  have hh : Restriction.highCount (a.stacks 670)≤(a.stacks 670).length :=
    List.length_filter_le _ _
  have htime : resetCost a+(20*((resetState a).stacks 670).length+
      3*Restriction.highCount ((resetState a).stacks 670)+16)+1≤37*bound+41 := by
    rw [hm]
    have := hb 670
    omega
  have hx := (reset_eval a).seq hs
  refine ⟨_,rf,compiled_halt_trace hx 858 867,htime,?_⟩
  have hin : dataBits (a.withPC (some prepareProgram.entry))≤896*bound :=
    StreamResources.dataBits_le_mul _ (by simpa using hb)
  intro prefixSteps intermediate hle htrace i
  have hbound := StructuredSpace.local_stack_bound prepareProgram (steps:=37*bound+41) hin
    prefixSteps intermediate (Nat.le_trans hle htime) htrace i
  omega

@[simp] theorem prepared_E (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 867=Restriction.selected true (a.stacks 670) (a.stacks 858) := by
  rw [result_E,reset_frame a 670 (by decide),reset_frame a 858 (by decide)]

@[simp] theorem prepared_H (a : Data) (rf : Fin 4 → Bool) :
    (result (resetState a) rf).stacks 868=List.replicate (Restriction.highCount (a.stacks 670)) true := by
  rw [result_H,reset_frame a 670 (by decide)]

end NativeHeadSelect

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

theorem lifted_call_bound {r s l R S : ℕ}
    (p : Program r s l) (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (a : State R S) (d e : State r s) (hproject : projectState reg stk a=d)
    (steps bound : ℕ) (ht : Trace p steps (d.withPC (some p.entry)) (e.withPC none))
    (hlocal : ∀ (q : ℕ) z, q ≤ steps → Trace p q (d.withPC (some p.entry)) z →
      ∀ i, (z.stacks i).length≤bound)
    (hb : ∀ i, (a.stacks i).length≤bound) (input output : Fin S) :
    ∀ (q : ℕ) z, q ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output) q
        (a.withPC (some (compiled (.call (ProgramLinking.liftProgram p reg stk)) input output).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have hstart : embedState reg stk a d=a := by rw [←hproject,embedState_project reg stk a hr hs]
  have he := eval_call_lifted p reg stk a hr hs ht
  rw [hstart] at he
  have hglobal := StructuredSpace.liftProgram_stack_bound p reg stk (a.withPC none) hr hs ht hlocal hb
  have hinit : ProgramLinking.embedCfg reg stk id none (a.withPC none) (d.withPC (some p.entry)) =
      a.withPC (some (ProgramLinking.liftProgram p reg stk).entry) := by
    change (embedState reg stk a d).withPC _ = _
    rw [hstart]
    rfl
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call routine ht =>
      exact StructuredSpace.call_stack_bound _ _ _ _ (compiled_site (.call (ProgramLinking.liftProgram p reg stk)) input output) ht hglobal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSelectionSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace
open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

/-- Reset never grows a retained caller stack, even when an old output word
must first be physically cleared. -/
theorem reset_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∀ i,((NativeHeadSelect.resetState a).stacks i).length≤B := by
  intro i
  by_cases hi : i∈NativeHeadSelect.changed
  · simp [NativeHeadSelect.resetState,BankRoutines.clearBankStacks,hi]
  · simpa [NativeHeadSelect.resetState,BankRoutines.clearBankStacks,hi] using ha i

theorem reset_space (a : State 40 896) (B : ℕ)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∀ q z,q≤NativeHeadSelect.resetCost a →
      Trace (compiled NativeHeadSelect.reset 858 867) q
        (a.withPC (some (compiled NativeHeadSelect.reset 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
  let middle : State 40 896 := ⟨readRegs a.regs 0 1 none,clearStacks 880 a.stacks⟩
  have first := BankRoutines.clear_call_eval (880:Fin 896) (0:Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (880:Fin 896) (0:Fin 40) 1 NativeHeadSelect.changed
    (by decide) middle.regs middle.stacks (by simp [middle])
  have hf := HighQuerySpace.clear_bound (880:Fin 896) (0:Fin 40) 1 a B ha 858 867
  have hr := HighQuerySpace.clear_bank_bound (880:Fin 896) (0:Fin 40) 1 NativeHeadSelect.changed
    (by decide) middle (by simp [middle]) B
    (HighQuerySpace.clear_state_bound 880 0 1 a B ha) 858 867
  exact StructuredSpace.sequence_stack_bound first rest 858 867 hf hr _ _ _
    (compiled_site NativeHeadSelect.reset 858 867)

/-- The only growing part is a five-stack local scan with ambient input
length≤P. Its11P+6 transient allowance is independent of caller envelope B. -/
theorem command_space (a : State 40 896) (P B : ℕ)
    (he : ∀ i∈NativeHeadSelect.changed,a.stacks i=[])
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hsize : (a.stacks 670).length≤P) (hlocal : 11*P+6≤B)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∀ q z,q≤20*(a.stacks 670).length+3*Restriction.highCount (a.stacks 670)+16 →
      Trace (compiled NativeHeadSelect.command 858 867) q
        (a.withPC (some (compiled NativeHeadSelect.command 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
  have h880 : a.stacks 880=[] := he 880 (by decide)
  let middle : State 40 896 := ⟨readRegs a.regs 0 1 none,copyStacks 858 878 a.stacks⟩
  have first : Eval (NativeHeadSelect.copy 858 878) (7*(a.stacks 858).length+5) a middle :=
    .call _ (ListRegisterProgram.copy_run 858 878 880 0 1 (by decide) (by decide)
      (by decide) (by decide) a.regs a.stacks h880)
  have second : Eval (NativeHeadSelect.copy 670 879) (7*(a.stacks 670).length+5)
      middle (NativeHeadSelect.copied a) := by
    apply Eval.call
    simpa [middle, NativeHeadSelect.copied, copyStacks, h880] using
      ListRegisterProgram.copy_run (670:Fin 896) 879 880 (0:Fin 40) 1
        (by decide) (by decide) (by decide) (by decide)
        middle.regs middle.stacks (by simp [middle,copyStacks,h880])
  have hf : ∀ q z,q≤7*(a.stacks 858).length+5 →
      Trace (compiled (NativeHeadSelect.copy 858 878) 858 867) q
        (a.withPC (some (compiled (NativeHeadSelect.copy 858 878) 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
    cases first with
    | call p tr =>
      apply StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (NativeHeadSelect.copy 858 878) 858 867) tr
      intro q z _ hz
      exact CopySpace.copyProgram_no_growth 858 878 880 0 1 (by decide) (by decide)
        (by decide) rfl (he 878 (by decide)) h880 ha hz
  have hm : ∀ i,(middle.stacks i).length≤B := hf _ _ le_rfl (compiled_trace first 858 867)
  have hs : ∀ q z,q≤7*(a.stacks 670).length+5 →
      Trace (compiled (NativeHeadSelect.copy 670 879) 858 867) q
        (middle.withPC (some (compiled (NativeHeadSelect.copy 670 879) 858 867).entry)) z →
      ∀ i,(z.stacks i).length≤B := by
    cases second with
    | call p tr =>
      apply StructuredSpace.call_stack_bound _ _ _ _
        (compiled_site (NativeHeadSelect.copy 670 879) 858 867) tr
      intro q z _ hz
      exact CopySpace.copyProgram_no_growth 670 879 880 0 1 (by decide) (by decide)
        (by decide) rfl (by simp [middle,copyStacks,he 879 (by decide)])
        (by simp [middle,copyStacks,h880]) hm hz
  have hc : ∀ i,((NativeHeadSelect.copied a).stacks i).length≤B :=
    hs _ _ le_rfl (compiled_trace second 858 867)
  have hp : projectState NativeHeadSelect.regs NativeHeadSelect.stackMap (NativeHeadSelect.copied a) =
      HeadSelect.state ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs)
        (a.stacks 670) (a.stacks 858) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [NativeHeadSelect.copied,NativeHeadSelect.stackMap,
        copyStacks,he 867 (by decide),he 868 (by decide),he 877 (by decide),
        he 878 (by decide),he 879 (by decide)]
  obtain ⟨rf,localEval⟩ := HeadSelect.command_eval
    ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs) (a.stacks 670) (a.stacks 858) hlen
  have localTrace := compiled_halt_trace localEval 0 3
  have hcount : Restriction.highCount (a.stacks 670)≤(a.stacks 670).length :=
    List.length_filter_le _ _
  have localBound : ∀ q z,q≤6*(a.stacks 670).length+3*Restriction.highCount (a.stacks 670)+5+1 →
      Trace HeadSelect.program q
        ((HeadSelect.state ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs)
          (a.stacks 670) (a.stacks 858) [] [] []).withPC (some HeadSelect.program.entry)) z →
      ∀ i,(z.stacks i).length≤B := by
    have hi : dataBits ((HeadSelect.state ((NativeHeadSelect.copied a).regs ∘ NativeHeadSelect.regs)
        (a.stacks 670) (a.stacks 858) [] [] []).withPC (some HeadSelect.program.entry))≤2*P := by
      simp [dataBits,stackBits,HeadSelect.state,Fin.sum_univ_succ]
      omega
    intro q z hq hz i
    have ht := StructuredSpace.local_stack_bound HeadSelect.program (steps:=9*P+6) hi
      q z (by omega) hz i
    omega
  have hlast := HighQuerySpace.lifted_call_bound HeadSelect.program NativeHeadSelect.regs
    NativeHeadSelect.stackMap (Fin.castAdd_injective _ _) (by decide)
    (NativeHeadSelect.copied a) _ _ hp _ B localTrace localBound hc 858 867
  rw [←hp] at localTrace
  have last := eval_call_from_state HeadSelect.program NativeHeadSelect.regs NativeHeadSelect.stackMap
    (NativeHeadSelect.copied a) (Fin.castAdd_injective _ _) (by decide) localTrace
  have tail := StructuredSpace.sequence_stack_bound second last 858 867 hs hlast _ _ _
    (compiled_site (.seq (NativeHeadSelect.copy 670 879) NativeHeadSelect.select) 858 867)
  have whole := StructuredSpace.sequence_stack_bound first (second.seq last) 858 867 hf tail _ _ _
    (compiled_site NativeHeadSelect.command 858 867)
  obtain ⟨out,canonical⟩ := NativeHeadSelect.command_eval a he hlen
  have htime := StreamResources.eval_steps_eq 858 867 (first.seq (second.seq last)) canonical
  simpa only [NativeHeadSelect.command, NativeHeadSelect.select, StructuredCalls.compiled,
    htime] using whole

/-- Paid reset and selection share one caller bound, including every final
halt and every old output discarded before a repeated head setup. -/
theorem prepare_trace_space_oai (a : State 40 896) (P B : ℕ)
    (hlen : (a.stacks 670).length=(a.stacks 858).length)
    (hsize : (a.stacks 670).length≤P) (hlocal : 11*P+6≤B)
    (ha : ∀ i,(a.stacks i).length≤B) :
    ∃ steps rf,Trace NativeHeadSelect.prepareProgram steps
      (a.withPC (some NativeHeadSelect.prepareProgram.entry))
      ((NativeHeadSelect.result (NativeHeadSelect.resetState a) rf).withPC none) ∧
      steps≤37*B+41 ∧
      ∀ (q : ℕ) z, Nat.le q steps → Trace NativeHeadSelect.prepareProgram q
        (a.withPC (some NativeHeadSelect.prepareProgram.entry)) z →
        ∀ i,(z.stacks i).length≤B := by
  have hm := NativeHeadSelect.reset_frame a 670 (by decide)
  have he := NativeHeadSelect.reset_frame a 858 (by decide)
  have hclean : ∀ i∈NativeHeadSelect.changed,(NativeHeadSelect.resetState a).stacks i=[] :=
    fun i hi => BankRoutines.clearBankStacks_mem i NativeHeadSelect.changed a.stacks hi
  have hlen' : ((NativeHeadSelect.resetState a).stacks 670).length=
      ((NativeHeadSelect.resetState a).stacks 858).length := by simpa only [hm,he] using hlen
  obtain ⟨rf,hs⟩ := NativeHeadSelect.command_eval (NativeHeadSelect.resetState a) hclean hlen'
  have heval := (NativeHeadSelect.reset_eval a).seq hs
  have hf := reset_space a B ha
  have hg := command_space (NativeHeadSelect.resetState a) P B hclean hlen'
    (by simpa only [hm] using hsize) hlocal (reset_bound a B ha)
  have hp := StructuredSpace.sequence_stack_bound (NativeHeadSelect.reset_eval a) hs
    858 867 hf hg _ _ _ (compiled_site NativeHeadSelect.prepare 858 867)
  have bound := StructuredSpace.compiled_halt_stack_bound heval 858 867 hp
  obtain ⟨n,r,htr,htime,_⟩ := NativeHeadSelect.prepare_trace_space a B hlen ha
  have hsteps : n=NativeHeadSelect.resetCost a+
      (20*((NativeHeadSelect.resetState a).stacks 670).length+
        3*Restriction.highCount ((NativeHeadSelect.resetState a).stacks 670)+16)+1 :=
    StreamResources.halted_trace_steps_eq htr (compiled_halt_trace heval 858 867) rfl rfl
  refine ⟨_,rf,compiled_halt_trace heval 858 867,?_,bound⟩
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space_oai
