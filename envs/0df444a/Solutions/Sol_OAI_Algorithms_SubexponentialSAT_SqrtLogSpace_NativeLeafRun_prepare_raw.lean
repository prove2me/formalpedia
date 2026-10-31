-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:42:58.395212+00:00
-- url     : https://prove2.me/submissions/8d7e3a67-939b-466f-afc2-fdd2d9e4a56d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation_afterCanonical_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafSetup_start_trace_space

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual normalization of a positive binary counter word

The logarithm preparer reverses its input and removes high zeroes together
with the leading one. This wrapper physically restores that one and reverses
the remaining word. Positive inputs therefore retain their exact value and
have width log2(value)+1. All three registers and both work stacks are clean
at return, even when the incoming registers are arbitrary.
-/

namespace SubexponentialSAT.CounterNormalizeProgram

open BitProgram StructuredProgram StructuredCalls CounterPrograms

theorem normalized_value (bits : List Bool) (hp : 0 < value bits) :
    value (normalized bits) = value bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [value] at hp
  | append_singleton bits bit ih =>
    cases bit with
    | false =>
      have hp' : 0 < value bits := by
        simpa [SubexpParameterProgram.value_append, value] using hp
      simpa [normalized, List.reverse_append, SubexpParameterProgram.trimTail,
        SubexpParameterProgram.value_append, value] using ih hp'
    | true =>
      simp [normalized, List.reverse_append, SubexpParameterProgram.trimTail]

theorem normalized_length (bits : List Bool) :
    (normalized bits).length = Nat.log2 (value bits) + 1 := by
  simp [normalized, SubexpParameterProgram.trimTail_reverse_length]

theorem normalized_eq_fixedBits (bits : List Bool) (hp : 0 < value bits) :
    normalized bits = SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits) := by
  have hcap : value bits < 2 ^ (Nat.log2 (value bits) + 1) := by
    simpa only [normalized_value bits hp, normalized_length] using
      SubexpParameterProgram.value_lt_two_pow_length (normalized bits)
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [normalized_length, SubexpLiftRing.fixedBits_length]
  · rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ hcap,
      ← CounterPrograms.value_eq_toNat]
    exact normalized_value bits hp

private theorem data_ext {a b : Data} (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) :
    a = b := by cases a; cases b; cases hr; cases hs; rfl

theorem reset_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    StructuredCalls.Eval reset 3 (state regs bits []) (state zeroRegs bits []) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) (state regs bits [])).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) false) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  apply StructuredCalls.Eval.base
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply data_ext
  · funext i
    fin_cases i <;>
      simp [state, zeroRegs, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  · rfl

theorem prepare_eval (bits : List Bool) :
    ∃ n, n ≤ 6 * bits.length + 9 ∧
      StructuredCalls.Eval (.call SubexpParameterProgram.prepareLogProgram) n
        (state zeroRegs bits [])
        (state zeroRegs [] (SubexpParameterProgram.trimTail bits.reverse)) := by
  obtain ⟨n, hn, ht⟩ := SubexpParameterProgram.prepareLog_runs bits
  have ha : initial SubexpParameterProgram.prepareLogProgram bits =
      (state zeroRegs bits []).withPC (some SubexpParameterProgram.prepareLogProgram.entry) := by
    simp only [initial, state, State.withPC ]
    congr 1
    first | done | (funext i; fin_cases i <;> rfl)
  have hb : terminal SubexpParameterProgram.prepareLogProgram
        (SubexpParameterProgram.trimTail bits.reverse) =
      (state zeroRegs [] (SubexpParameterProgram.trimTail bits.reverse)).withPC none := by
    simp only [terminal, state, State.withPC ]
    congr 1
    first | done | (funext i; fin_cases i <;> rfl)
  exact ⟨n, hn, .call _ (by simpa only [ha, hb] using ht)⟩

theorem pushTop_eval (d : Data) : StructuredCalls.Eval pushTop 2 d (pushed d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) true) d).seq
    (StructuredProgram.Eval.atom (.push (1 : Fin 3) 0) _)
  exact .base (by simpa [pushed, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h)

theorem reverse_eval (d : Data) :
    StructuredCalls.Eval (.call reverseProgram) (3 * (d.stacks 1).length + 3) d (transferred d) :=
  .call _ (ListRegisterProgram.transfer_run 1 0 0 1 (by decide) (by decide) d.regs d.stacks)

theorem restore_eval (tail : List Bool) :
    StructuredCalls.Eval restore (3 * tail.length + 8) (state zeroRegs [] tail)
      (state zeroRegs (true :: tail).reverse []) := by
  have h := (pushTop_eval (state zeroRegs [] tail)).seq
    (reverse_eval (pushed (state zeroRegs [] tail)))
  have heq : transferred (pushed (state zeroRegs [] tail)) =
      state zeroRegs (true :: tail).reverse [] := by
    apply data_ext
    · funext i
      fin_cases i <;> simp [transferred, pushed, state, zeroRegs, readRegs]
    · funext i
      fin_cases i <;> simp [transferred, pushed, state, StackRoutines.transferStacks]
  convert h using 1
  · simp [pushed, state]
    omega
  · exact heq.symm

theorem command_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    ∃ n, StructuredCalls.Eval command n (state regs bits [])
      (state zeroRegs (normalized bits) []) ∧ n ≤ 9 * bits.length + 20 := by
  obtain ⟨n, hn, he⟩ := prepare_eval bits
  refine ⟨3 + (n + (3 * (SubexpParameterProgram.trimTail bits.reverse).length + 8)),
    (reset_eval regs bits).seq (he.seq (restore_eval _)), ?_⟩
  have hlen : (SubexpParameterProgram.trimTail bits.reverse).length ≤ bits.length := by
    simpa using SubexpParameterProgram.trimTail_length_le bits.reverse
  omega

theorem normalize_eval (regs : Fin 3 → Bool) (bits : List Bool) (hp : 0 < value bits) :
    ∃ n, StructuredCalls.Eval command n (state regs bits [])
      (state zeroRegs (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)) []) ∧
      n ≤ 9 * bits.length + 20 := by
  simpa only [normalized_eq_fixedBits bits hp] using command_eval regs bits

theorem normalize_runs (regs : Fin 3 → Bool) (bits : List Bool) (hp : 0 < value bits) :
    BitProgram.RunsIn program (9 * bits.length + 21)
      ((state regs bits []).withPC (some program.entry))
      ((state zeroRegs (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)) []).withPC none) := by
  obtain ⟨n, he, hn⟩ := normalize_eval regs bits hp
  exact ⟨n + 1, by omega, StructuredCalls.compiled_halt_trace he 0 0⟩

end SubexponentialSAT.CounterNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSparsifyEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact syntax and normalization bridges for the word-based node search. -/

namespace SubexponentialSAT.ExecSparsifyEncoding

open ExecCNF ExecSunflowerCodeTransport

theorem encodeList_map {α β : Type*} (f : α → β) (enc : β → List Bool) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

end SubexponentialSAT.ExecSparsifyEncoding

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

private theorem normalize_injective : Function.Injective normalizeStacks := by decide
private theorem unary_injective : Function.Injective unaryStacks := by decide

/-- A native positive normalizer changes only the modulus word. -/
theorem normalize_eval (a : Data) (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (hp : 0 < CounterPrograms.value (a.stacks 780)) :
    ∃ n ≤ 9 * (a.stacks 780).length + 21, ∃ b,
      Eval normalize n a b ∧
      b.stacks = Function.update a.stacks 780
        (CounterNormalizeProgram.normalized (a.stacks 780)) := by
  let d := projectState registers normalizeStacks a
  have hd : d = CounterNormalizeProgram.state d.regs (a.stacks 780) [] := by
    apply CounterForPrograms.data_ext (a := d) (b := CounterNormalizeProgram.state d.regs (a.stacks 780) []) rfl
    funext i
    fin_cases i <;> simp [d, projectState, normalizeStacks, CounterNormalizeProgram.state, h0, h1]
  obtain ⟨n, hn, ht⟩ := CounterNormalizeProgram.normalize_runs d.regs (a.stacks 780) hp
  rw [← hd, ← CounterNormalizeProgram.normalized_eq_fixedBits _ hp] at ht
  let out := CounterNormalizeProgram.state CounterNormalizeProgram.zeroRegs
    (CounterNormalizeProgram.normalized (a.stacks 780)) []
  refine ⟨n, hn, embedState registers normalizeStacks a out,
    eval_call_from_state _ _ _ a register_injective normalize_injective ht, ?_⟩
  have hs : out.stacks = Function.update d.stacks 0
      (CounterNormalizeProgram.normalized (a.stacks 780)) := by
    funext i
    fin_cases i <;> simp [out, d, projectState, normalizeStacks, CounterNormalizeProgram.state, h0, h1]
  change Function.extend normalizeStacks out.stacks a.stacks = _
  rw [hs, ProgramLinking.extend_update normalize_injective]
  have hf : Function.extend normalizeStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers normalizeStacks a register_injective normalize_injective)
  rw [hf]
  rfl

/-- The round counter is converted physically; its value, rather than its
binary word length, becomes the number of future rounds. -/
theorem unary_eval (a : Data) (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) :
    ∃ n ≤ CounterConversions.runtimeBound (a.stacks 781), ∃ b,
      Eval unary n a b ∧
      b.stacks = Function.update (Function.update a.stacks 781 []) 0
        (List.replicate (CounterPrograms.value (a.stacks 781)) true) := by
  let d := projectState registers unaryStacks a
  have hd : d = CounterConversions.state d.regs (a.stacks 781) [] := by
    apply CounterForPrograms.data_ext (a := d) (b := CounterConversions.state d.regs (a.stacks 781) []) rfl
    funext i
    fin_cases i <;> simp [d, projectState, unaryStacks, CounterConversions.state, h0, h1]
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs d.regs (a.stacks 781) []
  rw [← hd, List.append_nil] at ht
  let out := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks 781)) true)
  refine ⟨n, hn, embedState registers unaryStacks a out,
    eval_call_from_state _ _ _ a register_injective unary_injective ht, ?_⟩
  have hs : out.stacks = Function.update (Function.update d.stacks 0 []) 1
      (List.replicate (CounterPrograms.value (a.stacks 781)) true) := by
    funext i
    fin_cases i <;> simp [out, d, projectState, unaryStacks, CounterConversions.state, h1]
  change Function.extend unaryStacks out.stacks a.stacks = _
  rw [hs, ProgramLinking.extend_update unary_injective,
    ProgramLinking.extend_update unary_injective]
  have hf : Function.extend unaryStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers unaryStacks a register_injective unary_injective)
  rw [hf]
  rfl

/-- Actual initializer, including every copy, arithmetic microstep, unary
output bit, and return. The enclosing measured preparer supplies the initial
scratch invariant when this local routine is integrated. -/
theorem command_eval (a : Data) (L : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (ht : a.stacks 767 = [])
    (hp : 0 < CounterPrograms.value (a.stacks 768)) :
    ∃ n ≤ 100 * (CounterPrograms.value (a.stacks 774) + 1) * (L + 1), ∃ b,
      Eval command n a b ∧ b.stacks = resultStacks a := by
  have hv : ∀ p ∈ savedRoutes, routeValid p := by
    intro p hp
    simp only [savedRoutes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> unfold routeValid <;> decide
  let a1 := routesState savedRoutes a
  have hcopy := routes_eval savedRoutes hv a ht
  have hcost := routes_cost_bound savedRoutes a L hL
  have hs : a1.stacks = Function.update (Function.update
      (Function.update a.stacks 817 (a.stacks 773)) 780 (a.stacks 768)) 781 (a.stacks 774) := by
    simp [a1, savedRoutes, routesState, routed]
  obtain ⟨u, hu, a2, he2, hs2⟩ := normalize_eval a1
    (by simp [hs, h0]) (by simp [hs, h1]) (by simpa [hs] using hp)
  obtain ⟨v, hv, a3, he3, hs3⟩ := unary_eval a2
    (by simp [hs2, hs, h0]) (by simp [hs2, hs, h1])
  have he4 := Subexp.TupleProgram.transfer_eval (0 : Fin 896) 781 (0 : Fin 40) 1
    (by decide) (by decide) a3
  let b : Data := ⟨readRegs a3.regs 0 1 none, StackRoutines.transferStacks 0 781 a3.stacks⟩
  refine ⟨routesCost savedRoutes a + (u + (v + (3 * (a3.stacks 0).length + 3))),
    ?_, b, hcopy.seq (he2.seq (he3.seq he4)), ?_⟩
  · have hw := hL 768
    have hr := hL 774
    change routesCost savedRoutes a ≤ 3 * (9 * L + 8) + 3 at hcost
    simp only [hs2, hs, Function.update_self, Function.update_of_ne (by decide : (781 : Fin 896) ≠ 780),
      CounterConversions.runtimeBound] at hv
    have hl : (a1.stacks 780).length = (a.stacks 768).length := by simp [hs]
    have hl0 : (a3.stacks 0).length = CounterPrograms.value (a.stacks 774) := by simp [hs3, hs2, hs]
    rw [hl] at hu
    rw [hl0]
    have hprod := Nat.mul_le_mul_left (32 * (CounterPrograms.value (a.stacks 774) + 1)) (Nat.add_le_add_right hr 1)
    nlinarith [Nat.zero_le (CounterPrograms.value (a.stacks 774) * L)]
  · funext i
    by_cases hi0 : i = 0
    · subst i
      simp [b, StackRoutines.transferStacks, resultStacks, h0]
    by_cases hi781 : i = 781
    · subst i
      simp [b, StackRoutines.transferStacks, hs3, hs2, hs, resultStacks]
    by_cases hi780 : i = 780 <;>
      simp [b, StackRoutines.transferStacks, hs3, hs2, hs, resultStacks, hi0, hi781, hi780,
        Function.update_apply]

/-- Saved modulus has the exact canonical width used in the fixed-square
candidate-count estimate, even if the arithmetic preparer emitted padding. -/
theorem result_modulus {m : ℕ} (a : Data) (hm : 0 < m)
    (hv : CounterPrograms.value (a.stacks 768) = 3 * m) :
    CounterPrograms.value (resultStacks a 780) = 3 * m ∧
      (resultStacks a 780).length = HashCandidates.digitWidth m := by
  have hp : 0 < CounterPrograms.value (a.stacks 768) := by omega
  simp [resultStacks, CounterNormalizeProgram.normalized_value _ hp,
    CounterNormalizeProgram.normalized_length, hv, HashCandidates.digitWidth,
    DyadicWidth.width, Nat.log2_eq_log_two]

end Initialize

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
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

theorem canonicalRowWidth_eval (a : Data) (hs : a.stacks 767 = []) :
    Eval canonicalRowWidth (canonicalRowSteps a) a (canonicalRowState a) := by
  have h1 := route_eval (780, 768) (by unfold routeValid; decide) a hs
  have h2 := route_eval (780, 783) (by unfold routeValid; decide) (routed (780, 768) a)
    (by simpa [routed] using hs)
  convert h1.seq h2 using 1
  · rfl
  · simp [canonicalRowSteps, routeCost, routed]
    omega
  · rfl

theorem canonicalRowState_modulus (a : Data) :
    (canonicalRowState a).stacks 768 = a.stacks 780 := by
  simp [canonicalRowState, routed]

theorem canonicalRowState_width (a : Data) :
    (canonicalRowState a).stacks 783 = a.stacks 780 := by
  simp [canonicalRowState, routed]

theorem canonicalRowState_frame (a : Data) (i : Fin 896) (h768 : i ≠ 768)
    (h783 : i ≠ 783) : (canonicalRowState a).stacks i = a.stacks i := by
  simp [canonicalRowState, routed, h768, h783]

theorem canonicalRowState_bound (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((canonicalRowState a).stacks i).length ≤ B := by
  intro i
  by_cases h768 : i = 768
  · subst i; simpa [canonicalRowState_modulus] using ha 780
  by_cases h783 : i = 783
  · subst i; simpa [canonicalRowState_width] using ha 780
  rw [canonicalRowState_frame a i h768 h783]
  exact ha i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupBoundSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured bounds for composition of the concrete setup phases

The predicates below retain actual executions. Polynomial coefficients and
degrees are chosen before the input size and the incoming machine state.
-/

namespace SubexponentialSAT.SubexpSetupBoundSpec

open BitProgram StructuredCalls SubexpSetupStorage Filter

theorem wordBound_mono {r s B C : ℕ} {a : State r s}
    (ha : WordBound B a) (hBC : B ≤ C) : WordBound C a :=
  fun i => (ha i).trans hBC

/-- A fixed stack gains at most one bit per actual instruction. -/
theorem eval_wordBound {r s B t : ℕ} {cmd : Cmd r s} {a b : State r s}
    (ha : WordBound B a) (he : Eval cmd t a b) : WordBound (B + t) b := by
  intro i
  have hg := BitProgram.trace_selectedStackBits (compiled cmd i i) {i}
    (compiled_trace he i i)
  have hi : (b.stacks i).length ≤ (a.stacks i).length + t := by
    simpa only [BitProgram.selectedStackBits, Finset.sum_singleton,
      StructuredProgram.State.withPC] using hg
  exact hi.trans (Nat.add_le_add_right (ha i) t)

end SubexponentialSAT.SubexpSetupBoundSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual loaded-leaf startup and canonical saved selector parameters. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- This concrete stage preserves all caller words except its five named
outputs. Unary round production is charged by the actual round value. -/
theorem saveCanonical_eval (a : Data) {n m B L : ℕ} (hm : 0 < m)
    (he : WorkerEmpty a) (hL : ∀ i, (a.stacks i).length ≤ L)
    (hc : BinaryArithmetic.toNat (a.stacks 768) = 3 * m)
    (hd : BinaryArithmetic.toNat (a.stacks 773) = SparseCode.distanceDenom m B)
    (hr : BinaryArithmetic.toNat (a.stacks 774) = HashSelect.loopCap n m) :
    ∃ steps b, steps ≤ saveCanonicalTime n m L ∧ Eval saveCanonical steps a b ∧
      WorkerEmpty b ∧ b.stacks 768 = b.stacks 780 ∧ b.stacks 783 = b.stacks 780 ∧
      BinaryArithmetic.toNat (b.stacks 780) = 3 * m ∧
      (b.stacks 780).length = HashCandidates.digitWidth m ∧
      BinaryArithmetic.toNat (b.stacks 817) = SparseCode.distanceDenom m B ∧
      b.stacks 781 = List.replicate (HashSelect.loopCap n m) true ∧
      (∀ i : Fin 896, i ≠ 768 → i ≠ 780 → i ≠ 781 → i ≠ 783 → i ≠ 817 →
        b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ L + saveCanonicalTime n m L) := by
  have hc' : CounterPrograms.value (a.stacks 768) = 3 * m := by
    rw [CounterPrograms.value_eq_toNat]; exact hc
  obtain ⟨ni, hni, c, hi, hs⟩ := HashGreedyProgram.Initialize.command_eval a L hL
    (he 0) (he 1) (he 767) (by omega)
  rw [CounterPrograms.value_eq_toNat, hr] at hni
  let I := 100 * (HashSelect.loopCap n m + 1) * (L + 1)
  have hcb : ∀ i, (c.stacks i).length ≤ L + I :=
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound hL hi)
      (Nat.add_le_add_left hni L)
  have hcf (i : Fin 896) (h780 : i ≠ 780) (h781 : i ≠ 781) (h817 : i ≠ 817) :
      c.stacks i = a.stacks i := by
    simp [hs, HashGreedyProgram.Initialize.resultStacks, h780, h781, h817]
  have hc767 : c.stacks 767 = [] := (hcf 767 (by decide) (by decide) (by decide)).trans (he 767)
  have hrow := NativeLeaf.canonicalRowWidth_eval c hc767
  let b := NativeLeaf.canonicalRowState c
  have hframe (i : Fin 896) (h768 : i ≠ 768) (h780 : i ≠ 780)
      (h781 : i ≠ 781) (h783 : i ≠ 783) (h817 : i ≠ 817) :
      b.stacks i = a.stacks i :=
    (NativeLeaf.canonicalRowState_frame c i h768 h783).trans (hcf i h780 h781 h817)
  have htime : NativeLeaf.canonicalRowSteps c ≤ 18 * (L + I) + 16 := by
    have h1 := hcb 768
    have h2 := hcb 783
    have h3 := hcb 780
    dsimp [NativeLeaf.canonicalRowSteps]
    omega
  have hmod : BinaryArithmetic.toNat (c.stacks 780) = 3 * m ∧
      (c.stacks 780).length = HashCandidates.digitWidth m := by
    simpa only [hs, CounterPrograms.value_eq_toNat] using
      HashGreedyProgram.Initialize.result_modulus a hm hc'
  refine ⟨ni + NativeLeaf.canonicalRowSteps c, b, ?_, hi.seq hrow, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hframe, ?_⟩
  · dsimp only [saveCanonicalTime]
    dsimp only [I] at htime
    omega
  · intro i
    have hn (j : Fin 896) (hj : 768 ≤ j.val) : workerStack i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [workerStack, Fin.val_castAdd] at hv
      have := i.isLt
      omega
    exact (hframe _ (hn 768 (by decide)) (hn 780 (by decide)) (hn 781 (by decide))
      (hn 783 (by decide)) (hn 817 (by decide))).trans (he i)
  · exact (NativeLeaf.canonicalRowState_modulus c).trans
      (NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)).symm
  · exact (NativeLeaf.canonicalRowState_width c).trans
      (NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)).symm
  · rw [NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)]
    exact hmod.1
  · rw [NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)]
    exact hmod.2
  · rw [NativeLeaf.canonicalRowState_frame c 817 (by decide) (by decide)]
    simpa [hs, HashGreedyProgram.Initialize.resultStacks] using hd
  · rw [NativeLeaf.canonicalRowState_frame c 781 (by decide) (by decide)]
    simp [hs, HashGreedyProgram.Initialize.resultStacks, CounterPrograms.value_eq_toNat, hr]
  · intro i
    apply (NativeLeaf.canonicalRowState_bound c (L + I) hcb i).trans
    dsimp [saveCanonicalTime, I]
    omega

/-- Same-run startup, canonical width and saved round/depth parameters.
All 896 stacks are bounded at every prefix, including padded caller words. -/
theorem canonicalStart_eval (a : Data) {n B W : ℕ} (records : List (List Bool))
    (hW : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
    (hformula : a.stacks 784 = Encoding.encodeList id records) (hm : records ≠ [])
    (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
    (hB : BinaryArithmetic.toNat (a.stacks 786) = B) :
    ∃ steps b, steps ≤ canonicalStartTime n records.length W ∧
      Eval canonicalStart steps a b ∧ WorkerEmpty b ∧
      b.stacks 768 = b.stacks 780 ∧ b.stacks 783 = b.stacks 780 ∧
      BinaryArithmetic.toNat (b.stacks 780) = 3 * records.length ∧
      (b.stacks 780).length = HashCandidates.digitWidth records.length ∧
      BinaryArithmetic.toNat (b.stacks 817) = SparseCode.distanceDenom records.length B ∧
      b.stacks 781 = List.replicate (HashSelect.loopCap n records.length) true ∧
      BinaryArithmetic.toNat (b.stacks 782) = records.length ∧
      (∀ i : Fin 896, 784 ≤ i.val → i ≠ 817 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ W + canonicalStartTime n records.length W) ∧
      Trace (compiled canonicalStart 784 788) (steps + 1)
        (a.withPC (some (compiled canonicalStart 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled canonicalStart 784 788) k
        (a.withPC (some (compiled canonicalStart 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ W + canonicalStartTime n records.length W + 1 := by
  obtain ⟨ns, s, _, hns, hes, hs, hsf, hsb, _, _⟩ :=
    start_trace_space a W records hW hempty hformula hm
  rw [hn, hB] at hs
  let S := CodeSetupOuterCost.startupConstant * (W + 1) ^ 4
  have hsb' : ∀ i, (s.stacks i).length ≤ W + S := by
    exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound hW hes) (Nat.add_le_add_left hns W)
  obtain ⟨nc, b, hnc, hec, hbempty, hwidth, h783, hmod, hmodlen, hdepth, hrounds, hcf, hcb⟩ :=
    saveCanonical_eval s (List.length_pos_iff.mpr hm) hs.worker hsb' hs.count hs.depth hs.rounds
  have heval : Eval canonicalStart (ns + nc) a b := hes.seq hec
  have ht := Nat.add_le_add hns hnc
  change ns + nc ≤ canonicalStartTime n records.length W at ht
  refine ⟨ns + nc, b, ht, heval, hbempty, hwidth, h783, hmod, hmodlen, hdepth, hrounds,
    ?_, ?_, ?_, compiled_halt_trace heval 784 788, ?_⟩
  · rw [hcf 782 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.clauses
  · intro i hi hi817
    have hne (j : Fin 896) (hj : j.val < 784) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    exact (hcf i (hne 768 (by decide)) (hne 780 (by decide)) (hne 781 (by decide))
      (hne 783 (by decide)) hi817).trans (hsf i hi)
  · intro i
    have hb := hcb i
    dsimp only [canonicalStartTime, S] at hb ⊢
    omega
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hW i
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
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

/-- From the actually loaded nonterminal formula, the native preparation
produces the selector's physical entry state and its attained initial code.
The same execution carries the time and every-prefix all-stack bounds.
The retained bound is independent of the exponential search runtime. -/
theorem command_eval (a : Data) {n B W : ℕ} (records : List (List Bool))
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (he : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
    (hformula : a.stacks 784 = Encoding.encodeList id records)
    (hm : records ≠ []) (hB : 0 < B)
    (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B) :
    ∃ (steps : ℕ) (started prepared out : Data)
      (shifts : SparseCode.SuppliedShifts records.length B)
      (Q : SparseCode.SuppliedLocal records.length B),
      let L := W + NativeLeafSetup.canonicalStartTime n records.length W
      steps ≤ NativeLeafSetup.canonicalStartTime n records.length W +
        continuationTime records.length B L started prepared ∧
      Eval command steps a out ∧
      (∀ i, (started.stacks i).length ≤ L) ∧
      BinaryArithmetic.toNat (started.stacks 782) = records.length ∧
      BinaryArithmetic.toNat (started.stacks 768) = 3 * records.length ∧
      Metadata records.length B prepared ∧
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime records.length B L
        (started.stacks 782).length (started.stacks 786).length) ∧
      Ready n records.length B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom records.length B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree records.length B /
        (100 * B * SparseCode.logSize records.length) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ retainedBound records.length B L started prepared) ∧
      ∀ k c, k ≤ steps → Trace (compiled command 784 788) k
        (a.withPC (some (compiled command 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (L + 1) (continuationSpace records.length B L started prepared) := by
  obtain ⟨ns,s,hns,hes,hse,hw,h783,hmod,hml,hd,hr,hmc,hsf,hsb,_hst,hss⟩ :=
    NativeLeafSetup.canonicalStart_eval a records ha he hformula hm hn hBword
  have hsB : BinaryArithmetic.toNat (s.stacks 786) = B := by
    rw [hsf 786 (by decide) (by decide)]
    exact hBword
  obtain ⟨nc,p,out,shifts,Q,hnc,hec,hmeta,hp,hready,hgood,hdist,hframe,hbound,hspace⟩ :=
    afterCanonical_eval s (List.length_pos_iff.mpr hm) hB hse hsb hmc hsB hw hmod hml h783 hd hr
  change nc ≤ continuationTime records.length B
    (W + NativeLeafSetup.canonicalStartTime n records.length W) s p at hnc
  refine ⟨ns+nc,s,p,out,shifts,Q,Nat.add_le_add hns hnc,hes.seq hec,hsb,hmc,
    hw ▸ hmod,hmeta,hp,hready,hgood,hdist,?_,hbound,?_⟩
  · intro i hi hregion
    rw [hframe i hi hregion]
    apply hsf i hi
    intro heq
    subst i
    change 817 < 800 ∨ 818 < 817 at hregion
    omega
  · exact StructuredSpace.sequence_stack_bound hes hec 784 788
      (fun k c hk ht i => (hss k c (Nat.le_succ_of_le hk) ht i).trans (Nat.le_max_left _ _))
      (fun k c hk ht i => (hspace k c hk ht i).trans (Nat.le_max_right _ _))
      (compiled command 784 788) (siteAddress command) (exitAddress command)
      (compiled_site command 784 788)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

theorem clauseRecords_body {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    Encoding.encodeList id (clauseRecords F) = ExecQuantitativeSparsify.encodeRawFormula F := by
  simp only [clauseRecords, ExecQuantitativeSparsify.encodeRawFormula,
    ExecSparsifyEncoding.encodeList_map]
  rfl


open DisjointReuse.DFSVisit

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
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

/-- The first query really starts with the upper query work banks empty.
The premise is the literal frame returned by preparation and the actual
cleared input bank; readiness alone is deliberately not used for this fact. -/
theorem prepared_query_workspace (a prepared : State 40 896)
    (hframe : ∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
      prepared.stacks i = a.stacks i)
    (ha : ∀ i : Fin 896, 788 ≤ i.val → a.stacks i = []) :
    ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
      prepared.stacks i = [] := by
  intro i hi
  rw [hframe i (by omega) (by omega)]
  exact ha i (by omega)

/-- Instantiate preparation on the exact raw DFS body. This exposes both
produced matrices and the actual blank first-query workspace from the loaded
three-word input, without a successful-code or layout premise. -/
theorem prepare_raw_oai {n B W : ℕ} (F : DisjointReuse.RawCNF n) (a : State 40 896)
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → a.stacks i = [])
    (hformula : a.stacks 784 = DisjointReuse.SparseCountProgram.encodeBody F)
    (hm : F ≠ []) (hB : 0 < B)
    (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B) :
    ∃ (steps : ℕ) (started prepared out : State 40 896)
      (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B),
      let L := W + NativeLeafSetup.canonicalStartTime n F.length W
      steps ≤ NativeLeafSetup.canonicalStartTime n F.length W +
        NativeLeafPreparation.continuationTime F.length B L started prepared ∧
      Eval NativeLeafPreparation.command steps a out ∧
      (∀ i, (started.stacks i).length ≤ L) ∧
      BinaryArithmetic.toNat (started.stacks 782) = F.length ∧
      BinaryArithmetic.toNat (started.stacks 768) = 3 * F.length ∧
      LeafOuterProgram.Metadata F.length B prepared ∧
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime F.length B L
        (started.stacks 782).length (started.stacks 786).length) ∧
      NativeLeafPreparation.Ready n F.length B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom F.length B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree F.length B /
        (100 * B * SparseCode.logSize F.length) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) → out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ NativeLeafPreparation.retainedBound F.length B L started prepared) ∧
      (∀ k c, k ≤ steps → Trace (compiled NativeLeafPreparation.command 784 788) k
        (a.withPC (some (compiled NativeLeafPreparation.command 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (L + 1)
          (NativeLeafPreparation.continuationSpace F.length B L started prepared)) ∧
      ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        out.stacks i = [] := by
  generalize hlenF : F.length = m
  have hlenRecords : (NativeTerminal.clauseRecords F).length = m := by
    simpa only [NativeTerminal.clauseRecords, List.length_map] using hlenF
  rw [← hlenRecords]
  have hlo : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [] := by
    intro i hi
    have hne (j : Fin 896) (hj : 782 < j.val) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    exact hempty i (hne 784 (by decide)) (hne 785 (by decide)) (hne 786 (by decide))
  have hencoded : a.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) :=
    hformula.trans (NativeTerminal.clauseRecords_body F).symm
  have hnonnil : NativeTerminal.clauseRecords F ≠ [] := by
    intro hz
    apply hm
    apply List.eq_nil_of_length_eq_zero
    have hlen := congrArg List.length hz
    simpa [NativeTerminal.clauseRecords] using hlen
  have h := NativeLeafPreparation.command_eval a (NativeTerminal.clauseRecords F)
    ha hlo hencoded hnonnil hB hn hBword
  obtain ⟨steps,started,prepared,out,shifts,Q,ht,he,hs,h782,h768,hmeta,hp,hr,hgood,hdist,
    hframe,hbound,hprefix⟩ := h
  refine ⟨steps,started,prepared,out,shifts,Q,ht,he,hs,h782,h768,hmeta,hp,hr,hgood,hdist,
    hframe,hbound,hprefix,prepared_query_workspace a out hframe ?_⟩
  intro i hi
  have hne (j : Fin 896) (hj : j.val < 788) : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact hempty i (hne 784 (by decide)) (hne 785 (by decide)) (hne 786 (by decide))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw_oai
