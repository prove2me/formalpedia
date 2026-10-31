-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:17:05.094293+00:00
-- url     : https://prove2.me/submissions/dada9f0f-21fc-4de1-8e91-57385247ad56

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_rowCommand_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_boundary_after_body
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_prepareKey_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_visits_exists
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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

end SubexponentialSAT.CounterNormalizeProgram

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

theorem trace_prefix_bound_cons {α : Type*} {step : α → Option α}
    {a b : α} {steps : ℕ} {P : α → Prop}
    (hs : step a = some b) (ha : P a)
    (htail : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle hp
  cases hp with
  | refl => exact ha
  | cons hs' ht =>
      have heq := Option.some.inj (hs.symm.trans hs')
      subst b
      exact htail _ _ (by omega) ht


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

/-- A loop induction combines its current body and remaining iterations by
maximum space; the number of completed iterations never multiplies the bound. -/
theorem while_true_stack_bound {r s L : ℕ} {body : StructuredCalls.Cmd r s}
    {test : Fin r} {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (htest : a.regs test = true)
    (hb : StructuredCalls.Eval body n a b)
    (hw : StructuredCalls.Eval (.while test body) m b c)
    (inputStack outputStack : Fin s)
    (hbody : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled body inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled body inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hwhile : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled (.while test body) inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled (.while test body) inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := n + m)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry body (embed ∘ some) (embed none)))) ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hbody 0 _ (Nat.zero_le n) (.refl _)
  · exact trace_prefix_bound_trans
      (StructuredCalls.eval_trace hb caller (embed ∘ some) (embed none)
        (fun q => hcode (some q)))
      (command_stack_bound hb inputStack outputStack hbody caller (embed ∘ some)
        (embed none) (fun q => hcode (some q)))
      (command_stack_bound hw inputStack outputStack hwhile caller embed exit hcode)

theorem while_false_stack_bound {r s L : ℕ} (body : StructuredCalls.Cmd r s)
    (test : Fin r) {bound : ℕ} (a : StructuredCalls.State r s)
    (htest : a.regs test = false) (hstart : ∀ i, (a.stacks i).length ≤ bound)
    (caller : Program r s L)
    (embed : StructuredCalls.Site (.while test body) → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.while test body) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.while test body) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := 0)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some exit)) ?_ hstart ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · intro prefixSteps intermediate hle hp
    have hz : prefixSteps = 0 := by omega
    subst prefixSteps
    cases hp
    exact hstart

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Enumerators
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators

open BitProgram StructuredCalls ExecCNFTupleEnumeration

/-- The binary countdown controller also retains a uniform stack bound for
arbitrarily many callbacks. Counter width is measured, never its numeric value. -/
theorem countdown_visits_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) (I J : StructuredCalls.State R S → Prop)
    (boundaryBound callbackBound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hmiddle : ∀ a, J a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hcallback : ∀ a b nb, Eval body nb a b → I a →
      a.regs (p.register 2) = true → 0 < CounterPrograms.value (a.stacks p.counter) →
      J b ∧ ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled body p.counter p.counter) prefixSteps
          (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    (hnext : ∀ a, J a → 0 < CounterPrograms.value (a.stacks p.counter) →
      I (CounterForPrograms.nextState p a))
    {costs : List ℕ} {steps : ℕ} {a b : StructuredCalls.State R S}
    (hvis : CounterForPrograms.Visits p body costs steps a b) (hI : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter) prefixSteps
        (a.withPC
          (some (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤
          max callbackBound (S * boundaryBound + 16 * boundaryBound + 16) := by
  let bound := max callbackBound (S * boundaryBound + 16 * boundaryBound + 16)
  have hboundary : boundaryBound ≤ bound := by
    have hS : 1 ≤ S := by have := p.counter.isLt; omega
    have hmul : boundaryBound ≤ S * boundaryBound := by
      simpa using Nat.mul_le_mul_right boundaryBound hS
    exact hmul.trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_max_right _ _)))
  induction hvis with
  | done a hf hz =>
      exact StructuredSpace.while_false_stack_bound _ _ a hf
        (fun i => (hinitial a hI i).trans hboundary)
        _ _ _ (compiled_site _ p.counter p.counter)
  | @step a middle b nb nt costs hf hp hb hc hs tail ih =>
      obtain ⟨hmid, hbody⟩ := hcallback a middle nb hb hI hf hp
      have hpositive : 0 < CounterPrograms.value (middle.stacks p.counter) := by
        simpa only [hc] using hp
      have hafter := hnext middle hmid hpositive
      have ha := CounterForPrograms.advance_eval p middle hs
      have hcost := CounterForPrograms.advanceCost_le p middle hpositive
      have hwidth := hmiddle middle hmid p.counter
      have hcontrol : ∀ prefixSteps intermediate,
          prefixSteps ≤ CounterForPrograms.advanceCost p middle →
          Trace (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter) prefixSteps
            (middle.withPC
              (some (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        have hb' : dataBits (middle.withPC
            (some (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter).entry)) ≤
            S * boundaryBound := StreamResources.dataBits_le_mul _ (hmiddle middle hmid)
        have h := StructuredSpace.local_stack_bound
          (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter)
          (steps := 16 * boundaryBound + 16) hb' prefixSteps intermediate
          (by omega) htrace i
        exact h.trans (by
          simpa only [bound, Nat.add_assoc] using
            (Nat.le_max_right callbackBound (S * boundaryBound + 16 * boundaryBound + 16)))
      have hcallbackBound : ∀ prefixSteps intermediate, prefixSteps ≤ nb →
          Trace (compiled body p.counter p.counter) prefixSteps
            (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        exact (hbody prefixSteps intermediate hle htrace i).trans (Nat.le_max_left _ _)
      have hsequence := StructuredSpace.sequence_stack_bound hb ha p.counter p.counter
        hcallbackBound hcontrol
        (compiled (.seq body (CounterForPrograms.advanceCmd p)) p.counter p.counter)
        (siteAddress (.seq body (CounterForPrograms.advanceCmd p)))
        (exitAddress (.seq body (CounterForPrograms.advanceCmd p)))
        (compiled_site _ p.counter p.counter)
      exact StructuredSpace.while_true_stack_bound hf (.seq hb ha) tail.eval
        p.counter p.counter hsequence (ih hafter)
        _ _ _ (compiled_site _ p.counter p.counter)

/-- The initial zero test and final halt are included in the counted loop's
prefix bound. The test scans only the current bounded-length counter word. -/
theorem countdown_for_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) {costs : List ℕ} {steps loopBound boundaryBound : ℕ}
    {a b : StructuredCalls.State R S} (hs : a.stacks p.scratch = [])
    (hinitial : ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hvis : CounterForPrograms.Visits p body costs steps (CounterForPrograms.testResult p a) b)
    (hloop : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter) prefixSteps
        ((CounterForPrograms.testResult p a).withPC
          (some (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ loopBound) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ 8 * (a.stacks p.counter).length + 7 + steps + 1 →
      Trace (CounterForPrograms.program p body p.counter p.counter) prefixSteps
        (a.withPC (some (CounterForPrograms.program p body p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤
          max loopBound (S * boundaryBound + 8 * boundaryBound + 7) := by
  let bound := max loopBound (S * boundaryBound + 8 * boundaryBound + 7)
  have htest := CounterForPrograms.test_eval p a hs
  have hprefix : ∀ prefixSteps intermediate,
      prefixSteps ≤ 8 * (a.stacks p.counter).length + 7 →
      Trace (compiled (CounterForPrograms.testCmd p) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (CounterForPrograms.testCmd p) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have hb : dataBits (a.withPC
        (some (compiled (CounterForPrograms.testCmd p) p.counter p.counter).entry)) ≤
        S * boundaryBound := StreamResources.dataBits_le_mul _ hinitial
    have hc := hinitial p.counter
    have h := StructuredSpace.local_stack_bound
      (compiled (CounterForPrograms.testCmd p) p.counter p.counter)
      (steps := 8 * boundaryBound + 7) hb prefixSteps intermediate (by omega) htrace i
    exact h.trans (by
      simpa only [bound, Nat.add_assoc] using
        (Nat.le_max_right loopBound (S * boundaryBound + 8 * boundaryBound + 7)))
  have hloop' : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter) prefixSteps
        ((CounterForPrograms.testResult p a).withPC
          (some (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    exact (hloop prefixSteps intermediate hle htrace i).trans (Nat.le_max_left _ _)
  have hseq := StructuredSpace.sequence_stack_bound htest hvis.eval p.counter p.counter
    hprefix hloop' (CounterForPrograms.program p body p.counter p.counter)
    (siteAddress (CounterForPrograms.forCmd p body))
    (exitAddress (CounterForPrograms.forCmd p body)) (compiled_site _ p.counter p.counter)
  exact StructuredSpace.compiled_halt_stack_bound (.seq htest hvis.eval)
    p.counter p.counter hseq


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial bounds for the physical integer-signature scan. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem words_length_bound (xs : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈xs,x.length ≤ B) : (words xs).length ≤ xs.length*(2*B+1) := by
  induction xs with
  | nil => simp [words]
  | cons x xs ih =>
      have hx := hb x (by simp)
      have ht := ih (fun y hy => hb y (by simp [hy]))
      simp only [words,List.length_append,Encoding.length_frame,List.length_cons]
      nlinarith

theorem sum_lengths_bound (xs : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈xs,x.length ≤ B) : (xs.map List.length).sum ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hb x (by simp)
      have ht := ih (fun y hy => hb y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

theorem rowWidth_bound (W : List Bool) (xs : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈xs,x.length ≤ B) : rowWidth W xs [true] ≤ widthBound W xs.length B := by
  have hs := sum_lengths_bound xs B hb
  simp only [rowWidth,List.length_singleton,widthBound]
  nlinarith

theorem rowKey_length_bound (W bits : List Bool) (row : List (List Bool))
    (hl : row.length=bits.length) :
    (rowKey W bits row).length ≤ rowWidth W row [true]+1 := by
  obtain ⟨t,ht,rf,out,he,hv,hlen⟩ := rowCommand_eval (fun _ => false) W row bits [true] hl
  have hv' : SubexponentialSAT.BinaryArithmetic.toNat out = 1+rowValue W row bits := by
    simpa [SubexponentialSAT.BinaryArithmetic.toNat] using hv
  have hp : 0 < SubexponentialSAT.CounterPrograms.value out := by
    rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hv']; omega
  have hn := SubexponentialSAT.CounterNormalizeProgram.normalized_eq_fixedBits out hp
  have htrim := SubexponentialSAT.SubexpParameterProgram.trimTail_length_le out.reverse
  have heq : rowKey W bits row = SubexponentialSAT.CounterNormalizeProgram.normalized out := by
    rw [hn]
    simp only [rowKey,canonical,SubexponentialSAT.CounterPrograms.value_eq_toNat,hv']
  rw [heq]
  simp only [SubexponentialSAT.CounterNormalizeProgram.normalized,List.length_reverse,List.length_cons]
  simp only [List.length_reverse] at htrim
  omega

theorem canonicalRowBudget_bound (W : List Bool) (row : List (List Bool)) (B : ℕ)
    (hb : ∀ x∈row,x.length ≤ B) : canonicalRowBudget W row ≤ rowCostBound W row.length B := by
  have hw := rowWidth_bound W row B hb
  unfold canonicalRowBudget rowBudget rowCostBound
  gcongr

theorem signatureStepCost_bound (W bits : List Bool) (row : List (List Bool)) (B : ℕ)
    (hl : row.length=bits.length) (hb : ∀ x∈row,x.length ≤ B) :
    signatureStepCost W bits row ≤ signatureRowBound W bits.length B := by
  have hw := rowWidth_bound W row B hb
  have hk := (rowKey_length_bound W bits row hl).trans (Nat.add_le_add_right hw 1)
  have hr := canonicalRowBudget_bound W row B hb
  have he := words_length_bound row B hb
  rw [hl] at hk hr he
  unfold signatureStepCost signatureRowBound
  omega

theorem signatureCost_bound (W bits : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hl : ∀ row∈rows,row.length=bits.length)
    (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) :
    signatureCost W bits rows ≤ rows.length*(signatureRowBound W bits.length B+2)+1 := by
  unfold signatureCost
  suffices hs : (List.map (fun row => signatureStepCost W bits row+2) rows).sum ≤
      rows.length*(signatureRowBound W bits.length B+2) by omega
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hx := signatureStepCost_bound W bits row B (hl row (by simp)) (hb row (by simp))
      have ht := ih (fun r hr => hl r (by simp [hr])) (fun r hr => hb r (by simp [hr]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem cost_le (W bits : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = bits.length)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) :
    cost W bits rows ≤ 7 * (words (rows.map words)).length +
      rows.length * (signatureRowBound W bits.length B + 2) + 8 := by
  have hs := signatureCost_bound W bits rows B hlen hwidth
  dsimp [cost]
  omega

namespace Rescan

theorem clear_eval (i : Fin 24) (a : Data) :
    Eval (clear i) (2 * (a.stacks i).length + 3) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks i a.stacks⟩ :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem copy_eval (i j : Fin 24) (a : Data)
    (hij : i ≠ j) (hi : i ≠ 21) (hj : (21 : Fin 24) ≠ j)
    (ht : a.stacks 21 = []) :
    Eval (copy i j) (7 * (a.stacks i).length + 5) a
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks i j a.stacks⟩ :=
  .call _ (ListRegisterProgram.copy_run i j 21 0 1 hij hi hj (by decide)
    a.regs a.stacks ht)

theorem storeFresh_eval (b : Bool) (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) (bits key : List Bool) :
    ∃ out, Eval (storeFresh b) 7
      (workState regs W rows candidate saved predecessor fuel fresh bits key)
      (workState out W rows candidate saved predecessor fuel b bits key) := by
  let a := workState regs W rows candidate saved predecessor fuel fresh bits key
  let c : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 22 a.stacks⟩
  let d := (StructuredProgram.Atom.set (0 : Fin 16) b).eval c
  let e := (StructuredProgram.Atom.push (22 : Fin 24) (0 : Fin 16)).eval d
  have hc : Eval (clear 22) 5 a c := clear_eval 22 a
  have he : Eval (.base (.seq (.atom (.set 0 b)) (.atom (.push 22 0)))) 2 c e :=
    .base ((StructuredProgram.Eval.atom _ c).seq (StructuredProgram.Eval.atom _ d))
  have hf : e = workState e.regs W rows candidate saved predecessor fuel b bits key := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [d, c, a, workState, StackRoutines.clearStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  refine ⟨e.regs, ?_⟩
  have ht := hc.seq he
  rw [hf] at ht
  exact ht

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem workState_fuel_update (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel newFuel : List Bool)
    (fresh : Bool) :
    (workState regs W rows candidate saved predecessor newFuel fresh [] []).stacks =
      Function.update (workState regs W rows candidate saved predecessor fuel fresh [] []).stacks
        19 newFuel := by
  funext i
  fin_cases i <;> simp [workState]

theorem nextState_workState (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) :
    CounterForPrograms.nextState countdownPorts
      (workState regs W rows candidate saved predecessor fuel fresh [] []) =
      workState (CounterForPrograms.nextState countdownPorts
        (workState regs W rows candidate saved predecessor fuel fresh [] [])).regs
        W rows candidate saved predecessor (CounterPrograms.ripple false fuel) fresh [] [] := by
  let a := workState regs W rows candidate saved predecessor fuel fresh [] []
  have hs : (CounterForPrograms.nextState countdownPorts a).stacks =
      Function.update a.stacks 19 (CounterPrograms.ripple false fuel) := by
    funext i
    by_cases hc : i = 19
    · subst i
      rw [Function.update_self]
      exact CounterForPrograms.nextState_counter countdownPorts a
    rw [Function.update_of_ne hc]
    by_cases he : i = 20
    · subst i
      exact CounterForPrograms.nextState_scratch countdownPorts a
    exact (CounterForPrograms.nextState_outside countdownPorts a i hc he).symm
  apply congrArg (StructuredProgram.State.mk _)
  exact hs.trans (workState_fuel_update _ W rows candidate saved predecessor fuel _ fresh).symm

theorem for_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) :
    ∃ n ≤ candidate.val *
        (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) + 8 * h + 8,
      ∃ out, Eval (CounterForPrograms.forCmd countdownPorts body) n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
          (List.replicate h false)
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  let a := workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []
  let t := CounterForPrograms.testResult countdownPorts a
  have ht : t = workState t.regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
      (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [] := by
    apply congrArg (StructuredProgram.State.mk t.regs)
    exact CounterForPrograms.testResult_stacks countdownPorts a rfl
  have hf : t.regs 15 = !(CounterPrograms.isZero (ExecCNFTupleEnumeration.fixedBits h candidate)) :=
    CounterForPrograms.testResult_flag countdownPorts a
  obtain ⟨costs, ns, out, hv, hc⟩ := visits_exists W rows h B hlen hwidth candidate candidate.val
    0 (ExecCNFTupleEnumeration.fixedBits h candidate) t.regs (by omega) (by simp)
    (ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt) hf
  simp only [AttainedSignatures.duplicateScan, Bool.not_false] at hv
  rw [← ht] at hv
  have htest := CounterForPrograms.test_eval countdownPorts a (by rfl)
  have hrun := htest.seq hv.eval
  obtain ⟨hcount, _, _, htime⟩ := hv.bounds
  have hlen' : (t.stacks countdownPorts.counter).length = h := by
    rw [ht]
    simp [workState, countdownPorts]
  have hval : CounterPrograms.value (t.stacks countdownPorts.counter) = candidate.val := by
    rw [ht]
    exact ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt
  rw [hval] at hcount
  rw [hlen', hcount] at htime
  refine ⟨_, ?_, out, hrun⟩
  change 8 * (ExecCNFTupleEnumeration.fixedBits h candidate).length + 7 + ns ≤ _
  rw [ExecCNFTupleEnumeration.fixedBits_length]
  nlinarith

/-- All live arrays and all four retained words are included. -/
theorem workState_stackBits (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor fuel : List Bool)
    (fresh : Bool) :
    stackBits (workState regs W rows candidate saved predecessor fuel fresh [] []).stacks =
      W.length + (words (rows.map words)).length + candidate.length + saved.length +
        predecessor.length + fuel.length + 1 := by
  simp [stackBits, workState, Fin.sum_univ_succ, Nat.add_assoc]

theorem boundary_stackBits (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h c i : ℕ) (fuel : List Bool)
    (hf : fuel.length = h) (fresh : Bool) :
    stackBits (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h c)
      (naturalKey W rows h c) (ExecCNFTupleEnumeration.fixedBits h i) fuel fresh [] []).stacks =
      boundaryBound W (naturalKey W rows h c) rows h := by
  rw [workState_stackBits]
  simp only [ExecCNFTupleEnumeration.fixedBits_length, hf, boundaryBound]
  omega

theorem Boundary.stackBits {W : List Bool} {rows : List (List (List Bool))}
    {h c phase : ℕ} {a : Data} (ha : Boundary W rows h c phase a) :
    stackBits a.stacks = boundaryBound W (naturalKey W rows h c) rows h := by
  obtain ⟨i, fuel, fresh, _, _, hf, he⟩ := ha
  rw [he]
  exact boundary_stackBits a.regs W rows h c i fuel hf fresh

theorem boundary_next (W : List Bool) (rows : List (List (List Bool)))
    (h c : ℕ) {a : Data} (ha : Boundary W rows h c 1 a)
    (hp : 0 < CounterPrograms.value (a.stacks countdownPorts.counter)) :
    Boundary W rows h c 0 (CounterForPrograms.nextState countdownPorts a) := by
  obtain ⟨i, fuel, fresh, hi, hv, hl, he⟩ := ha
  have hp' : 0 < CounterPrograms.value fuel := by
    rw [he] at hp
    exact hp
  have hd := CounterPrograms.value_decrement hp'
  refine ⟨i, CounterPrograms.ripple false fuel, fresh, hi, by omega,
    (CounterPrograms.decrement_length hp').trans hl, ?_⟩
  rw [he]
  exact nextState_workState a.regs W rows _ _ _ fuel fresh

/-- The exponential count of visits does not occur in this all-prefix bound. -/
theorem visits_stack_bound (W : List Bool) (rows : List (List (List Bool)))
    (h B : ℕ) (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (candidate : Fin (2 ^ h))
    {costs : List ℕ} {n : ℕ} {a b : Data}
    (hv : CounterForPrograms.Visits countdownPorts body costs n a b)
    (ha : Boundary W rows h candidate 0 a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (compiled (CounterForPrograms.loopCmd countdownPorts body) 19 19)
        prefixSteps (a.withPC (some (compiled
          (CounterForPrograms.loopCmd countdownPorts body) 19 19).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        max (boundaryBound W (naturalKey W rows h candidate) rows h +
          bodyBound W (naturalKey W rows h candidate) rows h B)
          (40 * boundaryBound W (naturalKey W rows h candidate) rows h + 16) := by
  let base := boundaryBound W (naturalKey W rows h candidate) rows h
  let callbackBudget := bodyBound W (naturalKey W rows h candidate) rows h B
  have hbound (phase : ℕ) (a : Data) (ha : Boundary W rows h candidate phase a)
      (i : Fin 24) : (a.stacks i).length ≤ base := by
    have hs := Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length))
      (Finset.mem_univ i)
    change (a.stacks i).length ≤ stackBits a.stacks at hs
    rw [ha.stackBits] at hs
    exact hs
  have hcallback : ∀ a b nb, Eval body nb a b → Boundary W rows h candidate 0 a →
      a.regs (countdownPorts.register 2) = true →
      0 < CounterPrograms.value (a.stacks countdownPorts.counter) →
      Boundary W rows h candidate 1 b ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled body 19 19) prefixSteps
          (a.withPC (some (compiled body 19 19).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ base + callbackBudget := by
    intro a b nb hb ha _ hp
    obtain ⟨hfinal, htime⟩ := boundary_after_body W rows h B hlen hwidth candidate hb ha hp
    refine ⟨hfinal, ?_⟩
    intro prefixSteps intermediate hle ht i
    apply StructuredSpace.local_stack_bound (compiled body 19 19)
      (steps := callbackBudget) (initialBound := base) _ prefixSteps intermediate
      (hle.trans htime) ht i
    exact le_of_eq ha.stackBits
  have ht := Enumerators.countdown_visits_stack_bound countdownPorts body
    (Boundary W rows h candidate 0) (Boundary W rows h candidate 1)
    base (base + callbackBudget) (hbound 0) (hbound 1) hcallback
    (fun a ha hp => boundary_next W rows h candidate ha hp) hv ha
  intro prefixSteps intermediate hle htrace i
  have hi := ht prefixSteps intermediate hle htrace i
  exact hi.trans (by dsimp [base, callbackBudget]; omega)

/-- Every prefix of the actual counted rescan, including test and halt. -/
theorem for_stack_bound (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) {n : ℕ} {finish : Data}
    (heval : Eval (CounterForPrograms.forCmd countdownPorts body) n
      (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []) finish) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
      Trace (compiled (CounterForPrograms.forCmd countdownPorts body) 19 19)
        prefixSteps ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
          (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []).withPC
          (some (compiled (CounterForPrograms.forCmd countdownPorts body) 19 19).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ loopSpace W rows h B candidate := by
  let a := workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    (ExecCNFTupleEnumeration.fixedBits h candidate) true [] []
  let t := CounterForPrograms.testResult countdownPorts a
  have ht : t = workState t.regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
      (ExecCNFTupleEnumeration.fixedBits h candidate) true [] [] := by
    apply congrArg (StructuredProgram.State.mk t.regs)
    exact CounterForPrograms.testResult_stacks countdownPorts a rfl
  have hf : t.regs 15 = !(CounterPrograms.isZero (ExecCNFTupleEnumeration.fixedBits h candidate)) :=
    CounterForPrograms.testResult_flag countdownPorts a
  obtain ⟨costs, ns, out, hv, _⟩ := visits_exists W rows h B hlen hwidth candidate candidate.val
    0 (ExecCNFTupleEnumeration.fixedBits h candidate) t.regs (by omega) (by simp)
    (ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt) hf
  simp only [AttainedSignatures.duplicateScan, Bool.not_false] at hv
  rw [← ht] at hv
  have hI : Boundary W rows h candidate 0 t := by
    refine ⟨0, ExecCNFTupleEnumeration.fixedBits h candidate, true, by omega, ?_, by simp, ht⟩
    rw [ExecCNFTupleEnumeration.fixedBits_value h candidate candidate.isLt]
    omega
  have hloop := visits_stack_bound W rows h B hlen hwidth candidate hv hI
  have hinitial : ∀ i, (a.stacks i).length ≤
      boundaryBound W (naturalKey W rows h candidate) rows h := by
    intro i
    have hs := Finset.single_le_sum (fun j _ => Nat.zero_le ((a.stacks j).length))
      (Finset.mem_univ i)
    change (a.stacks i).length ≤ stackBits a.stacks at hs
    have hb := boundary_stackBits regs W rows h candidate 0
      (ExecCNFTupleEnumeration.fixedBits h candidate) (by simp) true
    rw [hb] at hs
    exact hs
  have hb := Enumerators.countdown_for_stack_bound countdownPorts body (by rfl)
    hinitial hv hloop
  have htest := CounterForPrograms.test_eval countdownPorts a (by rfl)
  have hsame := StreamResources.eval_steps_eq 19 19 heval (htest.seq hv.eval)
  intro prefixSteps intermediate hle htrace i
  have hle' : prefixSteps ≤ 8 * (a.stacks countdownPorts.counter).length + 7 + ns + 1 := by
    rw [hsame] at hle
    exact hle
  have hi := hb prefixSteps intermediate hle' htrace i
  exact hi.trans (by unfold loopSpace; omega)

theorem setup_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved predecessor : List Bool) (fresh : Bool) :
    ∃ out, Eval setup (7 * candidate.length + 12)
      (workState regs W rows candidate saved predecessor [] fresh [] [])
      (workState out W rows candidate saved predecessor candidate true [] []) := by
  let a := workState regs W rows candidate saved predecessor [] fresh [] []
  let r₁ := readRegs regs 0 1 none
  have hcopy : Eval (copy 16 19) (7 * candidate.length + 5) a
      (workState r₁ W rows candidate saved predecessor candidate fresh [] []) := by
    have ht := copy_eval 16 19 a (by decide) (by decide) (by decide) rfl
    have he : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 16 19 a.stacks⟩ : Data) =
        workState r₁ W rows candidate saved predecessor candidate fresh [] [] := by
      apply congrArg (StructuredProgram.State.mk r₁)
      funext i
      fin_cases i <;> simp [a, workState, StackRoutines.copyStacks]
    rw [he] at ht
    exact ht
  obtain ⟨r₂, hf⟩ := storeFresh_eval true r₁ W rows candidate saved predecessor candidate fresh [] []
  exact ⟨r₂, by simpa only [setup] using hcopy.seq hf⟩

theorem cleanup_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (candidate saved : List Bool) (h : ℕ) (answer : Bool) :
    ∃ out, Eval cleanup (2 * candidate.length + 3 * h + 6)
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
      (workState out W rows candidate saved (List.replicate h false) [] answer [] []) := by
  let r₁ := readRegs regs 0 1 none
  have hclear : Eval (clear 18) (2 * candidate.length + 3)
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
      (workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []) := by
    have ht := clear_eval 18
      (workState regs W rows candidate saved candidate (List.replicate h false) answer [] [])
    have he : StackRoutines.clearStacks 18
        (workState regs W rows candidate saved candidate (List.replicate h false) answer [] []).stacks =
        (workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []).stacks := by
      funext i
      fin_cases i <;> simp [workState, StackRoutines.clearStacks]
    rw [he] at ht
    exact ht
  let b := workState r₁ W rows candidate saved [] (List.replicate h false) answer [] []
  let r₂ := readRegs r₁ 0 1 none
  have htransfer : Eval (.call (StackRoutines.transferProgram 19 18 0 1)) (3 * h + 3) b
      (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []) := by
    have ht : Eval (.call (StackRoutines.transferProgram 19 18 0 1))
        (3 * (b.stacks 19).length + 3) b
        ⟨readRegs b.regs 0 1 none, StackRoutines.transferStacks 19 18 b.stacks⟩ :=
      .call _ (ListRegisterProgram.transfer_run (19 : Fin 24) 18
        (0 : Fin 16) 1 (by decide) (by decide) b.regs b.stacks)
    have he : StackRoutines.transferStacks 19 18 b.stacks =
        (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []).stacks := by
      funext i
      fin_cases i <;> simp [b, workState, StackRoutines.transferStacks]
    rw [he] at ht
    have htarget :
        (⟨readRegs b.regs 0 1 none,
          (workState r₂ W rows candidate saved (List.replicate h false) [] answer [] []).stacks⟩ :
            Data) =
          workState r₂ W rows candidate saved (List.replicate h false) [] answer [] [] := by
      apply congrArg₂ StructuredProgram.State.mk <;> rfl
    rw [htarget] at ht
    change Eval (.call (StackRoutines.transferProgram 19 18 0 1))
      (3 * (List.replicate h false).length + 3) b _ at ht
    simpa only [List.length_replicate] using ht
  refine ⟨r₂, ?_⟩
  convert hclear.seq htransfer using 1
  · rfl
  · omega

theorem sequence_stack_bound {first second : Code} {n m bound : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : ∀ p q, p ≤ n → Trace (compiled first 19 19) p
      (a.withPC (some (compiled first 19 19).entry)) q → ∀ i, (q.stacks i).length ≤ bound)
    (hsecond : ∀ p q, p ≤ m → Trace (compiled second 19 19) p
      (b.withPC (some (compiled second 19 19).entry)) q → ∀ i, (q.stacks i).length ≤ bound) :
    ∀ p q, p ≤ n + m → Trace (compiled (.seq first second) 19 19) p
      (a.withPC (some (compiled (.seq first second) 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ bound :=
  StructuredSpace.sequence_stack_bound hf hs 19 19 hfirst hsecond
    (compiled (.seq first second) 19 19) (siteAddress _) (exitAddress _)
    (compiled_site _ 19 19)

theorem control_space_le (W : List Bool) (rows : List (List (List Bool))) (h B c t : ℕ)
    (ht : t ≤ 7 * h + 12) :
    boundaryBound W (naturalKey W rows h c) rows h + t ≤ loopSpace W rows h B c := by
  unfold loopSpace boundaryBound
  omega

theorem command_stack_bound (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) {n : ℕ} {finish : Data}
    (heval : Eval command n
      (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []) finish) :
    ∀ p q, p ≤ n + 1 → Trace (compiled command 19 19) p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).withPC (some (compiled command 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
  obtain ⟨r₁, hs⟩ := setup_eval regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0) fresh
  obtain ⟨nf, _, rf, hf⟩ := for_eval r₁ W rows h B hlen hwidth candidate
  obtain ⟨r₂, hc⟩ := cleanup_eval rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
    (naturalKey W rows h candidate) h
    (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate))
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hs hc
  let base := boundaryBound W (naturalKey W rows h candidate) rows h
  have hsetup : ∀ p q, p ≤ 7 * h + 12 → Trace (compiled setup 19 19) p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).withPC (some (compiled setup 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
    intro p q hp hq i
    have hb : stackBits (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).stacks ≤ base := by
      rw [workState_stackBits]
      simp only [ExecCNFTupleEnumeration.fixedBits_length, List.length_nil]
      dsimp [base, boundaryBound]
      omega
    have hh := StructuredSpace.local_stack_bound (compiled setup 19 19)
      (a := (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
        [] fresh [] []).withPC (some (compiled setup 19 19).entry))
      (steps := 7 * h + 12) hb p q hp hq i
    exact hh.trans (control_space_le W rows h B candidate _ le_rfl)
  have hcleanup : ∀ p q, p ≤ 5 * h + 6 → Trace (compiled cleanup 19 19) p
      ((workState rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
        (List.replicate h false)
        (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []).withPC
        (some (compiled cleanup 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
    intro p q hp hq i
    have hb := boundary_stackBits rf W rows h candidate candidate
      (List.replicate h false) (by simp)
      (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate))
    have hh := StructuredSpace.local_stack_bound (compiled cleanup 19 19)
      (a := (workState rf W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
        (naturalKey W rows h candidate) (ExecCNFTupleEnumeration.fixedBits h candidate)
        (List.replicate h false)
        (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []).withPC
        (some (compiled cleanup 19 19).entry))
      (steps := 5 * h + 6) (le_of_eq hb) p q hp hq i
    exact hh.trans (control_space_le W rows h B candidate _ (by omega))
  have hloop := for_stack_bound r₁ W rows h B hlen hwidth candidate hf
  have hcleanupCost : 2 * h + 3 * h + 6 = 5 * h + 6 := by omega
  rw [hcleanupCost] at hc
  have htail := sequence_stack_bound hf hc
    (fun p q hp hq i => hloop p q (by omega) hq i) hcleanup
  have hwhole := sequence_stack_bound hs (hf.seq hc) hsetup htail
  have hhalt := StructuredSpace.compiled_halt_stack_bound (hs.seq (hf.seq hc)) 19 19 hwhole
  have htime := StreamResources.eval_steps_eq 19 19 heval (hs.seq (hf.seq hc))
  intro p q hp hq i
  rw [htime] at hp
  exact hhalt p q hp hq i

theorem candidate_stack_bound_oai (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) {n : ℕ} {finish : Data}
    (heval : Eval candidateCommand n
      (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []) finish) :
    ∀ p q, p ≤ n + 1 → Trace candidateProgram p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
        (some candidateProgram.entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
  obtain ⟨np, hnp, rp, hp⟩ := prepareKey_eval regs W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    fresh (by simpa using hlen)
  obtain ⟨nc, _, rc, hc⟩ := command_eval rp W rows h B hlen hwidth candidate fresh
  let base := boundaryBound W (naturalKey W rows h candidate) rows h
  have htime : np ≤ bodyBound W (naturalKey W rows h candidate) rows h B := by
    have hs := cost_le W (ExecCNFTupleEnumeration.fixedBits h candidate) rows B
      (by simpa using hlen) hwidth
    simp only [ExecCNFTupleEnumeration.fixedBits_length] at hs hnp
    unfold bodyBound naturalKey
    omega
  have hprepare : ∀ p q, p ≤ np → Trace (compiled prepareKey 19 19) p
      ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
        (some (compiled prepareKey 19 19).entry)) q →
      ∀ i, (q.stacks i).length ≤ loopSpace W rows h B candidate := by
    intro p q hp' hq i
    have hb : stackBits (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).stacks ≤ base := by
      rw [workState_stackBits]
      simp only [ExecCNFTupleEnumeration.fixedBits_length, List.length_nil]
      dsimp [base, boundaryBound]
      omega
    have hh := StructuredSpace.local_stack_bound (compiled prepareKey 19 19)
      (a := (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
        (some (compiled prepareKey 19 19).entry))
      (steps := bodyBound W (naturalKey W rows h candidate) rows h B)
      hb p q (hp'.trans htime) hq i
    exact hh.trans (Nat.le_max_left _ _)
  have hscan := command_stack_bound rp W rows h B hlen hwidth candidate fresh hc
  have hwhole := sequence_stack_bound hp hc hprepare
    (fun p q hp' hq i => hscan p q (by omega) hq i)
  have hconverted := StructuredSpace.command_stack_bound (hp.seq hc) 19 19 hwhole
    candidateProgram (siteAddress candidateCommand) (exitAddress candidateCommand)
    (compiled_site candidateCommand 16 22)
  have hhalt := StructuredSpace.compiled_halt_stack_bound (hp.seq hc) 16 22 hconverted
  have hn := StreamResources.eval_steps_eq 16 22 heval (hp.seq hc)
  intro p q hp' hq i
  rw [hn] at hp'
  exact hhalt p q hp' hq i


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound_oai
