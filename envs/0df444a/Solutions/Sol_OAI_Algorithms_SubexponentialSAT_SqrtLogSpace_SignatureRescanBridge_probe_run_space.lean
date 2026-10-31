-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:55:33.95327+00:00
-- url     : https://prove2.me/submissions/1195fe20-6059-4d85-8c72-075408a1a494

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_rowCommand_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_candidate_stack_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram_Rescan_prepareKey_eval
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

theorem conditional_true_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = true) (heval : StructuredCalls.Eval yes steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled yes inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled yes inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.ite test yes no) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.ite test yes no) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.ite test yes no) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  refine trace_prefix_bound_cons (steps := steps)
    (P := fun x : Cfg r s L => ∀ i, (x.stacks i).length ≤ bound)
    (b := a.withPC (some (StructuredCalls.entry yes (fun q => embed (some (.inl q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inl q))) exit (fun q => hcode (some (.inl q)))

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

theorem signatureValue_length_bound (W bits : List Bool) (rows : List (List (List Bool))) (B : ℕ)
    (hl : ∀ row∈rows,row.length=bits.length)
    (hb : ∀ row∈rows,∀ x∈row,x.length ≤ B) :
    (signatureValue W bits rows).length ≤ rows.length*(2*(widthBound W bits.length B+1)+1) := by
  have hs : ∀ x∈(rows.map (rowKey W bits)).reverse, x.length ≤ widthBound W bits.length B+1 := by
    intro x hx
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    have hrw := rowWidth_bound W row B (hb row hr)
    rw [hl row hr] at hrw
    exact (rowKey_length_bound W bits row (hl row hr)).trans (Nat.add_le_add_right hrw 1)
  simpa [signatureValue] using words_length_bound (rows.map (rowKey W bits)).reverse
    (widthBound W bits.length B+1) hs

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

theorem candidateCommand_eval (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ cost W (ExecCNFTupleEnumeration.fixedBits h candidate) rows +
        9 * (naturalKey W rows h candidate).length +
        candidate.val * (bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16) +
        29 * h + 43, ∃ out,
      Eval candidateCommand n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
          (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  obtain ⟨np, hnp, rp, hp⟩ := prepareKey_eval regs W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) (ExecCNFTupleEnumeration.fixedBits h 0)
    fresh (by simpa using hlen)
  obtain ⟨nc, hnc, rc, hc⟩ := command_eval rp W rows h B hlen hwidth candidate fresh
  refine ⟨np + nc, ?_, rc, hp.seq hc⟩
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hnp
  change np ≤ cost W (ExecCNFTupleEnumeration.fixedBits h candidate) rows +
    9 * h + 9 * (naturalKey W rows h candidate).length + 17 at hnp
  omega

theorem naturalKey_length_le (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (c : ℕ) :
    (naturalKey W rows h c).length ≤ keyBound W h rows.length B := by
  have ht := signatureValue_length_bound W (ExecCNFTupleEnumeration.fixedBits h c) rows B
    (by simpa using hlen) hwidth
  simpa only [naturalKey, keyBound,
    ExecCNFTupleEnumeration.fixedBits_length] using ht

theorem candidate_time_uniform (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B, ∃ out,
      Eval candidateCommand n
        (workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
          (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] [])
        (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []) := by
  obtain ⟨n, hn, out, ht⟩ := candidateCommand_eval regs W rows h B hlen hwidth candidate fresh
  have hs := cost_le W (ExecCNFTupleEnumeration.fixedBits h candidate) rows B
    (by simpa using hlen) hwidth
  simp only [ExecCNFTupleEnumeration.fixedBits_length] at hs
  have hk := naturalKey_length_le W rows h B hlen hwidth candidate
  have hbody : bodyBound W (naturalKey W rows h candidate) rows h B + 16 * h + 16 ≤
      polynomialBudget W rows h B := by unfold bodyBound polynomialBudget; omega
  have hsetup : cost W (ExecCNFTupleEnumeration.fixedBits h candidate) rows +
      9 * (naturalKey W rows h candidate).length + 29 * h + 43 ≤
      polynomialBudget W rows h B := by unfold polynomialBudget; omega
  refine ⟨n, ?_, out, ht⟩
  calc
    n ≤ candidate.val * polynomialBudget W rows h B + polynomialBudget W rows h B := by
      have hm := Nat.mul_le_mul_left candidate.val hbody
      omega
    _ = (candidate.val + 1) * polynomialBudget W rows h B := by rw [Nat.add_mul, one_mul]

theorem loopSpace_le (W : List Bool) (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B) (c : ℕ) :
    loopSpace W rows h B c ≤ spaceBudget W rows h B := by
  have hk := naturalKey_length_le W rows h B hlen hwidth c
  have hb : bodyBound W (naturalKey W rows h c) rows h B ≤ polynomialBudget W rows h B := by
    unfold bodyBound polynomialBudget
    omega
  unfold loopSpace spaceBudget boundaryBound
  omega

/-- One fixed actual candidate machine returns the canonical full key and
freshness bit, with time and every-prefix storage bounds on that same run. -/
theorem candidate_run (regs : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool))) (h B : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B + 1, ∃ out,
      Trace candidateProgram n
        ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
          (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
          (some candidateProgram.entry))
        ((workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
          (naturalKey W rows h candidate) (List.replicate h false) []
          (!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)) [] []).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace candidateProgram prefixSteps
          ((workState regs W rows (ExecCNFTupleEnumeration.fixedBits h candidate) []
            (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] []).withPC
            (some candidateProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ spaceBudget W rows h B := by
  obtain ⟨steps, hsteps, out, he⟩ := candidate_time_uniform regs W rows h B hlen hwidth candidate fresh
  refine ⟨steps + 1, Nat.add_le_add_right hsteps 1, out, compiled_halt_trace he 16 22, ?_⟩
  intro prefixSteps intermediate hle ht i
  exact (candidate_stack_bound regs W rows h B hlen hwidth candidate fresh he
    prefixSteps intermediate hle ht i).trans (loopSpace_le W rows h B hlen hwidth candidate)


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem clearWord_eval (src : Fin 896) (a : State 40 896) :
    Eval (clearWord src) (2 * (a.stacks src).length + 3) a (clearState src a) := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  exact .call _ (by simpa [clearState, StackRoutines.clearResult, StackRoutines.clearStacks,
    StructuredProgram.State.withPC, StackRoutines.clearProgram, Nat.add_assoc] using hh)

theorem testAvailable_eval (a : State 40 896) (hs : a.stacks remainingPorts.scratch = []) :
    Eval testAvailableCommand (8 * (a.stacks remainingPorts.counter).length + 8) a
      (testAvailableState a) := by
  have ht := Eval.seq (CounterForPrograms.test_eval remainingPorts a hs)
    (Eval.base (StructuredProgram.Eval.atom
      (.copy controllerPorts.available (remainingPorts.register 2)) _))
  simpa only [testAvailableCommand, testAvailableState, Nat.add_assoc] using ht

theorem testAvailableState_flag (a : State 40 896) :
    (testAvailableState a).regs controllerPorts.available =
      !(CounterPrograms.isZero (a.stacks remainingPorts.counter)) :=
  CounterForPrograms.testResult_flag remainingPorts a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

theorem initializeFresh_eval (a : State 40 896) :
    Eval initializeFreshCommand (2 * (a.stacks (rescanStacks 22)).length + 5) a
      (initializeFreshState a) := by
  have ht := Eval.seq (clearWord_eval (rescanStacks 22) a)
    (Eval.base (StructuredProgram.Eval.seq (.atom (.set 0 false) _)
      (.atom (.push (rescanStacks 22) 0) _)))
  simpa only [initializeFreshCommand, initializeFreshState, Nat.add_assoc] using ht

theorem initializeFreshState_word (a : State 40 896) :
    (initializeFreshState a).stacks (rescanStacks 22) = [false] := by
  simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, clearState]

/-- The preserved caller frame is charged once when transferring the local
predicate's uniform bound to all896 physical source stacks. -/
theorem rescan_lifted_stack_bound {labels steps bound frameBound : ℕ}
    (routine : Program 16 24 labels) (frame : Cfg 40 896 labels)
    {a b : Cfg 16 24 labels} (hrun : Trace routine steps a b)
    (hlocal : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram routine rescanRegisters rescanStacks) prefixSteps
        (ProgramLinking.embedCfg rescanRegisters rescanStacks id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  StructuredSpace.liftProgram_stack_bound routine rescanRegisters rescanStacks frame
    rescanRegisters.injective rescanStacks.injective hrun hlocal hframe


/-- The actual complete predicate retains its exact key and freshness result,
with time and all physical source-stack prefixes bounded on one lifted run.
The caller's persistent data are included through `frameBound`. -/
theorem candidate_run (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h B frameBound : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound)
    (candidate : Fin (2 ^ h)) (fresh : Bool) :
    ∃ n ≤ (candidate.val + 1) *
        AttainedSignatureProgram.Rescan.polynomialBudget W rows h B + 1, ∃ out,
      Eval candidateCall n (candidateInput frame regs W rows h candidate fresh)
        (candidateOutput frame out W rows h candidate) ∧
      Trace candidateMachine n
        ((candidateInput frame regs W rows h candidate fresh).withPC
          (some candidateMachine.entry))
        ((candidateOutput frame out W rows h candidate).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace candidateMachine prefixSteps
          ((candidateInput frame regs W rows h candidate fresh).withPC
            (some candidateMachine.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (AttainedSignatureProgram.Rescan.spaceBudget W rows h B) frameBound := by
  obtain ⟨n, hn, out, ht, hspace⟩ :=
    AttainedSignatureProgram.Rescan.candidate_run regs W rows h B hlen hwidth candidate fresh
  have htrace := ProgramLinking.liftProgram_trace
    AttainedSignatureProgram.Rescan.candidateProgram rescanRegisters rescanStacks
    (frame.withPC none) rescanRegisters.injective rescanStacks.injective ht
  have htrace' : Trace candidateMachine n
      ((candidateInput frame regs W rows h candidate fresh).withPC
        (some candidateMachine.entry))
      ((candidateOutput frame out W rows h candidate).withPC none) := by
    simpa [candidateMachine, candidateInput, candidateOutput, ProgramLinking.embedCfg,
      ProgramLinking.relocatePc, embedState, StructuredProgram.State.withPC,
      ProgramLinking.liftProgram] using htrace
  refine ⟨n, hn, out, .call _ htrace', htrace', ?_⟩
  have hb := rescan_lifted_stack_bound
    AttainedSignatureProgram.Rescan.candidateProgram (frame.withPC none) ht hspace hframe
  simpa [candidateMachine, candidateInput, ProgramLinking.embedCfg,
    ProgramLinking.relocatePc, embedState, StructuredProgram.State.withPC,
    ProgramLinking.liftProgram] using hb

theorem testAvailableState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (testAvailableState a).stacks = a.stacks :=
  CounterForPrograms.testResult_stacks remainingPorts a hs

theorem initializeFreshState_stacks (a : State 40 896) :
    (initializeFreshState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  funext i
  by_cases hi : i = rescanStacks 22
  · subst i
    rw [Function.update_self, initializeFreshState_word]
  · simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, clearState]

theorem probePreState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePreState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  rw [probePreState, initializeFreshState_stacks, testAvailableState_stacks a hs]

/-- Preparing a candidate changes only the latch word. The whole fixed local
input projection is then the one used in the proved native rescan theorem. -/
theorem CandidateReady.probe_projection {a : State 40 896} {W : List Bool}
    {rows : List (List (List Bool))} {h : ℕ} {candidate : Fin (2 ^ h)}
    (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    projectState rescanRegisters rescanStacks (probePreState a) =
      AttainedSignatureProgram.Rescan.workState
        ((probePreState a).regs ∘ rescanRegisters) W rows
        (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change (probePreState a).stacks (rescanStacks i) = _
  rw [probePreState_stacks a hs]
  have hf (j : Fin 24) (hj : j ≠ 22) : rescanStacks j ≠ rescanStacks 22 :=
    fun he => hj (rescanStacks.injective he)
  by_cases h22 : i = 22
  · subst i
    rw [Function.update_self]
    rfl
  rw [Function.update_of_ne (hf i h22)]
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  by_cases h16 : i = 16
  · subst i; exact ready.current
  by_cases h17 : i = 17
  · subst i; exact ready.saved
  by_cases h18 : i = 18
  · subst i; exact ready.predecessor
  rw [ready.scratch i h0 h15 h16 h17 h18 h22]
  fin_cases i <;> simp_all

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureRescanBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Physical effects of one full-signature probe

The input readiness facts describe actual words. The native predicate itself
supplies the run; its returned freshness is the first-occurrence predicate for
the complete integer signature.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open AttainedSignatureProgram.Rescan

private theorem sequence_prefix {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : ∀ p q, p ≤ n → Trace (compiled first 0 0) p
      (a.withPC (some (compiled first 0 0).entry)) q → ∀ i, (q.stacks i).length ≤ bound)
    (hsecond : ∀ p q, p ≤ m → Trace (compiled second 0 0) p
      (b.withPC (some (compiled second 0 0).entry)) q → ∀ i, (q.stacks i).length ≤ bound) :
    ∀ p q, p ≤ n + m → Trace (compiled (.seq first second) 0 0) p
      (a.withPC (some (compiled (.seq first second) 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ bound :=
  StructuredSpace.sequence_stack_bound hf hs 0 0 hfirst hsecond
    (compiled (.seq first second) 0 0) (siteAddress _) (exitAddress _)
    (compiled_site _ 0 0)

/-- Uniform storage for the full probe, including its availability test,
latch initialization, compiled candidate call, readback and final halt.
The numeric candidate appears only in time, never in the storage bound. -/
theorem probe_run_space_oai (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h B frameBound : ℕ)
    (hlen : ∀ row ∈ rows, row.length = h)
    (hwidth : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ B)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = [])
    (hnonzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = false)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    ∃ n ≤ (candidate.val + 1) * polynomialBudget W rows h B +
        8 * (a.stacks remainingPorts.counter).length +
        2 * (a.stacks (rescanStacks 22)).length + 16, ∃ out,
      Eval (probeWith candidateCall) n a (probePostState a out W rows h candidate) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (probeWith candidateCall) 0 0) prefixSteps
          (a.withPC (some (compiled (probeWith candidateCall) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * (spaceBudget W rows h B + frameBound + 1) +
            8 * (a.stacks remainingPorts.counter).length +
            2 * (a.stacks (rescanStacks 22)).length + 20 := by
  let t := testAvailableState a
  let pre := probePreState a
  let readback : Cmd 40 896 := .base (.atom (.peek (rescanStacks 22) controllerPorts.fresh 0))
  let totalBound := 896 * (spaceBudget W rows h B + frameBound + 1) +
    8 * (a.stacks remainingPorts.counter).length +
    2 * (a.stacks (rescanStacks 22)).length + 20
  have htwords : t.stacks = a.stacks := testAvailableState_stacks a hs
  have hpre : ∀ i, (pre.stacks i).length ≤ frameBound + 1 := by
    intro i
    change ((probePreState a).stacks i).length ≤ _
    rw [probePreState_stacks a hs]
    by_cases hi : i = rescanStacks 22
    · subst i; simp
    · rw [Function.update_of_ne hi]
      exact (hframe i).trans (Nat.le_succ _)
  have hi : candidateInput pre (pre.regs ∘ rescanRegisters) W rows h candidate false = pre := by
    unfold candidateInput
    rw [← ready.probe_projection hs]
    exact embedState_project _ _ _ rescanRegisters.injective rescanStacks.injective
  obtain ⟨nc, hnc, out, hce, hct, hcp⟩ := SignatureTupleNative.candidate_run pre
    (pre.regs ∘ rescanRegisters) W rows h B (frameBound + 1) hlen hwidth hpre candidate false
  rw [hi] at hce hct hcp
  let finish := candidateOutput pre out W rows h candidate
  have hfinish : ∀ i, (finish.stacks i).length ≤ spaceBudget W rows h B + frameBound + 1 := by
    intro i
    have hb := hcp nc (finish.withPC none) le_rfl hct i
    exact hb.trans (by omega)
  have htest := testAvailable_eval a hs
  have hinit := initializeFresh_eval t
  rw [htwords] at hinit
  have hread : Eval readback 1 finish (probePostState a out W rows h candidate) :=
    .base (.atom (.peek (rescanStacks 22) controllerPorts.fresh 0) finish)
  have hav : t.regs controllerPorts.available = true := by
    rw [testAvailableState_flag, hnonzero]
    rfl
  have hrest := hinit.seq (hce.seq hread)
  have hall := htest.seq (Eval.ite_true (no := .base .skip) hav hrest)
  change Eval (probeWith candidateCall) _ a (probePostState a out W rows h candidate) at hall
  have htestSpace : ∀ p q, p ≤ 8 * (a.stacks remainingPorts.counter).length + 8 →
      Trace (compiled testAvailableCommand 0 0) p
        (a.withPC (some (compiled testAvailableCommand 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    have hb := StructuredSpace.local_stack_bound (compiled testAvailableCommand 0 0)
      (a := a.withPC (some (compiled testAvailableCommand 0 0).entry))
      (steps := 8 * (a.stacks remainingPorts.counter).length + 8)
      (StreamResources.dataBits_le_mul _ hframe)
    intro p q hp hq i
    exact (hb p q hp hq i).trans (by dsimp [totalBound]; omega)
  have hinitSpace : ∀ p q, p ≤ 2 * (a.stacks (rescanStacks 22)).length + 5 →
      Trace (compiled initializeFreshCommand 0 0) p
        (t.withPC (some (compiled initializeFreshCommand 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    have htframe : ∀ i, (t.stacks i).length ≤ frameBound := by
      rw [htwords]
      exact hframe
    have hb := StructuredSpace.local_stack_bound (compiled initializeFreshCommand 0 0)
      (a := t.withPC (some (compiled initializeFreshCommand 0 0).entry))
      (steps := 2 * (a.stacks (rescanStacks 22)).length + 5)
      (StreamResources.dataBits_le_mul _ htframe)
    intro p q hp hq i
    exact (hb p q hp hq i).trans (by dsimp [totalBound]; omega)
  have hcandidateSpace : ∀ p q, p ≤ nc → Trace (compiled candidateCall 0 0) p
      (pre.withPC (some (compiled candidateCall 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    apply StructuredSpace.call_stack_bound candidateMachine (compiled candidateCall 0 0)
      (siteAddress candidateCall) (exitAddress candidateCall)
      (fun pc => compiled_site candidateCall 0 0 pc) hct
    intro p q hp hq i
    exact (hcp p q hp hq i).trans (by dsimp [totalBound]; omega)
  have hreadSpace : ∀ p q, p ≤ 1 → Trace (compiled readback 0 0) p
      (finish.withPC (some (compiled readback 0 0).entry)) q →
      ∀ i, (q.stacks i).length ≤ totalBound := by
    have hb := StructuredSpace.local_stack_bound (compiled readback 0 0)
      (a := finish.withPC (some (compiled readback 0 0).entry)) (steps := 1)
      (StreamResources.dataBits_le_mul _ hfinish)
    intro p q hp hq i
    exact (hb p q hp hq i).trans (by dsimp [totalBound]; omega)
  have htailSpace := sequence_prefix hce hread hcandidateSpace hreadSpace
  have hrestSpace := sequence_prefix hinit (hce.seq hread) hinitSpace htailSpace
  have hbranchSpace := StructuredSpace.conditional_true_stack_bound
    (no := .base .skip) hav hrest 0 0 hrestSpace
    (compiled (.ite controllerPorts.available _ (.base .skip)) 0 0)
    (siteAddress _) (exitAddress _) (compiled_site _ 0 0)
  have hwholeSpace := sequence_prefix htest (Eval.ite_true (no := .base .skip) hav hrest) htestSpace hbranchSpace
  refine ⟨_, ?_, out, hall, ?_⟩
  · omega
  · exact StructuredSpace.compiled_halt_stack_bound hall 0 0 hwholeSpace

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space_oai
