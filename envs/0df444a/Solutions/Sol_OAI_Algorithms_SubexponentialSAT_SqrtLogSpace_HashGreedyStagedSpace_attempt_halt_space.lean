-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attempt_halt_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:37:42.333787+00:00
-- url     : https://prove2.me/submissions/89370a61-89e5-48fb-94c7-d6f94e6a56c5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashCandidateProgram_Leaf_prepare_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyProgram_PadScore_leaf_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassStaged_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassStagedSpace_command_halt_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Data for the exact-counting statement, corresponding to source lines 45–77.
The primitive execution and space obligations are separate from these data definitions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

theorem binaryNat_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (binaryNat a).length ≤ n + 1 := by
  by_cases hzero : a = 0
  · simp [binaryNat, hzero]
  · simpa only [binaryNat, ite_eq_right hzero, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-valued mass for finite sparse-hash selection.
The row semantics are abstract here; no evaluator is assumed computable
from this definition at the target cost. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R I : Type*}

theorem mass_le [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R) (m : ℕ)
    (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight rows ≤ Fintype.card X * m := by
  calc
    mass rowAccept weight rows ≤ ∑ _x : X, m := by
      apply Finset.sum_le_sum
      intro x _
      cases hx : accepts rowAccept rows x <;> simp [ hw x]
    _ = Fintype.card X * m := by simp

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual clause violations and sparse hash factors on the original variables. -/

namespace SubexponentialSAT.SqrtLog.HashInput


open scoped BigOperators
noncomputable section

variable {V E I R : Type*} [DecidableEq V] [CommRing R]

section Hash
variable [Fintype E] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
theorem violationWeight_le (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight C x ≤ Fintype.card E := by
  calc
    _ ≤ ∑ _e : E, 1 := Finset.sum_le_sum fun e _ => by split_ifs <;> omega
    _ = _ := by simp

end Hash
end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectTermination
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entirely integer termination for the finite greedy selector. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

theorem initial_mass_lt_cap_power {X R : Type*} [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ) (initial : List R)
    (n m : ℕ) (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight initial < 2 ^ (n + Nat.size m + 1) := by
  have hm := Nat.lt_size_self m
  calc
    mass rowAccept weight initial ≤ Fintype.card X * m :=
      mass_le rowAccept weight initial m hw
    _ ≤ 2 ^ n * m := Nat.mul_le_mul_right m hx
    _ < 2 ^ n * 2 ^ Nat.size m := Nat.mul_lt_mul_of_pos_left hm (by positivity)
    _ ≤ 2 ^ (n + Nat.size m + 1) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

end SubexponentialSAT.SqrtLog.HashSelect

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

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- Canonical mass words fit the saved round-count shape even when all m
marked counts contribute. An n+1 count bound is not used for this score. -/
theorem canonical_mass_length {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m : ℕ) (rows : List (List Bool))
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    (DisjointReuse.binaryNat (HashSelect.mass rowAccept weight rows)).length ≤
      HashSelect.loopCap n m := by
  have h := DisjointReuse.binaryNat_length_le
    (HashSelect.initial_mass_lt_cap_power rowAccept weight rows n m hx hw).le
  unfold HashSelect.loopCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMarked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Weighted selector mass is the sum of ordinary marked-clause counts.
This identity justifies executing the same count pipeline once per supplied
clause; no weighted arithmetic is hidden in the local indicator evaluator. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open scoped BigOperators

variable {X Row E : Type*} [Fintype X] [Fintype E]

theorem sum_markedCount (rowAccept : Row → X → Bool) (rows : List Row)
    (bad : E → X → Bool) :
    (∑ e, markedCount rowAccept rows bad e) =
      HashSelect.mass rowAccept (violationWeight bad) rows := by
  unfold markedCount HashSelect.mass violationWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases h : HashSelect.accepts rowAccept rows x <;> simp []

variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem cnf_weight (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight (fun e x => !(C e).eval x) x = HashInput.violationWeight C x := by
  unfold violationWeight HashInput.violationWeight
  apply Finset.sum_congr rfl
  intro e _
  cases h : (C e).eval x <;> simp [h]

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

variable {X Row : Type*} [Fintype X] {m : ℕ}


open LeafOuterProgram

open scoped BigOperators

/-- The concrete descending reference stream visits each original selector
exactly once; reversing its order does not change the full marked sum. -/
theorem alphabet_sum_marked {X Row : Type*} [Fintype X] {m : ℕ}
    (rowAccept : Row → X → Bool) (rows : List Row) (bad : Fin m → X → Bool)
    (count : List Bool → ℕ)
    (hcount : ∀ e : Fin m, count (Encoding.encodeNat e.val) = markedCount rowAccept rows bad e) :
    ((RowSelectionProgram.Index.alphabet m).map count).sum =
      HashSelect.mass rowAccept (violationWeight bad) rows := by
  rw [RowSelectionProgram.Index.alphabet, List.map_map, List.map_reverse, List.sum_reverse]
  rw [← List.map_coe_finRange m, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  simp only [Function.comp_def]
  simp_rw [hcount]
  exact sum_markedCount rowAccept rows bad


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
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

theorem prefixed_rows (a : Data) :
    (prefixed a).stacks 701=true::(Encoding.frame (a.stacks 768).reverse++a.stacks 701) := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,
    TupleProgram.frame_eq_escaped,List.append_assoc]

theorem prefixed_scratch (a : Data) : (prefixed a).stacks 702=[] := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed]

theorem prefixed_frame (a : Data) (i : Fin 896) (h1 : i≠701) (h2 : i≠702) :
    (prefixed a).stacks i=a.stacks i := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,h1,h2]

theorem trialStaged_sources (a : Data) :
    (trialStaged a).stacks 700=a.stacks 784 ∧
    (trialStaged a).stacks 701=true::(Encoding.frame (a.stacks 768).reverse++a.stacks 777) ∧
    (trialStaged a).stacks 707=a.stacks 782 ∧
    (trialStaged a).stacks 708=a.stacks 783 ∧
    (trialStaged a).stacks 709=a.stacks 785 := by
  have h := finalStaged_sources a
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (prefixed_frame _ 700 (by decide) (by decide)).trans h.1
  · rw [trialStaged,prefixed_rows,h.2.1,
      finalStaged_frame a 768 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact (prefixed_frame _ 707 (by decide) (by decide)).trans h.2.2.1
  · exact (prefixed_frame _ 708 (by decide) (by decide)).trans h.2.2.2.1
  · exact (prefixed_frame _ 709 (by decide) (by decide)).trans h.2.2.2.2

theorem trialStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h2 : i≠702) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (trialStaged a).stacks i=a.stacks i :=
  (prefixed_frame _ i h1 h2).trans (finalStaged_frame a i h0 h1 h7 h8 h9)

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

theorem staged_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ stagedPorts) :
    (LeafOuterNative.trialStaged a).stacks i = a.stacks i := by
  have hne : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [stagedPorts] using hi
  exact LeafOuterNative.trialStaged_frame a i hne.1 hne.2.1 hne.2.2.1
    hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2

theorem staged_stacks_congr (a b : State 40 896) (h : a.stacks = b.stacks) :
    (LeafOuterNative.trialStaged a).stacks = (LeafOuterNative.trialStaged b).stacks := by
  funext i
  have ha := LeafOuterNative.trialStaged_sources a
  have hb := LeafOuterNative.trialStaged_sources b
  by_cases hi : i ∈ stagedPorts
  · simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [ha.1,hb.1,h]
    · rw [ha.2.1,hb.2.1,h]
    · exact (LeafOuterNative.prefixed_scratch _).trans (LeafOuterNative.prefixed_scratch _).symm
    · rw [ha.2.2.1,hb.2.2.1,h]
    · rw [ha.2.2.2.1,hb.2.2.2.1,h]
    · rw [ha.2.2.2.2,hb.2.2.2.2,h]
  · rw [staged_frame a i hi,staged_frame b i hi,h]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual candidate attempt is the fixed normalizer, all-clause mass
collector, and paid fixed-width padding. The only remaining query execution
premise is the concrete per-mark evaluator, including its exact caller frame. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter

theorem reference_sum {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) :
    ((RowSelectionProgram.Index.alphabet m).map (referenceCount clauses rows)).sum =
      HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) rows := by
  rw [alphabet_sum_marked (HashGreedyCNF.rowAccept clauses) rows
    (fun e x => !(clauses e).eval x) _ (referenceCount_encode clauses rows)]
  congr 1
  funext x
  exact cnf_weight clauses x

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyStagedSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix storage for the physically staged candidate attempt. The full marked-query
runtime never appears in this bound: the marked queries supply an independent
prefix cap, while preparation, reference setup and padding are polynomial. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter HashGreedyExecution

theorem attempt_halt_space_oai {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (rows : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (a : State 40 896) (word : List Bool) (L K : ℕ)
    (hL : ∀ i, (a.stacks i).length ≤ L)
    (hpayload : HashCandidates.payloadWidth m depth ≤ L) (hscore : HashSelect.loopCap n m ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hgrowth : outputGrowth (fun _ => n + 1) (RowSelectionProgram.Index.alphabet m) ≤ 3 * L + 2)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [])
    (hq : ∀ (e : Fin m) tail (base : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState a m depth word))) base →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState a m depth word)) ∧ read middle = read base ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail []))
    (hspace : ∀ (e : Fin m) tail base t middle,
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState a m depth word))) base →
      (read base).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      (Encoding.encodeNat e.val).length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse) K)
    {steps : ℕ} {result : State 40 896} (he : Eval (attempt (HashMassStaged.command query)) steps a result) :
    StageSpace (attempt (HashMassStaged.command query)) (steps + 1) a (attemptSpace a n m depth L K) := by
  let trialRows := HashCandidates.normalize m depth word.reverse :: rows
  obtain ⟨np, hnp, b, hp, hprep⟩ := HashCandidateProgram.Leaf.prepare_eval hm a word
    hword hcounter hclean hlow ht hwidth hvalue
  have hws : workspace (LeafOuterNative.trialStaged b) =
      workspace (LeafOuterNative.trialStaged (trialState a m depth word)) := by
    have hs := HashMassStaged.staged_stacks_congr b (trialState a m depth word) hprep
    exact congrArg (fun words => fun i => words (workPort i)) hs
  have hbempty : ∀ i ∈ HashMassStaged.stagedPorts, b.stacks i = [] := by
    intro i hi
    have hne : i ≠ 768 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [hprep, hne, hempty i hi]
  have hb : ReferencesReady b := by
    constructor
    · simp [hprep, ht]
    · intro i hi
      have hempty : a.stacks i = [] := by
        rcases hi with hi | rfl
        · exact hlow i (by omega)
        · exact hcollector 320 (by decide) (by decide)
      have hne : i ≠ 768 := by
        intro hi768
        subst i
        rcases hi with hi | hi
        · exact (by decide : ¬ (768 : Fin 896).val < 9) hi
        · exact (by decide : (768 : Fin 896) ≠ 320) hi
      simp [hprep, hne, hempty]
  have hbL : ∀ i, (b.stacks i).length ≤ L := by
    intro i
    by_cases hi : i = 768
    · subst i
      simpa [hprep] using hpayload
    · simpa [hprep, hi] using hL i
  have hq' : ∀ bits tail (base : State 40 896),
      (∃ e : Fin m, bits = Encoding.encodeNat e.val) →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged b)) base →
      ∃ t middle, t ≤ queryCost bits ∧ workspace middle = workspace (LeafOuterNative.trialStaged b) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) =
          referenceCount clauses trialRows bits ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []) := by
    intro bits tail base hvalid hready
    obtain ⟨e, rfl⟩ := hvalid
    simpa only [hws, referenceCount_encode, trialRows] using
      hq e tail base (by simpa only [hws] using hready)
  have hspace' : ∀ bits tail base t middle, (∃ e : Fin m, bits = Encoding.encodeNat e.val) →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged b)) base →
      (read base).length ≤ 3 * L + 2 → tail.length ≤ 3 * L + 2 →
      bits.length ≤ 3 * L + 2 → n + 1 ≤ 3 * L + 2 →
      Eval query t (state recordPorts base false true false tail bits.reverse)
        (state recordPorts middle false true false tail []) →
      StageSpace query t (state recordPorts base false true false tail bits.reverse) K := by
    intro bits tail base t middle hvalid hready hr ht' hbits hw hrun
    obtain ⟨e, rfl⟩ := hvalid
    exact hspace e tail base t middle (by simpa only [hws] using hready) hr ht' hbits hw hrun
  have hbcollector : ∀ i : Fin 896, 321 ≤ i.val → i.val ≤ 324 → b.stacks i = [] := by
    intro i hi hj
    have hne : i ≠ 768 := by intro h; subst i; omega
    simp [hprep, hne, hcollector i (by omega) hj]
  obtain ⟨nq, _, c, hmass, hquery⟩ := HashMassStaged.eval query (referenceCount clauses trialRows)
    queryCost (fun _ => n + 1) (fun bits => ∃ e : Fin m, bits = Encoding.encodeNat e.val) b m hb
    (by simpa [hprep] using hmword) hbcollector hbempty (fun e => ⟨e, rfl⟩) hq'
  have hmassSpace := HashMassStagedSpace.command_halt_space query (referenceCount clauses trialRows)
    queryCost (fun _ => n + 1) (fun bits => ∃ e : Fin m, bits = Encoding.encodeNat e.val) b m L K hb
    (by simpa [hprep] using hmword) hbL hbcollector
    (fun e => ⟨e, rfl⟩) href hgrowth hq' hspace' hmass
  rw [reference_sum] at hquery
  have hlen : (DisjointReuse.binaryNat (HashSelect.mass (HashGreedyCNF.rowAccept clauses)
      (HashInput.violationWeight clauses) trialRows)).length ≤ HashSelect.loopCap n m :=
    HashGreedyCandidate.canonical_mass_length _ _ n m trialRows (by simp [SAT.Assignment])
      (fun x => by simpa using HashInput.violationWeight_le clauses x)
  have hcL : ∀ i, (c.stacks i).length ≤ L := by
    intro i
    by_cases hi : i = 769
    · subst i
      simpa [hquery] using hlen.trans hscore
    · simpa [hquery, hi] using hbL i
  have hcshape : (c.stacks 818).length = HashSelect.loopCap n m := by simp [hquery, hprep, hshape]
  obtain ⟨last, hpad, _⟩ := PadScore.leaf_eval c
    (by simp [hquery, hprep, hlow 0 (by decide)])
    (by simp [hquery, hprep, hlow 1 (by decide)])
    (by simp [hquery, hprep, hlow 2 (by decide)]) (by simpa [hquery, hprep, hshape] using hlen)
  have hprepSpace : StageSpace HashCandidateProgram.Leaf.prepare np a (attemptSpace a n m depth L K) := by
    constructor
    intro k state hk htrace i
    have h := StructuredSpace.local_stack_bound (compiled HashCandidateProgram.Leaf.prepare 778 777)
      (StreamResources.dataBits_le_mul _ hL) k state (hk.trans hnp) htrace i
    unfold attemptSpace
    omega
  have hmassBound : StageSpace (HashMassStaged.command query) nq b (attemptSpace a n m depth L K) := by
    constructor
    intro k state hk htrace i
    have h := hmassSpace.bound k state (by omega) htrace i
    have hroute : LeafOuterProgram.routeCost (782,0) b = LeafOuterProgram.routeCost (782,0) a := by
      simp [LeafOuterProgram.routeCost, hprep]
    have hword782 : b.stacks 782 = a.stacks 782 := by simp [hprep]
    unfold HashMassStagedSpace.spaceBudget at h
    rw [hroute, hword782] at h
    unfold attemptSpace
    omega
  have hpadSpace : StageSpace PadScore.leafCommand (23 * (c.stacks 818).length + 20) c
      (attemptSpace a n m depth L K) := by
    constructor
    intro k state hk htrace i
    have h := StructuredSpace.local_stack_bound (compiled PadScore.leafCommand 778 777)
      (StreamResources.dataBits_le_mul _ hcL) k state hk htrace i
    rw [hcshape] at h
    unfold attemptSpace
    omega
  have hfull := hp.seq (hmass.seq hpad)
  have hstage := StageSpace.seq hp (hmass.seq hpad) hprepSpace
    (StageSpace.seq hmass hpad hmassBound hpadSpace)
  have hsteps := StreamResources.eval_steps_eq 778 777 he hfull
  rw [hsteps]
  exact ⟨StructuredSpace.compiled_halt_stack_bound hfull 778 777 hstage.bound⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attempt_halt_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace.attempt_halt_space_oai
