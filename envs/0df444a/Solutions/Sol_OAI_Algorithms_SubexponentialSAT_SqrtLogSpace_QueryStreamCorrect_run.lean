-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:54:49.275064+00:00
-- url     : https://prove2.me/submissions/858087f8-250e-460e-9ce7-0f4c27ab945c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryLoop_prepare_high_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryKeptFrame_kept_frame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryReconstruction_run_space_with_full_frame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect_nodes_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata_actual_target_degree
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata_native_count
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata_native_count_le

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit finite geometric inversion and local CRT factors

The inverses in this file are finite polynomial expressions. Scalar inverses are
input data with multiplication certificates; no Bézout coefficients are chosen.
-/

noncomputable section

namespace SubexponentialSAT.TruncatedInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem trunc_degree_lt (D : ℕ) (f : A[X]) :
    (Truncation.trunc D f).degree < (D : ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).2
  intro n hn
  simp [Truncation.coeff_trunc, Nat.not_lt.mpr hn]

theorem X_pow_dvd_sub_trunc (D : ℕ) (f : A[X]) :
    (X : A[X]) ^ D ∣ f - Truncation.trunc D f := by
  rw [X_pow_dvd_iff]
  intro n hn
  simp [Truncation.coeff_trunc, hn]

/-- Coefficient truncation and monic remainder are the same operation. -/
theorem trunc_eq_modByMonic (D : ℕ) (f : A[X]) :
    Truncation.trunc D f = f %ₘ (X ^ D) := by
  nontriviality A
  have hself : Truncation.trunc D f %ₘ (X ^ D) = Truncation.trunc D f := by
    apply (modByMonic_eq_self_iff (monic_X.pow D)).2
    rw [degree_X_pow]
    exact trunc_degree_lt D f
  exact ((modByMonic_eq_of_dvd_sub (monic_X.pow D)
    (X_pow_dvd_sub_trunc D f)).trans hself).symm

theorem jet_eq_trunc (a : A) (D : ℕ) (f : A[X]) :
    JetCRT.jet a D f = Truncation.trunc D (f.comp (X + C a)) :=
  (trunc_eq_modByMonic D _).symm

@[simp] theorem jet_modByMonic (a : A) (D : ℕ) (f : A[X]) :
    JetCRT.jet a D f %ₘ (X ^ D) = JetCRT.jet a D f := by
  rw [jet_eq_trunc, ← trunc_eq_modByMonic, trunc_idempotent]

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_Reconstruction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit reconstruction for independently chosen node and jet counts

This interface reuses the audited dense-list Hermite program. Its inverse
table is computed by finite powers and geometric sums. No interpolation
choice, scalar-inverse oracle, or field assumption on the coefficient ring
occurs in `run`. The represented arithmetic callbacks carry their own costs.
-/

namespace SubexponentialSAT.SqrtLog.Reconstruction

noncomputable section

open Polynomial

variable {C A : Type*} [CommRing A]

theorem hasJets_of_coefficients (ops : SubexpSymbolicCost.RepresentedRing C A)
    {Q : ℕ} (nodes : Fin Q → C) (order : ℕ)
    (jets : Fin Q → List C) (target : Polynomial A)
    (h : ∀ i n, n < order →
      (PolynomialAlgorithm.denote ((jets i).map ops.decode)).coeff n =
        (target.comp (X + Polynomial.C (ops.decode (nodes i)))).coeff n) :
    HasJets ops nodes order jets target := by
  intro i
  rw [TruncatedInverse.jet_eq_trunc]
  ext n
  by_cases hn : n < order
  · simpa only [Truncation.coeff_trunc, ite_eq_left hn] using h i n hn
  · simp only [Truncation.coeff_trunc, ite_eq_right hn]

end
end SubexponentialSAT.SqrtLog.Reconstruction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source parameter object is derived from the executed query's numeric
bank, ring setup, and native head cache. Source order and jet order remain distinct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

theorem numeric_Q (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ) :
    (numeric q k l).val 21=(produce (q.input k)).Q :=
  (Execute.guardedModel_public (q.input k) l 4).trans (Layout.model_core_values (q.input k) l).2.2.2.2.1

theorem numeric_t (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (numeric q k l).val 33=(produce (q.input k)).t :=
  Execute.guardedModel_precision _ _ (Nat.ne_of_gt hg.2.2.1)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingQueryMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual query frontend links its addressed head node count to the
numeric bank. The generic native factor construction is independent of this
frontend execution closure. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram.PreparedSource

/-- The authentic addressed head input and the actual numeric bank use the
same node count; the input padding does not alter this value. -/
theorem actual_heads_node_count (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (node : Fin (LeafProgram.Query.packingProblem q k hg).Q) (l : Fin 8 → ℕ) :
    (heads q k hg first tail node).Q = (numeric q k l).val 21 :=
  (numeric_Q q k l).symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The polynomial reconstructed by the native query is the target of its
actual generated ternary ring and idempotent code. Its constant term is the
exact marked or unmarked count; the executed parameter bank supplies both
the interpolation budget and sufficient precision. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram
open LeafProgram.PreparedSource LeafProgram.NodeConcrete

attribute [local irreducible] Execute.guardedModel

theorem numeric_precision (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    (numeric q k lengths).val 33 =
      precision (BinaryArithmetic.toNat q.ambient) (BinaryArithmetic.toNat q.modulus) :=
  numeric_t q k lengths hg

theorem ambient_lt_precision (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    (Query.packingProblem q k hg).n < (numeric q k lengths).val 33 := by
  rw [numeric_precision q k lengths hg]
  change BinaryArithmetic.toNat q.ambient <
    precision (BinaryArithmetic.toNat q.ambient) (BinaryArithmetic.toNat q.modulus)
  unfold precision
  omega

theorem count_modulus (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    2 ^ (Query.packingProblem q k hg).n < 3 ^ (numeric q k lengths).val 33 :=
  (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 3)
      (ambient_lt_precision q k lengths hg))

section Addressed

variable (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ)
    (hg : Guard (q.input k))
    (first : MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem q k hg).r
      (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q) (lengths : Fin 8 → ℕ)

local notation "s" => heads q k hg first tail node
local notation "m" => numeric q k lengths
local notation "ht" => Query.ring_precision_pos (q.input k) lengths hg
local notation "hd" => Query.ring_degree_pos (q.input k) lengths hg

variable (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads q k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads q k hg first tail node).R)
      (heads q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((numeric q k lengths).val 33))
    (cache : RingProgram.ScalarCache 3 ((numeric q k lengths).val 33))
    (half : RingProgram.ScalarCode 3 ((numeric q k lengths).val 33))
    (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (numeric q k lengths)
      (Query.ring_degree_pos (q.input k) lengths hg) M cache half e)
    (source : List (List (SAT.Literal (Fin (heads q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  (numeric_field q k lengths hg) q hv (Circuit.Model.val m 42)
  (numeric_order_pos q k lengths hg) source hsource

theorem actual_target_degree_executed (hwidth : ∀ c ∈ source, c.length ≤ k)
    (H : Finset (Fin (s).n)) (high : H → Bool) :
    (specTarget spec H high).natDegree < (m).val 21 * (m).val 42 := by
  rw [← RingNodeMetadata.actual_heads_node_count q k hg first tail node lengths]
  exact actual_target_degree q hv k hg first tail node lengths words hc M cache half e hp
    source hsource hwidth H high

end Addressed

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The coefficients emitted by the actual ordered node loop determine the
same fixed-length Hermite inputs consumed by the native reconstruction tail.
No canonical choice of coefficient bytes across node states is required. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open Polynomial DensePolynomialProgram LeafProgram LeafParametersProgram

/-- Package the very coefficient words emitted at each node. The witness
selection is proof-only; the actual machine already retained their flat bytes. -/
theorem jets_of_outputs {A : Type*} [CommRing A] {width d Q J : ℕ}
    (ops : SubexpSymbolicCost.RepresentedRing (Coeff width d) A)
    (nodes : Fin Q → Coeff width d) (target : Polynomial A)
    (outputs : List (List Bool)) (hlen : outputs.length = Q)
    (houtputs : ∀ i : Fin Q, ∃ codes : List (Coeff width d),
      codes.length = J ∧
      codes.map ops.decode = List.ofFn
        (Truncated.ofPolynomial J (target.comp (X + C (ops.decode (nodes i))))).coeff ∧
      outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten) :
    ∃ jets : Fin Q → CRTLocalProgram.Model.Poly width d J,
      outputs.flatten = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)) ∧
      Reconstruction.HasJets ops nodes J (fun i => (jets i).val) target := by
  classical
  choose codes hlength hvalue hbits using houtputs
  let jets : Fin Q → CRTLocalProgram.Model.Poly width d J := fun i => ⟨codes i, hlength i⟩
  refine ⟨jets, ?_, ?_⟩
  · have hout : outputs = (List.finRange Q).map (fun i => Fixed.encode (jets i)) := by
      apply List.ext_getElem (by simp [hlen])
      intro i hi hj
      have hfinBound : i < (List.finRange Q).length := by simpa using hj
      have hiQ : i < Q := by simpa using hfinBound
      have hfin : (List.finRange Q)[i]'hfinBound = (⟨i, hiQ⟩ : Fin Q) := by
        apply Fin.ext
        simp
      rw [List.getElem_map, hfin]
      simpa only [jets, Fixed.encode, DensePolynomialProgram.encode] using hbits ⟨i, hiQ⟩
    rw [hout, List.flatMap_def]
  · apply Reconstruction.hasJets_of_coefficients
    intro i z hz
    change (PolynomialAlgorithm.denote ((codes i).map ops.decode)).coeff z = _
    rw [hvalue i, PolynomialAlgorithm.coeff_denote]
    have hcoeff (xs : List A) (j : ℕ) (hj : j < xs.length) :
        PolynomialAlgorithm.coeff xs j = xs[j] := by
      induction xs generalizing j with
      | nil => simp at hj
      | cons x xs ih =>
        cases j with
        | zero => rfl
        | succ j => exact ih j (by simpa using hj)
    rw [hcoeff (List.ofFn (Truncated.ofPolynomial J
      (target.comp (X + C (ops.decode (nodes i))))).coeff) z (by simpa using hz)]
    simp only [List.getElem_ofFn, Truncated.coeff_ofPolynomial]


open QueryReconstruction in
/-- The native recovery consumes exactly the ordered coefficient words emitted
by the node loop. Its Hermite certificate is derived from those same words. -/
theorem run_space_of_outputs_with_full_frame (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (outputs : List (List Bool)) (hlen : outputs.length = m.val 21)
    (hstream : a.stacks 863 = outputs.flatten)
    (houtputs : ∀ i : Fin (m.val 21),
      ∃ codes : List (Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
        codes.length = m.val 42 ∧
        codes.map (RingProgram.modelRing (m.val 33) ht hd
          (IrreducibleSearch.data hd) M cache).decode = List.ofFn
          (Truncated.ofPolynomial (m.val 42) (target.comp (X + C
            ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
              (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)))))).coeff ∧
        outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten)
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧
      out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 896, i ∈ retainedPorts → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  obtain ⟨jets, hbytes, hhas⟩ := jets_of_outputs
    (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
    (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
    target outputs hlen houtputs
  exact QueryReconstruction.run_space_with_full_frame m ht hd M cache half e hp a
    hscratch hframe hnodes hQ hJ hfield hexponent jets (hstream.trans hbytes)
    target hdegree hhas count multiplicity ambient hcount hlarge hconstant B S ha
    hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize hcountsize

section ActualQuery

open PreparedSource QueryReconstruction

variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
    (hv : query.Valid)
    (first : MulticolorTypes.Word (Query.packingProblem query k hg).r
      (Query.packingProblem query k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem query k hg).r
      (Query.packingProblem query k hg).Q))
    (node : Fin (Query.packingProblem query k hg).Q) (lengths : Fin 8 → ℕ)
    (m : Circuit.Model) (hm : m = numeric query k lengths)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)

local notation "headsInput" => heads query k hg first tail node

variable (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads query k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads query k hg first tail node).R) (heads query k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (source : List (List (SAT.Literal (Fin (heads query k hg first tail node).n))))
    (hsource : query.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "factor" => nativeSpecOfInputs headsInput m ht hd words hc M cache half e hp
  (field_of_model query k lengths hg m hm) query hv (Circuit.Model.val m 42)
  (order_of_model query k lengths hg m hm) source hsource

theorem query_run_space_with_full_frame (H : Finset (Fin (headsInput).n)) (high : H → Bool)
    (hwidth : ∀ clause ∈ source, clause.length ≤ k)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (outputs : List (List Bool)) (hlen : outputs.length = m.val 21)
    (hstream : a.stacks 863 = outputs.flatten)
    (houtputs : ∀ i : Fin (m.val 21),
      ∃ codes : List (Coeff (baseWidth 3 (m.val 33)) (m.val 34)),
        codes.length = m.val 42 ∧
        codes.map (RingProgram.modelRing (m.val 33) ht hd
          (IrreducibleSearch.data hd) M cache).decode = List.ofFn
          (Truncated.ofPolynomial (m.val 42)
            ((NodeConcrete.specTarget factor H high).comp (X + C
              ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
                (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)))))).coeff ∧
        outputs[i.val]'(by omega) = (codes.map RingProgram.flat).flatten)
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hambient : (headsInput).n + 1 ≤ B) :
    let count := NodeSemantics.ternaryFixedHighCount H high
      (NodeConcrete.sourceHashes factor) (factor).marked (factor).markedClause
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧ out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 896, i ∈ retainedPorts → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  dsimp only
  have hQ : 0 < m.val 21 := by
    rw [hm, numeric_Q]
    have hh := hg.2.2.2.2.2.2.1
    omega
  have hfield : m.val 21 < 3^(m.val 34) := by
    rw [hm, numeric_Q]
    exact numeric_field query k lengths hg
  have hdegree : (NodeConcrete.specTarget factor H high).natDegree < m.val 21 * m.val 42 := by
    subst m
    exact QueryTargetMetadata.actual_target_degree_executed query hv k hg
      first tail node lengths words hc M cache half e hp source hsource hwidth H high
  have hconstant := QueryTargetMetadata.native_count headsInput m ht hd words hc
    M cache half e hp (field_of_model query k lengths hg m hm) query hv (m.val 42)
    (order_of_model query k lengths hg m hm) source hsource H high
  have hcount := QueryTargetMetadata.native_count_le headsInput m ht hd words hc
    M cache half e hp (field_of_model query k lengths hg m hm) query hv (m.val 42)
    (order_of_model query k lengths hg m hm) source hsource H high
  have hlarge : 1 * 2^(headsInput).n < 3^(m.val 33) := by
    rw [hm]
    have hn : (headsInput).n = (Query.packingProblem query k hg).n := by rfl
    rw [hn, one_mul]
    exact QueryTargetMetadata.count_modulus query k lengths hg
  exact run_space_of_outputs_with_full_frame m ht hd M cache half e hp a hscratch hframe hnodes
    hQ (order_of_model query k lengths hg m hm) hfield
    (by rw [hm]; exact Query.ring_exponent (query.input k) lengths hg)
    (NodeConcrete.specTarget factor H high) outputs hlen hstream houtputs hdegree
    _ 1 (headsInput).n (by simpa using hcount) hlarge hconstant B S ha
    hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize
    ((DisjointReuse.binaryNat_length_le hcount).trans hambient)

end ActualQuery

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

/-- Compose the actual decoder, ordered node execution and reconstruction.
The three independently established space caps combine by maximum. -/
theorem command_eval_prefix {np nn nr Dp Dn Dr : ℕ} {a b c out : Data}
    (hp : Eval HighQueryAdapter.prepareHigh np a b)
    (hn : Eval QueryStreamProgram.nodes nn b c)
    (hr : Eval QueryReconstruction.command nr c out)
    (sp : QueryExecution.PrefixBound HighQueryAdapter.prepareHigh (np+1) a Dp)
    (sn : QueryExecution.PrefixBound QueryStreamProgram.nodes (nn+1) b Dn)
    (sr : QueryExecution.PrefixBound QueryReconstruction.command (nr+1) c Dr) :
    Eval QueryStreamProgram.command (np+nn+nr) a out ∧
      Trace QueryStreamProgram.program (np+nn+nr+1)
        (a.withPC (some QueryStreamProgram.program.entry)) (out.withPC none) ∧
      QueryExecution.PrefixBound QueryStreamProgram.command (np+nn+nr+1) a
        (max Dp (max Dn Dr)) := by
  have ep : QueryExecution.PrefixBound HighQueryAdapter.prepareHigh np a
      (max Dp (max Dn Dr)) := ⟨fun k z hk hz i =>
    (sp.bound k z (by omega) hz i).trans (Nat.le_max_left _ _)⟩
  have en : QueryExecution.PrefixBound QueryStreamProgram.nodes nn b
      (max Dp (max Dn Dr)) := ⟨fun k z hk hz i =>
    (sn.bound k z (by omega) hz i).trans
      ((Nat.le_max_left Dn Dr).trans (Nat.le_max_right _ _))⟩
  have er : QueryExecution.PrefixBound QueryReconstruction.command nr c
      (max Dp (max Dn Dr)) := ⟨fun k z hk hz i =>
    (sr.bound k z (by omega) hz i).trans
      ((Nat.le_max_right Dn Dr).trans (Nat.le_max_right _ _))⟩
  have he : Eval QueryStreamProgram.command (np+nn+nr) a out := by
    simpa only [QueryStreamProgram.command,Nat.add_assoc] using hp.seq (hn.seq hr)
  have hs := QueryExecution.prefix_seq hp (hn.seq hr) ep
    (QueryExecution.prefix_seq hn hr en er)
  refine ⟨he,compiled_halt_trace he 330 323,⟨?_⟩⟩
  apply StructuredSpace.compiled_halt_stack_bound he 838 838
  simpa only [QueryStreamProgram.command,Nat.add_assoc] using hs.bound

section ActualNode
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource LeafHeadSetupProgram
open QueryNodeEvaluation

variable (query : LeafQueryFrontend.Query) (k RB RC RD RI RE : ℕ)
  (hg : Guard (query.input k)) (hv : query.Valid)
  (first : MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (Query.packingProblem query k hg).r
    (Query.packingProblem query k hg).Q))
  (node : Fin (Query.packingProblem query k hg).Q)
  (m : Circuit.Model) (padding : Fin 8 → ℕ)
  (hm : m=Execute.guardedModel (query.input k) padding)
  (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3 ^ (m.val 34))
  (hQ : m.val 21=(Native.queryInputsAddressed query k hg first tail node).Q)
  (hR : (base.stacks 740).length=(Native.queryInputsAddressed query k hg first tail node).R)
  (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
local notation "H" => HighMarkedFrontend.highSet query
local notation "resources" => ProducedQueryResources.ofPacking query k RB RC RD RI RE hg first tail
local notation "work" => CostAssembly.assembledWork k (ProducedQueryResources.ambient query) resources


include hm hQ hR in
/-- The fixed conditioned query executes high decoding, all interpolation
nodes, and canonical reconstruction on one trace. The count is obtained from
the actual source target and the same emitted coefficient bytes. -/
theorem run_oai (A S : ℕ) (a : State 40 896)
    (frontBase front : State 40 768) (bw : Bank.Words)
    (hf : Query.FrontState query k frontBase front padding bw)
    (hpark : ∀ j : Fin 14,
      a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) =
        (PackingCallerProgram.result front (Query.packingProblem query k hg)
          first tail).stacks (LayoutMasters.high j))
    (hparked : ∀ j : Fin 14,
      (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
    (hcache : ∀ i∈cacheInputPorts,(a.stacks i).length≤A)
    (hvalues : ∀ i,m.val i≤A)
    (hsources : Query.Sources query (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length≤A) (h701 : (a.stacks 701).length≤A)
    (h708 : (a.stacks 708).length≤A)
    (hnodes : a.stacks 300=Encoding.encodeList id
      (RingNodeMetadata.nodeBits (m.val 33) (m.val 34) (m.val 21)))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i∈QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h704 : a.stacks 704=List.replicate query.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex query))
    (h706 : a.stacks 706=[query.mark.isSome])
    (counterWords : List (List Bool))
    (hshape : counterWords.map List.length=List.replicate (H).card 1)
    (rank : Fin (2^(H).card)) (hrank : CounterPrograms.value counterWords.flatten=rank.val)
    (hcounter : a.stacks 330=Encoding.encodeList id counterWords)
    (hring : ∀ i∈QueryReconstruction.ringPorts,
      a.stacks (i.castAdd 576)=e.stacks (i.castAdd 320))
    (hflat : a.stacks 256=e.stacks 256)
    (hwidth : ∀ clause∈source,clause.length≤k)
    (ha : WordBound (QueryHeadBudgets.compact A) a)
    (hAS : A≤S) (hqsize : 3^(m.val 34)≤S)
    (hmodsize : (a.stacks 194).length≤S) (hwidthsize : (a.stacks 202).length≤S)
    (hambient : (native).n+1≤QueryHeadBudgets.compact A) :
    ∃ words, ∃ hc : CacheCorrect (native).height (unary (native).R) (native).width words,
    ∃ steps final,
      let high := HighIncidenceProgram.Rank.highEquiv (HighIncidenceProgram.Order.highOrder H) rank
      let factor := nativeSpecOfInputs native m ht hd words hc M cache half e ho.produced
        hfield query hv (m.val 42) hJ source hsource
      Eval QueryStreamProgram.command steps a final ∧
      Trace QueryStreamProgram.program (steps+1)
        (a.withPC (some QueryStreamProgram.program.entry)) (final.withPC none) ∧
      final.stacks 323=DisjointReuse.binaryNat
        (NodeSemantics.ternaryFixedHighCount H high (NodeConcrete.sourceHashes factor)
          factor.marked factor.markedClause) ∧
      final.stacks 863=[] ∧ WordBound (QueryHeadBudgets.compact A) final ∧
      (∀ i∈retainedPorts,i≠702 → i≠703 → final.stacks i=a.stacks i) ∧
      (∀ i,HashMarkedReturn.kept i=true → final.stacks i=a.stacks i) ∧
      steps+1≤budget (native).n (m.val 33) (m.val 34) (m.val 21) (m.val 42) A S work ∧
      QueryExecution.PrefixBound QueryStreamProgram.command (steps+1) a
        (space (native).n (m.val 33) (m.val 34) (m.val 42) A S) := by
  let F := QueryHeadBudgets.compact A
  let high := HighIncidenceProgram.Rank.highEquiv (HighIncidenceProgram.Order.highOrder H) rank
  obtain ⟨np,rf,hp,hpt,h702,h703,hpf,hb,hps⟩ :=
    HighQueryLoop.prepare_high_resources H counterWords hshape rank hrank a F F
      hcounter hmask (ha 330) (ha 338) (fun i _ => ha i) ha
  let b := HighQueryAdapter.highResult (HighQueryAdapter.resetHighState a) rf counterWords.flatten
  have bp : ∀ j : Fin 14,b.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))=
      a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j)) := by
    intro j
    apply hpf
    fin_cases j <;> decide
  have bc : ∀ i∈cacheInputPorts,b.stacks i=a.stacks i := by
    intro i hi
    apply hpf
    simp only [cacheInputPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have bf : ∀ i∈QueryReadyConstruction.arithmeticPorts,b.stacks (i.castAdd 128)=out.stacks i := by
    intro i hi
    apply Eq.trans (hpf _ ?_) (hframe i hi)
    simp only [QueryReadyConstruction.arithmeticPorts, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have bs : Query.Sources query
      (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort b) :=
    ⟨(hpf 700 (by decide)).trans hsources.formula,
      (hpf 701 (by decide)).trans hsources.rows,
      (hpf 707 (by decide)).trans hsources.modulus,
      (hpf 708 (by decide)).trans hsources.width,
      (hpf 709 (by decide)).trans hsources.ambient⟩
  obtain ⟨words,hc,nn,c,outputs,he,hi,hlen,hstream,houtputs,hnt,hns⟩ :=
    nodes_run query k RB RC RD RI RE hg hv first tail node m padding ht hd M cache half e
      base out ho hfield hJ source hsource high A b frontBase front bw hf
      (fun j => (bp j).trans (hpark j)) (fun j => by rw [bp j]; exact hparked j)
      (fun i h => by rw [bc i h]; exact hcache i h) hvalues bs
      (by rw [hpf 700 (by decide)]; exact h700)
      (by rw [hpf 701 (by decide)]; exact h701)
      (by rw [hpf 708 (by decide)]; exact h708)
      ((hpf 300 (by decide)).trans hnodes) ((hpf 338 (by decide)).trans hmask) bf hdegree
      ((hpf 704 (by decide)).trans h704) ((hpf 705 (by decide)).trans h705)
      ((hpf 706 (by decide)).trans h706) h702 h703 hb hm hQ hR
  have hpositive : 0 < m.val 21 := by
    have hn := node.isLt
    change node.val < (native).Q at hn
    omega
  have cring : ∀ i∈QueryReconstruction.ringPorts,
      c.stacks (i.castAdd 576)=e.stacks (i.castAdd 320) := by
    intro i hii
    have hm : i.castAdd 576∈retainedPorts := by
      simp only [QueryReconstruction.ringPorts, List.mem_cons,
        List.not_mem_nil, or_false] at hii
      rcases hii with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hd : i.castAdd 576∉HighQueryAdapter.highChanged := by
      simp only [QueryReconstruction.ringPorts, List.mem_cons,
        List.not_mem_nil, or_false] at hii
      rcases hii with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (hi.retained _ hm).trans ((hpf _ hd).trans (hring i hii))
  obtain ⟨nr,final,hrt,hr,htrace,hcount,hblank,hfinal,hu,h320,h322,hlow,hret,_hreg,hrs⟩ :=
    QueryCountReconstruction.query_run_space_with_full_frame query k hg hv first tail node
      padding m hm ht hd words hc M cache half e ho.produced source hsource H high hwidth
      c (hi.readout_scratch hpositive) cring
      ((hi.retained 256 (by decide)).trans ((hpf 256 (by decide)).trans hflat)) outputs hlen hstream
      (fun i => houtputs i.val (by omega)) F S hi.bounded
      ((hvalues 21).trans hAS) ((hvalues 42).trans hAS) ((hvalues 33).trans hAS)
      ((hvalues 34).trans hAS) hqsize
      (by rw [hi.retained 194 (by decide),hpf 194 (by decide)]; exact hmodsize)
      (by rw [hi.retained 202 (by decide),hpf 202 (by decide)]; exact hwidthsize) hambient
  have rsp : QueryExecution.PrefixBound QueryReconstruction.command (nr+1) c
      (896*F+QueryReconstruction.budget F S) := ⟨hrs⟩
  have dsp : QueryExecution.PrefixBound HighQueryAdapter.prepareHigh (np+1) a
      (67*F+37) := ⟨fun p q hle ht i =>
    (hps.bound p q hle ht i).trans (max_le (Nat.le_refl _) (by omega))⟩
  obtain ⟨whole,trace,spaceBound⟩ := command_eval_prefix hp he hr dsp hns rsp
  have finalFrame : ∀ i∈retainedPorts,i≠702 → i≠703 → final.stacks i=a.stacks i := by
    intro i him h702i h703i
    have ht : final.stacks i=c.stacks i := by
      have cases : i∈QueryReconstruction.retainedPorts ∨ i=320 ∨ i=322 ∨
          ((330 : ℕ) ≤ i.val ∧ i.val < 768 ∧ i ≠ 699) := by
        have hm := (List.mem_filter.mp him).1
        simp only [framePorts, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals first | decide | simp [retainedPorts] at him
      rcases cases with hc|rfl|rfl|⟨hlo,hhi,hne⟩
      · exact hret i hc
      · exact h320
      · exact h322
      · exact hlow i hlo hhi hne
    have hd : i∉HighQueryAdapter.highChanged := by
      intro hh
      simp only [HighQueryAdapter.highChanged, List.mem_cons,
        List.not_mem_nil, or_false] at hh
      rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first | exact h702i rfl | exact h703i rfl | simp [retainedPorts,framePorts] at him
    exact ht.trans ((hi.retained i him).trans (hpf i hd))
  refine ⟨words,hc,np+nn+nr,final,whole,trace,hcount,hblank,hfinal,finalFrame,?_,?_,?_⟩
  · apply QueryKeptFrame.kept_frame whole
    intro i hii
    apply finalFrame i ?_ ?_ ?_
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
      rcases hii with rfl|rfl|rfl|rfl|rfl <;> decide
  · change np≤18*F+65*(native).n+67 at hpt
    change np+nn+nr+1≤18*F+65*(native).n+67+23*F+
      (m.val 21)*(nodeBudget (native).n (m.val 33) (m.val 34) (m.val 42) A work+1)+32+
      QueryReconstruction.budget F S
    omega
  · exact spaceBound

end ActualNode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run_oai
