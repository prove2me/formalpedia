-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:24:00.091703+00:00
-- url     : https://prove2.me/submissions/000b2d73-15a2-41b8-b198-664604a03699

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram_branch_execution_from_state
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSRefinement_accumulate_after_leaf
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSRefinement_popCurrent_boundary
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSResource_branch_execution_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseSelectorRefinement_selectCurrent_execution

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Syntactic frontend for the variable-parameter SAT algorithm

The external input declares `n` Boolean coordinates. We first normalize the
finite CNF, then enumerate only its syntactically appearing coordinates in
increasing order. The resulting coordinate set is retained through all later
branching; this frontend is not reapplied at sparsification leaves.

All constructions inspect finite syntax. No satisfiability test, choice of a
satisfying assignment, or noncomputable enumeration is used by `prepare`.
-/

namespace SubexponentialSAT.SubexpFrontend

open SAT

theorem literalCode_negate {n : ℕ} (l : Literal (Fin n)) :
    Encoding.literalCode l.negate = negateCode (Encoding.literalCode l) := by
  rcases l with ⟨v, p⟩
  have hd0 : (2 * v.val) / 2 = v.val := by omega
  have hd1 : (2 * v.val + 1) / 2 = v.val := by omega
  have hm0 : (2 * v.val) % 2 = 0 := by omega
  have hm1 : (2 * v.val + 1) % 2 = 1 := by omega
  cases p <;> simp [Encoding.literalCode, Literal.negate, negateCode,
    hd0, hd1, hm0, hm1]

end SubexponentialSAT.SubexpFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
private theorem filter_map_comm (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (L : List α) :
    (L.map f).filter q = (L.filter p).map f := by
  induction L with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [ h, hx, ih]

@[simp] theorem removeTautologies_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : removeTautologies negβ (F.map (List.map f)) =
      (removeTautologies negα F).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [tautology_map f hf negα negβ hn]

@[simp] theorem absorb_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : absorb (F.map (List.map f)) = (absorb F).map (List.map f) := by
  unfold absorb
  rw [dedupClauses_map f hf]
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, strictSubset_map f hf]

@[simp] theorem normalize_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : ExecCNF.normalize negβ (F.map (List.map f)) =
      (ExecCNF.normalize negα F).map (List.map f) := by
  simp only [ExecCNF.normalize, cleanLiterals_map f hf,
    removeTautologies_map f hf negα negβ hn, absorb_map f hf]

@[simp] theorem eraseClauses_map (f : α → β) (hf : Function.Injective f)
    (F S : Formula α) : eraseClauses (F.map (List.map f)) (S.map (List.map f)) =
      (eraseClauses F S).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, equivalent_map f hf]

/-- The actual petal filter commutes with injective literal encoding. -/
theorem petal_filter_map (f : α → β) (hf : Function.Injective f)
    (C H : Clause α) :
    (C.map f).filter (fun x => !decide (x ∈ H.map f)) =
      (C.filter (fun x => !decide (x ∈ H))).map f := by
  apply filter_map_comm f
  intro x
  simp [List.mem_map, hf.eq_iff]

theorem petal_family_map (f : α → β) (hf : Function.Injective f)
    (G : Formula α) (H : Clause α) :
    (G.map (List.map f)).map (fun C => C.filter (fun x => !decide (x ∈ H.map f))) =
      (G.map (fun C => C.filter (fun x => !decide (x ∈ H)))).map (List.map f) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro C _
  exact petal_filter_map f hf C H

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLogic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

theorem execInstr_stack_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin s)
    (hk : k ∉ stackWrites instr) : (execInstr instr c).stacks k = c.stacks k := by
  cases instr <;> simp_all [stackWrites, execInstr]

theorem step_stack_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin s)
    (safe : ∀ label, a.pc = some label → k ∉ stackWrites (p.code label))
    (hs : step p a = some b) : b.stacks k = a.stacks k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_stack_frame _ _ _ (safe label hp)

end BitPrograms

end SubexponentialSAT.ProgramLogic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


theorem result_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (F selected : List (List α)) (H : List α) :
    result (F.map (List.map f)) (selected.map (List.map f)) (H.map f) =
      (result F selected H).map (List.map f) := by
  simp only [result, ExecCNFCodeTransport.eraseClauses_map f hf,
    ← List.map_cons, ExecCNFCodeTransport.absorb_map f hf]

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

theorem result_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (F selected : List (List α)) (H : List α) :
    result (F.map (List.map f)) (selected.map (List.map f)) (H.map f) =
      (result F selected H).map (List.map f) := by
  have hp : petals (selected.map (List.map f)) (H.map f) =
      (petals selected H).map (List.map f) :=
    ExecCNFCodeTransport.petal_family_map f hf selected H
  simp only [result, hp, ExecCNFCodeTransport.eraseClauses_map f hf,
    ← List.map_append, ExecCNFCodeTransport.absorb_map f hf]

end SubexponentialSAT.ExecPetalChildProgram

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

theorem conditional_false_stack_bound {r s L : ℕ} {yes no : StructuredCalls.Cmd r s}
    {test : Fin r} {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (htest : a.regs test = false) (heval : StructuredCalls.Eval no steps a b)
    (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled no inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled no inputStack outputStack).entry)) intermediate →
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
    (b := a.withPC (some (StructuredCalls.entry no (fun q => embed (some (.inr q))) exit)))
    ?_ ?_ ?_
  · simp [step, StructuredProgram.State.withPC, StructuredCalls.entry,
      hcode none, StructuredCalls.code, execInstr, htest]
  · exact hsource 0 _ (Nat.zero_le steps) (.refl _)
  · exact command_stack_bound heval inputStack outputStack hsource caller
      (fun q => embed (some (.inr q))) exit (fun q => hcode (some (.inr q)))

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

theorem length_le_of_sublist {α : Type*} (enc : α → List Bool)
    {xs ys : List α} (h : xs.Sublist ys) :
    (Encoding.encodeList enc xs).length ≤ (Encoding.encodeList enc ys).length := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a h ih =>
      rw [Encoding.length_encodeList_cons]
      omega
  | cons_cons a h ih =>
      rw [Encoding.length_encodeList_cons, Encoding.length_encodeList_cons]
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

theorem masked_sublist {α : Type*} (mask : List Bool) (C : List α) :
    (masked mask C).Sublist C := by
  induction C generalizing mask with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [masked]
    split
    · exact .cons_cons x (ih mask.tail)
    · exact .cons x (ih mask.tail)

theorem rawCandidate_spec {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, C.length = c ∧ H.Sublist C := by
  obtain ⟨C, hC, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, _, hp⟩ := List.mem_map.mp hm
  obtain ⟨hc, hH⟩ := Prod.mk.inj hp
  exact ⟨C, hC, hc, hH ▸ masked_sublist mask C⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

theorem negatedUnits_codes {n : ℕ} (H : List (Literal (Fin n))) :
    negatedUnits SubexpFrontend.negateCode (H.map Encoding.literalCode) =
      (negatedUnits Literal.negate H).map (List.map Encoding.literalCode) := by
  simp [negatedUnits, List.map_reverse, List.map_map, Function.comp_def,
    SubexpFrontend.literalCode_negate]

theorem resultB_codes {n : ℕ} (F S : List (List (Literal (Fin n))))
    (H : List (Literal (Fin n))) :
    resultB SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode))
      (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode) =
      (resultB Literal.negate F S H).map (List.map Encoding.literalCode) := by
  unfold resultB
  rw [negatedUnits_codes, ← List.map_append]
  exact ExecPetalChildProgram.result_map Encoding.literalCode Encoding.literalCode_injective _ _ _

open BitProgram StructuredCalls

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the outer disjoint counting traversal.

The leaf command is an explicit piece of finite code chosen with `k`. Its
layout, reconstruction, input loading and output export are still
separate obligations until the concrete leaf implementation is substituted.
There is no oracle instruction or endpoint theorem in this module.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram

open BitProgram StructuredCalls SubexpPostfixControl

theorem lowPorts_eq :
    lowPorts = (List.finRange 256).map (Fin.castLE (by decide : 256 ≤ 1220)) :=
  lowPortsWrapped.2

theorem testPending_eval (d : Data) :
    Eval testPending 1 d
      ⟨readRegs d.regs 2 1 (d.stacks 257).head?, d.stacks⟩ := by
  simpa [testPending, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr]
    using Eval.base (StructuredProgram.Eval.atom (.peek (257 : Fin 1220) (2 : Fin 80) 1) d)

theorem clearPort_eval (port : Fin 1220) (d : Data) :
    Eval (clearPort port) (2 * (d.stacks port).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run port 0 1 d.regs d.stacks)

theorem clearPorts_eval (ports : List (Fin 1220)) (d : Data) (bound : ℕ)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * ports.length, ∃ e,
      Eval (clearPorts ports) t d e ∧
      (∀ i ∈ ports, e.stacks i = []) ∧
      (∀ i, i ∉ ports → e.stacks i = d.stacks i) ∧
      (∀ i, (e.stacks i).length ≤ bound) := by
  induction ports generalizing d with
  | nil => exact ⟨0, by simp, d, .base (.skip d), by simp, by simp, hbound⟩
  | cons port rest ih =>
    let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩
    have habound : ∀ i, (a.stacks i).length ≤ bound := by
      intro i
      by_cases hi : i = port
      · subst i
        simp [a, StackRoutines.clearStacks]
      · simpa [a, StackRoutines.clearStacks, hi] using hbound i
    obtain ⟨t, ht, e, he, hclear, hframe, hbe⟩ := ih a habound
    refine ⟨2 * (d.stacks port).length + 3 + t, ?_, e,
      (clearPort_eval port d).seq he, ?_, ?_, hbe⟩
    · have hd := hbound port
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with hi | hi
      · subst i
        by_cases hp : port ∈ rest
        · exact hclear port hp
        · rw [hframe port hp]
          simp [a, StackRoutines.clearStacks]
      · exact hclear i hi
    · intro i hi
      have hir : i ∉ rest := fun hir => hi (List.mem_cons_of_mem _ hir)
      have hip : i ≠ port := fun heq => hi (by simp [heq])
      rw [hframe i hir]
      simp [a, StackRoutines.clearStacks, hip]

theorem mem_lowPorts (i : Fin 1220) : i ∈ lowPorts ↔ i.val < 256 := by
  rw [lowPorts_eq]
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem clearLow_eval (d : Data) (bound : ℕ)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * 256, ∃ e,
      Eval clearLow t d e ∧
      (∀ i, i.val < 256 → e.stacks i = []) ∧
      (∀ i, 256 ≤ i.val → e.stacks i = d.stacks i) ∧
      (∀ i, (e.stacks i).length ≤ bound) := by
  obtain ⟨t, ht, e, he, hc, hf, hb⟩ := clearPorts_eval lowPorts d bound hbound
  refine ⟨t, by simpa [lowPorts_eq] using ht, e, he, ?_, ?_, hb⟩
  · intro i hi
    exact hc i ((mem_lowPorts i).mpr hi)
  · intro i hi
    exact hf i (by rw [mem_lowPorts]; omega)



theorem splitter_input_projection (d : Data) (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hscratch : ∀ i : Fin 23, 7 ≤ i.val → d.stacks (splitterStack i) = []) :
    projectState (registers 15 (by decide)) splitterStack d =
      DisjointBranchProgram.inputState (d.regs ∘ registers 15 (by decide))
        (d.stacks 257) (d.stacks 258) F S H := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  refine Fin.addCases (m := 7) (n := 16) (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · rfl
    · rfl
    · exact hleft
    · exact hright
    · exact hF
    · exact hH
    · exact hS
  · simpa [ExecBranchControllerSupport.emptyBank] using
      hscratch (Fin.natAdd 7 j) (by simp)

theorem splitter_input_projection_of_clean (d : Data)
    (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    projectState (registers 15 (by decide)) splitterStack d =
      DisjointBranchProgram.inputState (d.regs ∘ registers 15 (by decide))
        (d.stacks 257) (d.stacks 258) F S H := by
  apply splitter_input_projection d F S H hF hH hS hleft hright
  intro i hi
  have hrange : (splitterStack i).val < 24 ∧ splitterStack i ≠ 9 ∧ splitterStack i ≠ 12 := by
    have h : ∀ j : Fin 23, 7 ≤ j.val →
        (splitterStack j).val < 24 ∧ splitterStack j ≠ 9 ∧ splitterStack j ≠ 12 := by decide
    exact h i hi
  exact hclean _ hrange.1 hrange.2.1 hrange.2.2


/- The typed count identity for the concrete disjoint branch. -/


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSResource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Resource bounds for the actual outer DFS commands.

Cleanup is structurally nonallocating. The bounds below concern the concrete
finite tables and every source prefix, before applying the guarded primitive
compiler. The selector and leaf contracts still require their own executions.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

open BitProgram StructuredCalls SparseDFSProgram

theorem clearPort_space (port : Fin 1220) {steps bound : ℕ} {a b : Data}
    (he : Eval (clearPort port) steps a b)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearPort port) 256 256) prefixSteps
        (a.withPC (some (compiled (clearPort port) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  cases he with
  | call p htrace =>
      apply StructuredSpace.call_stack_bound (StackRoutines.clearProgram port 0 1)
        (compiled (clearPort port) 256 256) (siteAddress (clearPort port))
        (exitAddress (clearPort port)) (compiled_site (clearPort port) 256 256) htrace
      intro prefixSteps c _ hc i
      exact (SparseDFSBoundarySpace.clearProgram_stack_length_le port 0 1 hc i).trans
        (hstart i)

/-- Sequential clearing keeps the same bound, including during every pop
and return jump. The finite list length never multiplies the space bound. -/
theorem clearPorts_space (ports : List (Fin 1220)) {steps bound : ℕ} {a b : Data}
    (he : Eval (clearPorts ports) steps a b)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (clearPorts ports) 256 256) prefixSteps
        (a.withPC (some (compiled (clearPorts ports) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  induction ports generalizing steps a b with
  | nil =>
      cases he with
      | base h =>
          cases h with
          | skip =>
              intro prefixSteps c hp hc
              have hz : prefixSteps = 0 := by omega
              subst prefixSteps
              cases hc
              exact hstart
  | cons port rest ih =>
      cases he with
      | seq first second =>
          have hfirst := clearPort_space port first hstart
          have hmiddle := hfirst _ _ le_rfl (compiled_trace first 256 256)
          exact StructuredSpace.sequence_stack_bound first second 256 256 hfirst
            (ih second hmiddle) (compiled (clearPorts (port :: rest)) 256 256)
            (siteAddress (clearPorts (port :: rest)))
            (exitAddress (clearPorts (port :: rest))) (compiled_site (clearPorts (port :: rest)) 256 256)

theorem testPending_space (a : Data) (bound : ℕ)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ 1 →
      Trace (compiled testPending 256 256) prefixSteps
        (a.withPC (some (compiled testPending 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  intro prefixSteps c hp hc
  have hcases : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
  rcases hcases with rfl | rfl
  · cases hc
    exact hstart
  · rw [trace_same_length_unique hc (compiled_trace (testPending_eval a) 256 256)]
    exact hstart

/-- A complete visit cleanup clears the current formula and all 256 DFS
workspace stacks, preserves the other high words, and restores the loop flag
by reading the real frontier. Every intermediate stack remains bounded. -/
theorem finishVisit_execution_space (a : Data) (bound : ℕ)
    (hstart : ∀ i, (a.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * 257 + 1, ∃ e,
      Eval finishVisit t a e ∧
      (∀ i, i.val < 256 → e.stacks i = []) ∧ e.stacks 265 = [] ∧
      (∀ i, 256 ≤ i.val → i ≠ 265 → e.stacks i = a.stacks i) ∧
      e.regs 2 = (a.stacks 257).head?.getD false ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled finishVisit 256 256) prefixSteps
          (a.withPC (some (compiled finishVisit 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
  let cleared : Data :=
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 265 a.stacks⟩
  have hclear : Eval (clearPort 265) (2 * (a.stacks 265).length + 3) a cleared :=
    clearPort_eval 265 a
  have hclear_space := clearPort_space 265 hclear hstart
  have hcleared : ∀ i, (cleared.stacks i).length ≤ bound :=
    hclear_space _ _ le_rfl (compiled_trace hclear 256 256)
  obtain ⟨lowTime, htime, afterLow, hlow, hempty, hframe, hlowBound⟩ :=
    clearLow_eval cleared bound hcleared
  let final : Data := ⟨readRegs afterLow.regs 2 1 (afterLow.stacks 257).head?, afterLow.stacks⟩
  have htest : Eval testPending 1 afterLow final := testPending_eval afterLow
  have hlow_space : ∀ prefixSteps c, prefixSteps ≤ lowTime →
      Trace (compiled clearLow 256 256) prefixSteps
        (cleared.withPC (some (compiled clearLow 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    simpa only [clearLow] using clearPorts_space lowPorts hlow hcleared
  have htest_space : ∀ prefixSteps c, prefixSteps ≤ 1 →
      Trace (compiled testPending 256 256) prefixSteps
        (afterLow.withPC (some (compiled testPending 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound :=
    testPending_space afterLow bound hlowBound
  have htail_space := StructuredSpace.sequence_stack_bound
    (first := clearLow) (second := testPending) (n := lowTime) (m := 1)
    (bound := bound) (a := cleared) (b := afterLow) (c := final)
    hlow htest 256 256
    hlow_space htest_space
    (compiled (.seq clearLow testPending) 256 256)
    (siteAddress (.seq clearLow testPending)) (exitAddress (.seq clearLow testPending))
    (compiled_site (.seq clearLow testPending) 256 256)
  have hfinish_space : ∀ prefixSteps c,
      prefixSteps ≤ 2 * (a.stacks 265).length + 3 + (lowTime + 1) →
      Trace (compiled finishVisit 256 256) prefixSteps
        (a.withPC (some (compiled finishVisit 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    exact StructuredSpace.sequence_stack_bound hclear (hlow.seq htest) 256 256
      hclear_space htail_space (compiled finishVisit 256 256)
      (siteAddress finishVisit) (exitAddress finishVisit)
      (compiled_site finishVisit 256 256)
  refine ⟨2 * (a.stacks 265).length + 3 + (lowTime + 1), ?_, final,
    hclear.seq (hlow.seq htest), hempty, ?_, ?_, ?_, ?_⟩
  · have h := hstart 265
    omega
  · change afterLow.stacks 265 = []
    rw [hframe 265 (by decide)]
    simp [cleared, StackRoutines.clearStacks]
  · intro i hi hne
    change afterLow.stacks i = a.stacks i
    rw [hframe i hi]
    simp [cleared, StackRoutines.clearStacks, hne]
  · have hpending : afterLow.stacks 257 = a.stacks 257 := by
      rw [hframe 257 (by decide)]
      simp [cleared, StackRoutines.clearStacks]
    simp [final, readRegs, hpending]
  · exact hfinish_space


private theorem lifted_trace_stack_frame {r s l R S steps : ℕ}
    (routine : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    {a b : Cfg R S l} (htrace : Trace (ProgramLinking.liftProgram routine register stack) steps a b)
    (i : Fin S) (hoff : ¬ ∃ j, stack j = i) : b.stacks i = a.stacks i := by
  have hne : ∀ j, i ≠ stack j := fun j he => hoff ⟨j, he.symm⟩
  induction htrace with
  | refl => rfl
  | cons hstep _ ih =>
      apply ih.trans
      apply ProgramLogic.step_stack_frame (ProgramLinking.liftProgram routine register stack) i _ hstep
      intro label _
      change i ∉ ProgramLogic.stackWrites (ProgramLinking.relocateInstr register stack id none
        (routine.code label))
      cases routine.code label <;> simp [ProgramLinking.relocateInstr, ProgramLogic.stackWrites, hne]

/-- Every real branch execution preserves high words outside its fixed port
footprint. The header258 is handled separately by the splitter's exact header
readback; this structural rule covers raw input, leaf count, setup words and
all reserved high stacks for the very same branch witness. -/
theorem branch_preserves_other_high {steps : ℕ} {a b : Data}
    (he : Eval branch steps a b) (i : Fin 1220) (hi : 256 ≤ i.val)
    (hpending : i ≠ 257) (hheader : i ≠ 258) (hleft : i ≠ 261)
    (hright : i ≠ 262) (hcurrent : i ≠ 265) : b.stacks i = a.stacks i := by
  have hsplitOff : ¬ ∃ j, splitterStack j = i := by
    rintro ⟨j, rfl⟩
    have hrange := (by decide : ∀ q : Fin 23,
      (splitterStack q).val < 256 ∨ splitterStack q = 257 ∨ splitterStack q = 258 ∨
      splitterStack q = 261 ∨ splitterStack q = 262 ∨ splitterStack q = 265) j
    rcases hrange with h | h | h | h | h | h
    · omega
    · exact hpending h
    · exact hheader h
    · exact hleft h
    · exact hright h
    · exact hcurrent h
  have hpairOff : ¬ ∃ j, pairStack j = i := by
    rintro ⟨j, rfl⟩
    have hrange := (by decide : ∀ q : Fin 5,
      (pairStack q).val < 256 ∨ pairStack q = 257 ∨ pairStack q = 258 ∨
      pairStack q = 261 ∨ pairStack q = 262) j
    rcases hrange with h | h | h | h | h
    · omega
    · exact hpending h
    · exact hheader h
    · exact hleft h
    · exact hright h
  cases he with
  | seq hsplit hpair =>
      cases hsplit with
      | call _ hfirst =>
          cases hpair with
          | call _ hsecond =>
              exact (lifted_trace_stack_frame SparseFrontierProgram.pushPairProgram
                (registers 4 (by decide)) pairStack hsecond i hpairOff).trans
                (lifted_trace_stack_frame DisjointBranchProgram.program
                  (registers 15 (by decide)) splitterStack hfirst i hsplitOff)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}


/-- The encoded core child agrees with the typed result literal by literal. -/
theorem childA_body {n : ℕ} (F S : RawCNF n) (H : List (SAT.Literal (Fin n))) :
    ExecCoreChildProgram.formulaCode
      (ExecCoreChildProgram.result (F.map (List.map Encoding.literalCode))
        (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode)) =
      SparseCountProgram.encodeBody (ExecCoreChildProgram.result F S H) := by
  rw [ExecCoreChildProgram.result_map Encoding.literalCode Encoding.literalCode_injective]
  rfl

theorem childB_body {n : ℕ} (F S : RawCNF n) (H : List (SAT.Literal (Fin n))) :
    ExecCoreChildProgram.formulaCode
      (DisjointBranchProgram.resultB SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode))
        (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode)) =
      SparseCountProgram.encodeBody (DisjointBranchProgram.resultB SAT.Literal.negate F S H) := by
  rw [DisjointBranchProgram.resultB_codes]
  rfl

theorem typed_branch_execution {n : ℕ} (d : SparseDFSProgram.Data)
    (F S : RawCNF n) (H : List (SAT.Literal (Fin n)))
    (hF : d.stacks 265 = SparseCountProgram.encodeBody F)
    (hH : d.stacks 9 = Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode))
    (hS : d.stacks 12 = SparseCountProgram.encodeBody S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume
      (F.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
      (H.map Encoding.literalCode)) ^ 2,
      ∃ e, Eval SparseDFSProgram.branch t d e ∧
        e.stacks 257 =
          ExecWorklistProgram.record (SparseCountProgram.encodeBody (ExecCoreChildProgram.result F S H)) ++
          (ExecWorklistProgram.record (SparseCountProgram.encodeBody
            (DisjointBranchProgram.resultB SAT.Literal.negate F S H)) ++ d.stacks 257) ∧
        e.stacks 258 = d.stacks 258 ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
        e.stacks 265 = [] ∧ e.stacks 259 = d.stacks 259 ∧
        e.stacks 260 = d.stacks 260 := by
  obtain ⟨t, ht, e, he, hout, hframe⟩ := SparseDFSProgram.branch_execution_from_state d
    (F.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
    (H.map Encoding.literalCode) hF hH hS hleft hright hclean
  rw [childA_body F S H, childB_body F S H] at hout
  exact ⟨t, ht, e, he, hout, hframe⟩


theorem finishVisit_boundary (threshold : List Bool) (s : Frontier n)
    (d : SparseDFSProgram.Data) (bound : ℕ)
    (ha : AfterVisit threshold s d) (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * 257 + 1, ∃ e,
      Eval SparseDFSProgram.finishVisit t d e ∧ Boundary threshold s e ∧
      (∀ i, 256 ≤ i.val → i ≠ 265 → e.stacks i = d.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled SparseDFSProgram.finishVisit 256 256) prefixSteps
          (d.withPC (some (compiled SparseDFSProgram.finishVisit 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
  obtain ⟨t, ht, e, he, hlow, hcurrent, hframe, hflag, hspace⟩ :=
    SparseDFSResource.finishVisit_execution_space d bound hbound
  refine ⟨t, ht, e, he, ?_, hframe, hspace⟩
  refine ⟨(hframe 257 (by decide) (by decide)).trans ha.pending,
    (hframe 258 (by decide) (by decide)).trans ha.header,
    (hframe 259 (by decide) (by decide)).trans ha.threshold_word,
    (hframe 260 (by decide) (by decide)).trans ha.total,
    (hframe 261 (by decide) (by decide)).trans ha.left_empty,
    (hframe 262 (by decide) (by decide)).trans ha.right_empty,
    (hframe 263 (by decide) (by decide)).trans ha.leaf_empty,
    hcurrent, hlow, ?_⟩
  rw [hflag, ha.pending]
  cases hp : s.pending <;> simp [pendingBytes, Encoding.encodeList]


theorem branch_after_selection {k c : ℕ} (threshold : List Bool)
    (node : Node n) (rest : List (Node n)) (total bound : ℕ)
    (H : List (SAT.Literal (Fin n))) (d : SparseDFSProgram.Data)
    (hv : Valid k node.formula)
    (hpriority : SparsePriorityProgram.RawPriority k node.formula
      (BinaryArithmetic.toNat threshold) c H)
    (hpending : d.stacks 257 = pendingBytes rest)
    (hheader : d.stacks 258 = Encoding.encodeNat n)
    (hthreshold : d.stacks 259 = threshold)
    (htotal : d.stacks 260 = binaryNat total)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hleaf : d.stacks 263 = [])
    (hF : d.stacks 265 = SparseCountProgram.encodeBody node.formula)
    (hH : d.stacks 9 = Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode))
    (hS : d.stacks 12 = SparseCountProgram.encodeBody
      (SparsePriorityProgram.selectedRaw node.formula c H))
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = [])
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    let S := SparsePriorityProgram.selectedRaw node.formula c H
    let V := ExecCoreChildProgram.inputVolume (node.formula.map (List.map Encoding.literalCode))
      (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode)
    let next : Frontier n :=
      ⟨⟨childA node.formula c H, node.depth + 1⟩ ::
        ⟨childB node.formula c H, node.depth + 1⟩ :: rest, total⟩
    ∃ t ≤ 621000 * V ^ 2, ∃ e,
      Eval SparseDFSProgram.branch t d e ∧
      Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧
      AfterVisit threshold next e ∧
      ∀ prefixSteps cfg, prefixSteps ≤ t →
        Trace (compiled SparseDFSProgram.branch 256 256) prefixSteps
          (d.withPC (some (compiled SparseDFSProgram.branch 256 256).entry)) cfg →
        ∀ i, (cfg.stacks i).length ≤
          max bound ((pendingBytes rest).length + (n + 1) + 620001 * V ^ 2) := by
  dsimp only
  let S := SparsePriorityProgram.selectedRaw node.formula c H
  have hproject := SparseDFSProgram.splitter_input_projection_of_clean d
    (node.formula.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
    (H.map Encoding.literalCode) hF hH hS hleft hright hclean
  obtain ⟨t, ht, e, he, hspace⟩ := SparseDFSResource.branch_execution_space d
    (d.regs ∘ SparseDFSProgram.registers 15 (by decide)) (d.stacks 257) (d.stacks 258)
    (node.formula.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
    (H.map Encoding.literalCode) bound hbound
  rw [← hproject, embedState_project _ _ d (SparseDFSProgram.registers 15 (by decide)).injective
    SparseDFSProgram.splitterStack.injective] at he hspace
  obtain ⟨u, _, f, hf, hout, hn, hl, hr, _, hm, hcount⟩ :=
    typed_branch_execution d node.formula S H hF hH hS hleft hright hclean
  have hfinal : f = e := Eval.final_unique 256 hf he
  subst f
  have h263 : e.stacks 263 = [] :=
    (SparseDFSResource.branch_preserves_other_high he 263 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hleaf
  refine ⟨t, ht, e, he, .branch node rest total c H hv hpriority, ?_, ?_⟩
  · refine ⟨?_, hn.trans hheader, hm.trans hthreshold, hcount.trans htotal, hl, hr, h263⟩
    rw [hout, hpending]
    simp only [pendingBytes_cons, childA, childB, S]
  · simpa only [hpending, hheader, Encoding.length_encodeNat] using hspace


/- Actual frontier boundary decoding. -/
open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSInvariantSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical space at an actual refined DFS boundary.

Raw clause order is retained in the serialized frontier. Normalized syntax
and the strictly ordered DFS depths bound that word; the count mass bounds
the canonical accumulator. The raw input, two setup words and every reserved
high port are charged independently of the semantic count invariant.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSInvariantSpace

open SparseDFSRefinement SparseDFSBoundarySpace

variable {n : ℕ}

/-- The selected core and family retain at most the actual input body bytes.
This controls their physical padding and framing, not only their cardinality. -/
theorem selected_payload_lengths {k c : ℕ} (F : RawCNF n)
    (H : List (SAT.Literal (Fin n)))
    (hcandidate : (c, H) ∈ SparsePriorityProgram.rawCandidates k F) :
    (Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode)).length ≤
        (SparseCountProgram.encodeBody F).length ∧
      (SparseCountProgram.encodeBody (SparsePriorityProgram.selectedRaw F c H)).length ≤
        (SparseCountProgram.encodeBody F).length := by
  obtain ⟨C, hC, _, hsub⟩ := SparsePriorityProgram.rawCandidate_spec k F c H hcandidate
  have hcore := EncodingLength.length_le_of_sublist Encoding.encodeNat
    (hsub.map Encoding.literalCode)
  have hmember := EncodingLength.length_le_of_sublist
    (Encoding.encodeList Encoding.encodeNat)
    ((List.singleton_sublist.mpr hC).map (List.map Encoding.literalCode))
  simp only [List.map_singleton, Encoding.length_encodeList_cons,
    Encoding.length_encodeList_nil] at hmember
  constructor
  · change _ ≤ (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      (F.map (List.map Encoding.literalCode))).length
    omega
  · exact EncodingLength.length_le_of_sublist (Encoding.encodeList Encoding.encodeNat)
      (List.filter_sublist.map (List.map Encoding.literalCode))

/-- All three simultaneous splitter inputs are bounded by one retained body.
The actual branch program still charges every copied and framed child. -/
theorem selected_inputVolume_le {k c : ℕ} (F : RawCNF n)
    (H : List (SAT.Literal (Fin n)))
    (hcandidate : (c, H) ∈ SparsePriorityProgram.rawCandidates k F) :
    ExecCoreChildProgram.inputVolume (F.map (List.map Encoding.literalCode))
      ((SparsePriorityProgram.selectedRaw F c H).map (List.map Encoding.literalCode))
      (H.map Encoding.literalCode) ≤ 4 * (SparseCountProgram.encodeBody F).length + 3 := by
  obtain ⟨hcore, hselected⟩ := selected_payload_lengths F H hcandidate
  change (SparseCountProgram.encodeBody (SparsePriorityProgram.selectedRaw F c H)).length +
    (SparseCountProgram.encodeBody F).length +
    2 * (Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode)).length + 3 ≤ _
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSInvariantSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

namespace BoundedEval
variable {command first second yes no : Code} {t u B : ℕ} {a b c : Data}

theorem final_bound (h : BoundedEval command t a b B) :
    ∀ i, (b.stacks i).length ≤ B :=
  h.space t _ le_rfl (compiled_trace h.eval 256 256)

theorem seq (h : BoundedEval first t a b B) (g : BoundedEval second u b c B) :
    BoundedEval (.seq first second) (t + u) a c B :=
  ⟨h.eval.seq g.eval, StructuredSpace.sequence_stack_bound h.eval g.eval 256 256 h.space g.space
    (compiled (.seq first second) 256 256) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 256 256)⟩

theorem ite_true {flag : Fin 80} (hf : a.regs flag = true)
    (h : BoundedEval yes t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_true hf h.eval, StructuredSpace.conditional_true_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

theorem ite_false {flag : Fin 80} (hf : a.regs flag = false)
    (h : BoundedEval no t a b B) : BoundedEval (.ite flag yes no) (t + 1) a b B :=
  ⟨.ite_false hf h.eval, StructuredSpace.conditional_false_stack_bound hf h.eval 256 256 h.space
    (compiled (.ite flag yes no) 256 256) (siteAddress (.ite flag yes no))
    (exitAddress (.ite flag yes no)) (compiled_site (.ite flag yes no) 256 256)⟩

end BoundedEval

variable {n : ℕ}

set_option maxHeartbeats 3200000 in
/-- All branch construction, failed selector scans, accumulation and cleanup
are part of the same actual body evaluation. No elapsed traversal time enters
its source-space bound. -/
theorem body_refinement_oai {k : ℕ} (threshold : List Bool) (leaf : Code)
    (node : Node n) (rest : List (Node n)) (total parameterBound leafTime bound : ℕ) (d : Data)
    (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hv : Valid k node.formula) (hb : Boundary threshold ⟨node :: rest, total⟩ d)
    (hdimension : BinaryArithmetic.toNat (d.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1))
    (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
    (hparameterLength : (d.stacks 264).length ≤ parameterBound)
    (hambientLength : (d.stacks 267).length ≤ n + 1)
    (hcount : total + rawCount node.formula ≤ 2 ^ n)
    (hbound : ∀ i, (d.stacks i).length ≤ bound)
    (hpop : n + 1 + (pendingBytes rest).length +
      11 * (SparseCountProgram.encodeBody node.formula).length + 13 ≤ bound)
    (hselect : (SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
      SparseSelectorRefinement.inputVolume node.formula threshold ^ 4 ≤ bound)
    (hbranch : (pendingBytes rest).length + (n + 1) +
      620001 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2 ≤ bound)
    (hadd : 100 * (n + 1) ≤ bound)
    (hleaf : LeafContract (n := n) k threshold parameterBound leaf leafTime bound) :
    ∃ next t, t ≤ visitTime k n (SparseCountProgram.encodeBody node.formula).length
        threshold.length leafTime bound ∧
      ∃ e, BoundedEval (body k leaf) t d e bound ∧
        Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧
        Boundary threshold next e ∧
        (∀ i, i ∈ ([256, 264, 266, 267] : List (Fin 1220)) → e.stacks i = d.stacks i) := by
  obtain ⟨a, hpa, hcurrent, hpending, hpf, hlow, _, _, _, hpspace⟩ :=
    popCurrent_boundary threshold node rest total d bound hb hbound
  have popEval : BoundedEval popCurrent
      (9 * (SparseCountProgram.encodeBody node.formula).length + 11) d a bound :=
    ⟨hpa, fun t c ht hc i => (hpspace t c ht hc i).trans (max_le hpop le_rfl)⟩
  obtain ⟨ts, hts, b, hsb, hsf, hmissing, hfound, hsspace⟩ :=
    SparseSelectorRefinement.selectCurrent_execution node.formula threshold a bound hk hM
      hv.width hv.literal_nodup hv.clause_nodup hcurrent
      ((hpf 259 (by decide) (by decide)).trans hb.threshold)
      (fun i hi => hlow i (by omega)) popEval.final_bound
  have selectEval : BoundedEval (selectCurrent k) ts a b bound :=
    ⟨hsb, fun t c ht hc i => (hsspace t c ht hc i).trans (max_le hselect le_rfl)⟩
  have highFrame (i : Fin 1220) (hi : 256 ≤ i.val) (hic : i ≠ 265) (hip : i ≠ 257) :
      b.stacks i = d.stacks i := by
    rw [hsf i (by intro h; subst i; omega) (by intro h; subst i; omega), hpf i hic hip]
  have bPending : b.stacks 257 = pendingBytes rest :=
    (hsf 257 (by decide) (by decide)).trans hpending
  have bCurrent : b.stacks 265 = SparseCountProgram.encodeBody node.formula :=
    (hsf 265 (by decide) (by decide)).trans hcurrent
  have bHeader := (highFrame 258 (by decide) (by decide) (by decide)).trans hb.header
  have bThreshold := (highFrame 259 (by decide) (by decide) (by decide)).trans hb.threshold
  have bTotal := (highFrame 260 (by decide) (by decide) (by decide)).trans hb.total
  have bLeft := (highFrame 261 (by decide) (by decide) (by decide)).trans hb.left_empty
  have bRight := (highFrame 262 (by decide) (by decide) (by decide)).trans hb.right_empty
  have bLeaf := (highFrame 263 (by decide) (by decide) (by decide)).trans hb.leaf_empty
  have finish (next : Frontier n) (c : Data) (visit : AfterVisit threshold next c)
      (hc : ∀ i, (c.stacks i).length ≤ bound) :=
    finishVisit_boundary threshold next c bound visit hc
  cases hflag : b.regs 23 with
  | false =>
    obtain ⟨hstacks, _, _, hnone, _, _⟩ := hmissing hflag
    have ready : LeafReady k threshold parameterBound node.formula b :=
      ⟨bCurrent, by rw [highFrame 264 (by decide) (by decide) (by decide)]; exact hdimension,
        by rw [highFrame 267 (by decide) (by decide) (by decide)]; exact hambient,
        by rw [highFrame 264 (by decide) (by decide) (by decide)]; exact hparameterLength,
        by rw [highFrame 267 (by decide) (by decide) (by decide)]; exact hambientLength,
        bHeader, bThreshold, bLeft, bRight, bLeaf,
        fun i hi => (congrFun hstacks i).trans (hlow i hi)⟩
    obtain ⟨tl, htl, c, leafEval, done⟩ := hleaf.execution node.formula b hv ready hnone selectEval.final_bound
    obtain ⟨ta, hta, f, hacc, hvisit, hacframe, haspace⟩ :=
      accumulate_after_leaf threshold node rest total bound c
        ((done.persistent 257 (by simp)).trans bPending)
        ((done.persistent 258 (by simp)).trans bHeader)
        ((done.persistent 259 (by simp)).trans bThreshold)
        ((done.persistent 260 (by simp)).trans bTotal)
        ((done.persistent 261 (by simp)).trans bLeft)
        ((done.persistent 262 (by simp)).trans bRight)
        done.count done.scratch hcount leafEval.final_bound
    have accEval : BoundedEval accumulate ta c f bound :=
      ⟨hacc, fun t c ht hc i => (haspace t c ht hc i).trans (max_le hadd le_rfl)⟩
    obtain ⟨tf, htf, e, hfe, hboundary, hfframe, hfspace⟩ :=
      finish ⟨rest, total + rawCount node.formula⟩ f hvisit accEval.final_bound
    have finishEval : BoundedEval finishVisit tf f e bound := ⟨hfe, hfspace⟩
    have whole := popEval.seq (selectEval.seq
      (((leafEval.seq accEval).ite_false (yes := branch) hflag).seq finishEval))
    have hm := Nat.le_max_right (621000 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2)
      (leafTime + 100 * (n + 1))
    refine ⟨⟨rest, total + rawCount node.formula⟩, _, ?_, e, whole,
      .leaf node rest total hnone, hboundary, ?_⟩
    · unfold visitTime SparseSelectorRefinement.inputVolume at *
      omega
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals rw [hfframe _ (by decide) (by decide),
        hacframe _ (by decide) (by decide) (by decide), done.persistent _ (by simp),
        highFrame _ (by decide) (by decide) (by decide)]
  | true =>
    obtain ⟨c, H, priority, _, hH, hS⟩ := hfound hflag
    have hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → b.stacks i = [] := by
      intro i hi hi9 hi12
      rw [hsf i hi9 hi12]
      exact hlow i (by omega)
    obtain ⟨tb, htb, f, hbf, transition, hvisit, hbspace⟩ :=
      branch_after_selection threshold node rest total bound H b hv priority bPending bHeader
        bThreshold bTotal bLeft bRight bLeaf bCurrent hH hS hclean selectEval.final_bound
    have hV := SparseDFSInvariantSpace.selected_inputVolume_le node.formula H priority.candidate
    have hVpow := Nat.pow_le_pow_left hV 2
    have branchEval : BoundedEval branch tb b f bound := by
      refine ⟨hbf, ?_⟩
      intro t c ht hc i
      apply (hbspace t c ht hc i).trans
      apply max_le le_rfl
      exact (Nat.add_le_add_left (Nat.mul_le_mul_left 620001 hVpow) _).trans hbranch
    obtain ⟨tf, htf, e, hfe, hboundary, hfframe, hfspace⟩ :=
      finish _ f hvisit branchEval.final_bound
    have finishEval : BoundedEval finishVisit tf f e bound := ⟨hfe, hfspace⟩
    have whole := popEval.seq (selectEval.seq
      ((branchEval.ite_true (no := .seq leaf accumulate) hflag).seq finishEval))
    have htime := htb.trans (Nat.mul_le_mul_left 621000 hVpow)
    have hm := Nat.le_max_left (621000 * (4 * (SparseCountProgram.encodeBody node.formula).length + 3) ^ 2)
      (leafTime + 100 * (n + 1))
    refine ⟨_, _, ?_, e, whole, transition, hboundary, ?_⟩
    · unfold visitTime SparseSelectorRefinement.inputVolume at *
      omega
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals rw [hfframe _ (by decide) (by decide),
        SparseDFSResource.branch_preserves_other_high hbf _ (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide),
        highFrame _ (by decide) (by decide) (by decide)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement_oai
