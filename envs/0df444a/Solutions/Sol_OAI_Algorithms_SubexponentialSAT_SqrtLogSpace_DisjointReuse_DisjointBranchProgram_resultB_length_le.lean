-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:57:23.7092+00:00
-- url     : https://prove2.me/submissions/4a791c64-32a6-47f8-b044-8d5cbc184d1e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSemanticHelpers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact list identities used when composing executable CNF filters. -/
namespace SubexponentialSAT.Encoding
universe u

/-- Filtering discards complete frames; this bound needs no property of the
payload encoder. -/
theorem length_encodeList_filter_le {α : Type u} (enc : α → List Bool)
    (keep : α → Bool) (values : List α) :
    (encodeList enc (values.filter keep)).length ≤ (encodeList enc values).length := by
  induction values with
  | nil => simp
  | cons a values ih =>
    cases h : keep a with
    | false =>
      simp [ h, length_encodeList_cons] ; omega
    | true =>
      simp [ h, length_encodeList_cons] ; omega

end SubexponentialSAT.Encoding

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

/-- Clause deduplication retains a subsequence of the original payloads. -/
theorem length_encodeList_dedupClauses_le (enc : Clause α → List Bool) (F : Formula α) :
    (Encoding.encodeList enc (dedupClauses F)).length ≤
      (Encoding.encodeList enc F).length := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega

/-- Absorption cannot increase the serialized formula length, even when the
payload encoder uses unequal-length clause encodings. -/
theorem length_encodeList_absorb_le (enc : Clause α → List Bool) (F : Formula α) :
    (Encoding.encodeList enc (absorb F)).length ≤
      (Encoding.encodeList enc F).length := by
  unfold absorb
  exact (Encoding.length_encodeList_filter_le enc _ _).trans
    (length_encodeList_dedupClauses_le enc F)

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

theorem encodeList_id_map {α : Type*} (enc : α → List Bool) (xs : List α) :
    Encoding.encodeList id (xs.map enc) = Encoding.encodeList enc xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-code interfaces for the fixed encoded relation scanner. -/
namespace SubexponentialSAT.ExecClauseRelationScan
open BitProgram StructuredCalls

theorem encodeClause_codes (C : List ℕ) :
    encodeClause (codeClause C) = Encoding.encodeList Encoding.encodeNat C :=
  ExecClauseRelationsProgram.encodeList_id_map _ _

theorem encodeFormula_codes (F : List (List ℕ)) :
    encodeFormula (codeFormula F) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp only [encodeFormula, codeFormula, List.map_cons, Encoding.encodeList,
      encodeClause_codes]
    exact congrArg (fun tail => true :: Encoding.frame
      (Encoding.encodeList Encoding.encodeNat C) ++ tail) ih

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNegatedQueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving complemented-literal queries

The clause iterator supplies a literal's unary word in reverse order. This
fixed program preserves that query on stack 0 and writes the reversed unary
word for the opposite literal on stack 1. Stacks 2 and 3 are empty workspaces
on entry and return. All costs below count actual finite-program transitions.
-/

namespace SubexponentialSAT.SubexpNegatedQueryProgram

open BitProgram StructuredCalls
open ParserProgram (pair)

theorem negateCode_le (c : ℕ) : SubexpFrontend.negateCode c ≤ c + 1 := by
  unfold SubexpFrontend.negateCode
  split <;> omega

end SubexponentialSAT.SubexpNegatedQueryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

theorem clauseCode_fields (C : List ℕ) :
    ExecClauseRelationScan.encodeClause (C.map Encoding.encodeNat) =
      ExecCleanLiteralsProgram.clauseCode C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    simpa [ExecClauseRelationScan.encodeClause, ExecCleanLiteralsProgram.clauseCode,
      Encoding.encodeList] using ih

theorem formulaCode_fields (F : List (List ℕ)) :
    ExecClauseRelationScan.encodeFormula (bitFields F) = formulaCode F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simpa [ExecClauseRelationScan.encodeFormula, bitFields, formulaCode,
      ExecCleanLiteralsProgram.formulaCode, Encoding.encodeList, clauseCode_fields] using ih

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual stable subtraction of a core from an encoded clause. Membership
tests, core copies, record emission, and order restoration use finite code. -/
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

theorem result_encoded_length_le {α : Type*} [DecidableEq α]
    (enc : α → List Bool) (C H : List α) :
    (Encoding.encodeList enc (result C H)).length ≤ (Encoding.encodeList enc C).length :=
  Encoding.length_encodeList_filter_le enc _ C

end SubexponentialSAT.ExecPetalProgram

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

theorem petals_length_le (selected : Formula) (H : Clause) :
    (encodeFormula (petals selected H)).length ≤ (encodeFormula selected).length := by
  induction selected with
  | nil => exact le_rfl
  | cons C F ih =>
    have hc := ExecPetalProgram.result_encoded_length_le id C H
    change (encodeClause (ExecPetalProgram.result C H)).length ≤ (encodeClause C).length at hc
    simp only [petals, List.map_cons, encodeFormula, Encoding.length_encodeList_cons] at ih ⊢
    omega

theorem formulaCode_encoding (F : List (List ℕ)) :
    formulaCode F = Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F := by
  rw [← ExecClauseRelationScan.encodeFormula_codes]
  exact (SubexpNormalizationProgram.formulaCode_fields F).symm

theorem petals_codes (selected : List (List ℕ)) (H : List ℕ) :
    petals (ExecClauseRelationScan.codeFormula selected) (ExecClauseRelationScan.codeClause H) =
      ExecClauseRelationScan.codeFormula (petals selected H) := by
  simpa [petals, ExecPetalProgram.result, ExecClauseRelationScan.codeFormula,
    ExecClauseRelationScan.codeClause] using
    ExecCNFCodeTransport.petal_family_map Encoding.encodeNat Encoding.encodeNat_injective selected H

theorem encode_append_length_le {α : Type*} (enc : α → List Bool) (xs ys : List α) :
    (Encoding.encodeList enc (xs ++ ys)).length ≤
      (Encoding.encodeList enc xs).length + (Encoding.encodeList enc ys).length := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih =>
    simp only [List.cons_append, Encoding.length_encodeList_cons]
    omega

theorem petals_code_length_le (selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (petals selected H)).length ≤ (formulaCode selected).length := by
  have h := petals_length_le (ExecClauseRelationScan.codeFormula selected)
    (ExecClauseRelationScan.codeClause H)
  simpa only [formulaCode_encoding, petals_codes,
    ExecClauseRelationScan.encodeFormula_codes] using h

theorem prepared_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length + 1 ≤
      inputVolume F selected H := by
  have hp := petals_code_length_le selected H
  have he := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at he
  have ha := encode_append_length_le clauseCode (petals selected H) (ExecCNF.eraseClauses F selected)
  change (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length ≤
    (formulaCode (petals selected H)).length + (formulaCode (ExecCNF.eraseClauses F selected)).length at ha
  unfold inputVolume
  omega

theorem result_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (result F selected H)).length + 1 ≤ inputVolume F selected H := by
  have ha := ExecCNF.length_encodeList_absorb_le clauseCode
    (petals selected H ++ ExecCNF.eraseClauses F selected)
  change (formulaCode (result F selected H)).length ≤
    (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length at ha
  exact (Nat.add_le_add_right ha 1).trans (prepared_length_le F selected H)

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete negated singleton generation for the disjoint B child.
The fixed routine consumes a unary literal-record list on stack 0 and prepends
its negated singleton clauses to the encoded formula on stack 2. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram

open BitProgram StructuredCalls

theorem output_length_le (H : List ℕ) (F : List (List ℕ)) :
    (formulaCode (units H ++ F)).length ≤
      (formulaCode F).length + 8 * (clauseCode H).length := by
  induction H generalizing F with
  | nil => simp [units]
  | cons c H ih =>
      have hneg : (Encoding.encodeNat (SubexpFrontend.negateCode c)).length ≤
          (Encoding.encodeNat c).length + 1 := by
        simpa only [Encoding.length_encodeNat] using
          Nat.add_le_add_right (SubexpNegatedQueryProgram.negateCode_le c) 1
      have hrec := ih ([SubexpFrontend.negateCode c] :: F)
      have heq : units (c :: H) ++ F = units H ++ ([SubexpFrontend.negateCode c] :: F) := by
        simp [units, List.reverse_cons, List.map_append, List.append_assoc]
      rw [heq]
      simp only [formulaCode, Encoding.length_encodeList_cons] at hrec ⊢
      simp only [clauseCode, SubexpTautologyProgram.encodedClause,
        Encoding.length_encodeList_cons, Encoding.length_encodeList_nil] at hrec ⊢
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

theorem preparedB_volume_le (F S : List (List ℕ)) (H : List ℕ) :
    ExecPetalChildProgram.inputVolume
        (negatedUnits SubexpFrontend.negateCode H ++ F) S H ≤
      5 * ExecCoreChildProgram.inputVolume F S H := by
  have h := NegatedCoreProgram.output_length_le H F
  change (ExecCoreChildProgram.formulaCode
      (negatedUnits SubexpFrontend.negateCode H ++ F)).length ≤
    (ExecCoreChildProgram.formulaCode F).length +
      8 * (ExecCoreChildProgram.clauseCode H).length at h
  unfold ExecPetalChildProgram.inputVolume ExecCoreChildProgram.inputVolume
  dsimp only [ExecPetalChildProgram.formulaCode, ExecPetalChildProgram.clauseCode,
    ExecCoreChildProgram.formulaCode, ExecCoreChildProgram.clauseCode] at h ⊢
  omega

theorem resultB_length_le_oai (F S : List (List ℕ)) (H : List ℕ) :
    (ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)).length ≤
      5 * ExecCoreChildProgram.inputVolume F S H := by
  have h := ExecPetalChildProgram.result_length_le
    (negatedUnits SubexpFrontend.negateCode H ++ F) S H
  exact (Nat.le_add_right _ 1).trans (h.trans (preparedB_volume_le F S H))

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.resultB_length_le_oai
