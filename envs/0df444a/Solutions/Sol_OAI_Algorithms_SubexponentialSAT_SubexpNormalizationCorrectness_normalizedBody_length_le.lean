-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody_length_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:58:24.751137+00:00
-- url     : https://prove2.me/submissions/48d916a7-bb0c-42e0-ba5c-9aca917af81d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u

variable {α : Type u} [DecidableEq α]

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem dedupClauses_subset (F : Formula α) : dedupClauses F ⊆ F := by
  intro C hC
  induction F with
  | nil => simp [dedupClauses] at hC
  | cons D F ih =>
    by_cases h : F.any (fun E => equivalent D E) = true
    · have htail : C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact List.mem_cons_of_mem D (ih htail)
    · have hsplit : C = D ∨ C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact hsplit.elim (fun h => h ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem D (ih h))

theorem absorb_subset (F : Formula α) : absorb F ⊆ F := by
  intro C hC
  exact dedupClauses_subset F (List.mem_filter.mp hC).1

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem normalize_literal_nodup (neg : α → α) (F : Formula α) :
    ∀ C ∈ normalize neg F, C.Nodup := by
  intro C hC
  have h1 := absorb_subset _ hC
  have h2 := (List.mem_filter.mp h1).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h2
  exact dedupLiterals_nodup D

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecQuantitativeSparsify
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quantitative bounds for the executable list sparsifier

This module instantiates the actual list search and depth-first worklist at the
arithmetically selected inverse budget. The finite-set view of each output is
used only for SAT semantics. Node visits are counted by the actual worklist;
they are not presented as primitive bit-machine transitions.
-/

namespace SubexponentialSAT.ExecQuantitativeSparsify

open SAT

variable {n : ℕ}

theorem literalList_codes (C : Clause (Fin n)) :
    (literalList C).map Encoding.literalCode = Encoding.clauseNumbers C := by
  let r := fun a b : Literal (Fin n) => Encoding.literalCode a ≤ Encoding.literalCode b
  let _ : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  let _ : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.literalCode_injective (le_antisymm h h')⟩
  unfold literalList Encoding.clauseNumbers
  let e : Literal (Fin n) ↪ ℕ := ⟨Encoding.literalCode, Encoding.literalCode_injective⟩
  have he : C.map e = C.image Encoding.literalCode := Finset.map_eq_image e C
  rw [← he]
  change (C.val.sort _).map Encoding.literalCode = (C.val.map Encoding.literalCode).sort _
  apply Multiset.map_sort
  intro a ha b hb
  rfl

theorem orderedClauses_codes (F : CNF (Fin n)) :
    (orderedClauses F).map Encoding.clauseNumbers = Encoding.cnfNumbers F := by
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  let _ : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  let _ : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  unfold orderedClauses Encoding.cnfNumbers
  let e : Clause (Fin n) ↪ List ℕ :=
    ⟨Encoding.clauseNumbers, Encoding.clauseNumbers_injective⟩
  have he : F.map e = F.image Encoding.clauseNumbers := Finset.map_eq_image e F
  rw [← he]
  change (F.val.sort _).map Encoding.clauseNumbers = (F.val.map Encoding.clauseNumbers).sort _
  apply Multiset.map_sort
  intro a ha b hb
  rfl

/-- The numerical payload of the executable input is exactly the canonical
payload specified by `Encoding`, including both sorting conventions. -/
theorem formulaList_codes (F : CNF (Fin n)) :
    (formulaList F).map (List.map Encoding.literalCode) = Encoding.cnfNumbers F := by
  simp only [formulaList, List.map_map, Function.comp_def, literalList_codes]
  exact orderedClauses_codes F

theorem encode_formulaList (F : CNF (Fin n)) :
    encodeRawFormula (formulaList F) = Encoding.encodeCNFBody F := by
  rw [encodeRawFormula, formulaList_codes]
  rfl

end SubexponentialSAT.ExecQuantitativeSparsify

end OAI.Algorithms
end

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem dedupLiterals_eq_of_nodup (C : Clause α) (hC : C.Nodup) : dedupLiterals C = C := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hC
      have h : ¬ contains x xs = true := by simpa only [contains_true] using hx
      simp only [dedupLiterals, ite_eq_right h, ih hxs]

theorem cleanLiterals_eq_of_nodup (F : Formula α) (hF : ∀ C ∈ F, C.Nodup) :
    cleanLiterals F = F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [cleanLiterals, List.map_cons]
      rw [dedupLiterals_eq_of_nodup C (hF C (by simp))]
      congr 1
      exact ih (fun D hD => hF D (by simp [hD]))

@[simp] theorem cleanLiterals_normalize (neg : α → α) (F : Formula α) :
    cleanLiterals (normalize neg F) = normalize neg F :=
  cleanLiterals_eq_of_nodup _ (normalize_literal_nodup neg F)

/-- The extra pass in the typed worklist does not alter order or multiplicity. -/
theorem normalizedInput_eq_normalize {n : ℕ}
    (F : Formula (SAT.Literal (Fin n))) :
    ExecSparsifyWorklist.normalizedInput F = normalize SAT.Literal.negate F := by
  exact cleanLiterals_normalize SAT.Literal.negate F

/-- Exact encoded normalization, including last-occurrence choices and order. -/
theorem normalize_literalCode {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    normalize SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode)) =
      (normalize SAT.Literal.negate F).map (List.map Encoding.literalCode) :=
  normalize_map Encoding.literalCode Encoding.literalCode_injective
    SAT.Literal.negate SubexpFrontend.negateCode SubexpFrontend.literalCode_negate F

/-- This is the list-level interface consumed by the actual normalizer. -/
theorem normalizedInput_literalCode {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    (ExecSparsifyWorklist.normalizedInput F).map (List.map Encoding.literalCode) =
      normalize SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode)) := by
  rw [normalizedInput_eq_normalize, normalize_literalCode]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

open BitProgram StructuredCalls

theorem encoded_dedup_length_le (records : List (List Bool)) :
    (Encoding.encodeList id (ExecCNF.dedupLiterals records)).length ≤
      (Encoding.encodeList id records).length := by
  induction records with
  | nil => rfl
  | cons bits rest ih =>
      unfold ExecCNF.dedupLiterals
      split
      · simp only [Encoding.length_encodeList_cons, id_eq]
        omega
      · simpa only [Encoding.length_encodeList_cons, id_eq] using
          Nat.add_le_add_left ih (2 * bits.length + 2)

theorem dedup_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    ExecCNF.dedupLiterals (xs.map f) = (ExecCNF.dedupLiterals xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hm : ExecCNF.contains (f x) (xs.map f) = true ↔
          ExecCNF.contains x xs = true := by
        rw [ExecCNF.contains_true, ExecCNF.contains_true, List.mem_map]
        constructor
        · rintro ⟨y, hy, h⟩
          exact hf h ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      by_cases h : ExecCNF.contains x xs = true
      · have h' := hm.mpr h
        simp [ExecCNF.dedupLiterals, h, h', ih]
      · have h' : ExecCNF.contains (f x) (xs.map f) ≠ true := fun hx => h (hm.mp hx)
        simp [ExecCNF.dedupLiterals, h, h', ih]

theorem encode_nat_records (xs : List ℕ) :
    Encoding.encodeList id (xs.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCleanLiteralsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clausewise literal cleanup

Each framed clause is decoded, passed to the fixed literal-deduplication
program, and framed again. An outer record reversal restores clause order.
The finite control is independent of the input formula and its clause sizes.
-/

namespace SubexponentialSAT.ExecCleanLiteralsProgram

open BitProgram StructuredCalls

theorem clauseCode_dedup_length_le (clause : List ℕ) :
    (clauseCode (ExecCNF.dedupLiterals clause)).length ≤ (clauseCode clause).length := by
  have h := ExecLiteralDedupProgram.encoded_dedup_length_le (clause.map Encoding.encodeNat)
  rw [ExecLiteralDedupProgram.dedup_map Encoding.encodeNat Encoding.encodeNat_injective,
    ExecLiteralDedupProgram.encode_nat_records, ExecLiteralDedupProgram.encode_nat_records] at h
  exact h

theorem cleaned_length_le (formula : List (List ℕ)) :
    (formulaCode (ExecCNF.cleanLiterals formula)).length ≤ (formulaCode formula).length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have h := clauseCode_dedup_length_le clause
      change (Encoding.encodeList clauseCode (ExecCNF.cleanLiterals rest)).length ≤
        (Encoding.encodeList clauseCode rest).length at ih
      simp only [formulaCode, ExecCNF.cleanLiterals, List.map_cons, Encoding.length_encodeList_cons]
      change (Encoding.encodeList clauseCode (rest.map ExecCNF.dedupLiterals)).length ≤
        (Encoding.encodeList clauseCode rest).length at ih
      omega

end SubexponentialSAT.ExecCleanLiteralsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded-clause tautology testing

The outer iterator reads unary literal records. For each literal, a concrete
program builds its opposite's query, copies the preserved clause, and runs the
proved encoded membership program. All data-dependent repetition is in those
finite programs and the record iterator.
-/

namespace SubexponentialSAT.SubexpTautologyProgram

open BitProgram StructuredCalls

theorem encodedClause_records (C : List ℕ) :
    encodedClause C = Encoding.encodeList id (literalRecords C) := by
  induction C with
  | nil => rfl
  | cons c C ih => simpa [encodedClause, literalRecords, Encoding.encodeList] using ih

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

open BitProgram StructuredCalls

theorem decodeFields_literalRecords (C : List ℕ) :
    decodeFields (SubexpTautologyProgram.literalRecords C) = some C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    change decodeFields (C.map Encoding.encodeNat) = some C at ih
    simp [SubexpTautologyProgram.literalRecords, decodeFields, ih]

@[simp] theorem decodeClause_encodedClause (C : List ℕ) :
    decodeClause (SubexpTautologyProgram.encodedClause C) = some C := by
  rw [SubexpTautologyProgram.encodedClause_records]
  change (do
    let (fields, rest) ← ProgramEncoding.readRecords
      (ProgramEncoding.encodeRecords (SubexpTautologyProgram.literalRecords C))
    if rest.isEmpty then decodeFields fields else none) = some C
  simp [decodeFields_literalRecords]

@[simp] theorem keepClause_encodedClause (C : List ℕ) :
    keepClause (SubexpTautologyProgram.encodedClause C) =
      !(ExecCNF.tautology SubexpFrontend.negateCode C) := by
  simp [keepClause]

theorem encodedFormula_records (F : List (List ℕ)) :
    encodedFormula F = Encoding.encodeList id (formulaRecords F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [encodedFormula, formulaRecords, Encoding.encodeList] using ih

theorem filtered_formulaRecords (F : List (List ℕ)) :
    (formulaRecords F).filter keepClause =
      formulaRecords (ExecCNF.removeTautologies SubexpFrontend.negateCode F) := by
  change (F.map SubexpTautologyProgram.encodedClause).filter keepClause =
    (F.filter (fun C => !(ExecCNF.tautology SubexpFrontend.negateCode C))).map
      SubexpTautologyProgram.encodedClause
  induction F with
  | nil => rfl
  | cons C F ih =>
    cases h : !(ExecCNF.tautology SubexpFrontend.negateCode C) <;>
      simp [ h, ih]

theorem encoded_filter_length_le (records : List (List Bool)) :
    (Encoding.encodeList id (records.filter keepClause)).length ≤
      (Encoding.encodeList id records).length := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
    cases h : keepClause bits <;>
      simp [ h, Encoding.length_encodeList_cons] <;> omega

theorem filtered_length_le (F : List (List ℕ)) :
    (encodedFormula (ExecCNF.removeTautologies SubexpFrontend.negateCode F)).length ≤
      (encodedFormula F).length := by
  rw [encodedFormula_records, ← filtered_formulaRecords, encodedFormula_records]
  exact encoded_filter_length_le _

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Actual literal cleanup followed by tautology removal

This is a fixed program on the original declared variable universe. Its two
stages use the same input/output port and restore empty work stacks. The exact
list order and the length bound are retained for subsequent clause absorption.
-/

namespace SubexponentialSAT.SubexpNormalizationPrefixProgram

open BitProgram StructuredCalls

theorem preprocess_length_le (F : List (List ℕ)) :
    (formulaCode (preprocess F)).length ≤ (formulaCode F).length :=
  (SubexpTautologyFilterProgram.filtered_length_le (ExecCNF.cleanLiterals F)).trans
    (ExecCleanLiteralsProgram.cleaned_length_le F)

end SubexponentialSAT.SubexpNormalizationPrefixProgram

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

theorem normalize_length_le (F : List (List ℕ)) :
    (formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F)).length ≤
      (formulaCode F).length :=
  (ExecCNF.length_encodeList_absorb_le _ _).trans
    (SubexpNormalizationPrefixProgram.preprocess_length_le F)

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationCorrectness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Canonical-input correctness of the encoded normalizer

The program consumes the body left by the separate header parser. The output
is exactly the typed sparsifier's ordered normalized input. The declared
variable universe is retained, so unused coordinates require no renaming.
-/

namespace SubexponentialSAT.SubexpNormalizationCorrectness

open BitProgram
open SubexpNormalizationProgram (Data Ready formulaCode )

theorem canonical_body_eq {n : ℕ} (F : SAT.CNF (Fin n)) :
    formulaCode ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode)) =
      Encoding.encodeCNFBody F :=
  ExecQuantitativeSparsify.encode_formulaList F

theorem normalizedBody_length_le_oai {n : ℕ} (F : SAT.CNF (Fin n)) :
    (normalizedBody F).length ≤ (Encoding.encodeCNFBody F).length := by
  have h := SubexpNormalizationProgram.normalize_length_le
    ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode))
  rw [← ExecCNFCodeTransport.normalizedInput_literalCode, canonical_body_eq] at h
  exact h

end SubexponentialSAT.SubexpNormalizationCorrectness

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody_length_le_oai := @OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness.normalizedBody_length_le_oai
