-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:57:53.697994+00:00
-- url     : https://prove2.me/submissions/32278909-10e1-4d88-abef-867c33be0e16

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S064

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

variable {V : Type u}

variable [DecidableEq V]

section Decidable

theorem normalize_not_tautology {F : CNF V} {C : Clause V} (hC : C ∈ normalize F) :
    ¬ C.IsTautology :=
  (Finset.mem_filter.mp (absorb_subset (removeTautologies F) hC)).2

end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem literalCode_lt {n : ℕ} (l : SAT.Literal (Fin n)) : literalCode l < 2 * n := by
  have hv := l.variable.isLt
  cases hp : l.positive <;> simp [literalCode, hp] ; omega

theorem mem_clauseNumbers_lt {n : ℕ} {C : SAT.Clause (Fin n)} {a : ℕ}
    (h : a ∈ clauseNumbers C) : a < 2 * n := by
  have hi : a ∈ C.image literalCode := by simpa [clauseNumbers] using h
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hi
  exact literalCode_lt l

theorem length_encodeClause_upper {n : ℕ} (C : SAT.Clause (Fin n)) :
    (encodeList encodeNat (clauseNumbers C)).length ≤ 1 + (4 * n + 4) * C.card := by
  have h := length_encodeList_upper encodeNat (clauseNumbers C) (2 * n + 1)
    (fun a ha => by rw [length_encodeNat]; have := mem_clauseNumbers_lt ha; omega)
  have hc : 2 * (2 * n + 1) + 2 = 4 * n + 4 := by omega
  simpa only [length_clauseNumbers, hc] using h

/-- A polynomial upper bound for the actual encoding, without any semantic oracle. -/
theorem formulaBitLength_upper {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    formulaBitLength F ≤ n + 2 + (4 + (8 * n + 8) * k) * F.card := by
  have hp : ∀ as ∈ cnfNumbers F,
      (encodeList encodeNat as).length ≤ 1 + (4 * n + 4) * k := by
    intro as has
    have hi : as ∈ F.image clauseNumbers := by simpa [cnfNumbers] using has
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hi
    exact (length_encodeClause_upper C).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hw C hC)) _)
  have h := length_encodeList_upper (encodeList encodeNat) (cnfNumbers F)
    (1 + (4 * n + 4) * k) hp
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change (encodeCNFBody F).length ≤ _ at h
  calc
    n + 1 + (encodeCNFBody F).length
        ≤ n + 1 + (1 + (2 * (1 + (4 * n + 4) * k) + 2) * F.card) :=
          Nat.add_le_add_left h _
    _ = n + 2 + (4 + (8 * n + 8) * k) * F.card := by ring

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SunflowerBranch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal-set sunflower branching

Concrete CNF children and their semantic union, together with the absorption
invariants used by the cumulative-insertion argument. Opposite polarities are
distinct literals; no variable-disjointness premise is used.
-/

namespace SubexponentialSAT.SunflowerBranch
open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

theorem antichain_normalize (F : CNF V) : Antichain (normalize F) :=
  antichain_absorb _

end SubexponentialSAT.SunflowerBranch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem dedupLiterals_length_le (C : Clause α) : (dedupLiterals C).length ≤ C.length := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih.trans (Nat.le_succ _)
    · simpa [dedupLiterals, h] using Nat.succ_le_succ ih

theorem dedupClauses_map_nodup (F : Formula α) : ((dedupClauses F).map clauseSet).Nodup := by
  induction F with
  | nil => simp [dedupClauses]
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simpa [dedupClauses, h] using ih
    · simp only [dedupClauses, ite_eq_right h, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hm
      have hmem : clauseSet C ∈ formulaSet (dedupClauses F) := by
        exact List.mem_toFinset.mpr hm
      rw [formulaSet_dedupClauses] at hmem
      exact h ((any_equivalent_true C F).mpr hmem)

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem formulaSet_filter (F : Formula α) (p : Clause α → Bool)
    (q : Finset α → Prop) [DecidablePred q]
    (hp : ∀ C, p C = true ↔ q (clauseSet C)) :
    formulaSet (F.filter p) = (formulaSet F).filter q := by
  ext C
  simp only [mem_formulaSet, Finset.mem_filter]
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hD, htest⟩ := List.mem_filter.mp hD
    exact ⟨⟨D, hD, rfl⟩, (hp D).mp htest⟩
  · rintro ⟨⟨D, hD, rfl⟩, hq⟩
    exact ⟨D, List.mem_filter.mpr ⟨hD, (hp D).mpr hq⟩, rfl⟩

@[simp] theorem formulaSet_removeTautologies (neg : α → α) (F : Formula α) :
    formulaSet (removeTautologies neg F) =
      (formulaSet F).filter (fun C => ¬ ∃ x ∈ C, neg x ∈ C) := by
  apply formulaSet_filter
  intro C
  simp only [not_true_iff, tautology_true]

@[simp] theorem formulaSet_absorb (F : Formula α) :
    formulaSet (absorb F) =
      (formulaSet F).filter (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C) := by
  change formulaSet ((dedupClauses F).filter _) = _
  rw [formulaSet_filter (dedupClauses F) _
    (fun C => ¬ ∃ D ∈ formulaSet F, D ⊂ C)]
  · rw [formulaSet_dedupClauses]
  · intro C
    simp only [not_true_iff, any_strictSubset_true]

@[simp] theorem formulaSet_eraseClauses (F S : Formula α) :
    formulaSet (eraseClauses F S) = formulaSet F \ formulaSet S := by
  unfold eraseClauses
  rw [formulaSet_filter F _ (fun C => C ∉ formulaSet S)]
  · ext C
    simp
  · intro C
    simp only [not_true_iff, any_equivalent_true]

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

section SAT
variable {V : Type u} [DecidableEq V]

@[simp] theorem absorb_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (absorb F) = SubexponentialSAT.SAT.absorb (formulaSet F) := formulaSet_absorb F

@[simp] theorem normalize_set (F : Formula (SubexponentialSAT.SAT.Literal V)) :
    formulaSet (normalize SubexponentialSAT.SAT.Literal.negate F) = SubexponentialSAT.SAT.normalize (formulaSet F) := by
  simp only [normalize, absorb_set, formulaSet_removeTautologies, formulaSet_cleanLiterals]
  rfl

end SAT
end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem absorb_map_nodup (F : Formula α) : ((absorb F).map clauseSet).Nodup := by
  apply List.Sublist.nodup _ (dedupClauses_map_nodup F)
  exact List.Sublist.map clauseSet List.filter_sublist

theorem normalize_map_nodup (neg : α → α) (F : Formula α) :
    ((normalize neg F).map clauseSet).Nodup := absorb_map_nodup _

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

@[simp] theorem dedupClauses_length (F : Formula α) :
    (dedupClauses F).length = (formulaSet F).card := by
  have h := List.toFinset_card_of_nodup (dedupClauses_map_nodup F)
  change (formulaSet (dedupClauses F)).card = _ at h
  rw [formulaSet_dedupClauses, List.length_map] at h
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

theorem formulaList_width (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    ExecSunflowerSearch.RawWidthAtMost k (formulaList F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  simpa only [literalList_length] using hF D ((mem_orderedClauses F D).mp hD)

end SubexponentialSAT.ExecQuantitativeSparsify

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

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CNFNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Raw input normalization for the frozen counting manuscript, lines 1758–1762.
The ambient type remains `Fin n` throughout, including unused variables.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

variable {n : ℕ}

theorem formulaSet_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) : SAT.WidthAtMost k (ExecCNF.formulaSet F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  exact D.toFinset_card_le.trans (h D hD)

theorem normalize_width_le (F : RawCNF n) {k : ℕ}
    (h : ∀ C ∈ F, C.length ≤ k) :
    ∀ C ∈ ExecCNF.normalize SAT.Literal.negate F, C.length ≤ k := by
  intro C hC
  have h₁ := ExecCNF.absorb_subset _ hC
  have h₂ := (List.mem_filter.mp h₁).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h₂
  exact (ExecCNF.dedupLiterals_length_le D).trans (h D hD)

private theorem encodeList_length_perm {α : Type*} (enc : α → List Bool)
    {as bs : List α} (h : as.Perm bs) :
    (Encoding.encodeList enc as).length = (Encoding.encodeList enc bs).length := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Encoding.length_encodeList_cons, ih]
  | swap a b as => simp only [Encoding.length_encodeList_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem encodeList_length_map_congr {α β γ : Type*}
    (enc₁ : β → List Bool) (enc₂ : γ → List Bool) (f : α → β) (g : α → γ)
    (as : List α) (h : ∀ a ∈ as, (enc₁ (f a)).length = (enc₂ (g a)).length) :
    (Encoding.encodeList enc₁ (as.map f)).length =
      (Encoding.encodeList enc₂ (as.map g)).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, Encoding.length_encodeList_cons]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- Sorting literals and clauses changes their order but not the serialized size.
The hypotheses exclude both literal repetitions and semantically duplicate clauses. -/
theorem encodeRawCNFBody_length_eq (F : RawCNF n)
    (hC : ∀ C ∈ F, C.Nodup) (hF : (F.map ExecCNF.clauseSet).Nodup) :
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      (F.map (List.map Encoding.literalCode))).length =
      (Encoding.encodeCNFBody (ExecCNF.formulaSet F)).length := by
  have hclause (C : List (SAT.Literal (Fin n))) (h : C ∈ F) :
      (C.map Encoding.literalCode).Perm (Encoding.clauseNumbers (ExecCNF.clauseSet C)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      ((hC C h).map Encoding.literalCode_injective) (Finset.sort_nodup _ _)
    ext i
    simp [ExecCNF.clauseSet]
  have hformula : ((F.map ExecCNF.clauseSet).map Encoding.clauseNumbers).Perm
      (Encoding.cnfNumbers (ExecCNF.formulaSet F)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      (hF.map Encoding.clauseNumbers_injective) (Finset.sort_nodup _ _)
    ext C
    simp [ExecCNF.formulaSet]
  calc
    (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
        (F.map (List.map Encoding.literalCode))).length =
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
          ((F.map ExecCNF.clauseSet).map Encoding.clauseNumbers)).length := by
      rw [List.map_map]
      apply encodeList_length_map_congr
      intro C h
      exact encodeList_length_perm Encoding.encodeNat (hclause C h)
    _ = (Encoding.encodeCNFBody (ExecCNF.formulaSet F)).length :=
      encodeList_length_perm _ hformula

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriority
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: smallest-width, largest-core selection and marked degrees. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority

open OAI.Algorithms.SubexponentialSAT.SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

/-- A coarse polynomial clause bound, sufficient for the search cost. -/
theorem clause_card_le (F : CNF (Fin n)) (k : ℕ)
    (hF : ∀ C ∈ F, C.card ≤ k) : F.card ≤ (k + 1) * (2 * n + 1) ^ k := by
  let enc := fun C : Clause (Fin n) => C.image Encoding.literalCode
  have hinj : Function.Injective enc := Finset.image_injective Encoding.literalCode_injective
  have hsub : F.image enc ⊆ (Finset.range (k + 1)).biUnion
      (fun j => (Finset.range (2 * n)).powersetCard j) := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    refine Finset.mem_biUnion.mpr ⟨D.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (hF D hD)), ?_⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Encoding.literalCode_lt l)
    · exact Finset.card_image_of_injective _ Encoding.literalCode_injective
  calc
    F.card = (F.image enc).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.range (k + 1)).biUnion
        (fun j => (Finset.range (2 * n)).powersetCard j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (k + 1)).card * (2 * n + 1) ^ k := by
      apply Finset.card_biUnion_le_card_mul
      intro j hj
      simp only [Finset.card_powersetCard, Finset.card_range]
      calc
        (2 * n).choose j ≤ (2 * n) ^ j := Nat.choose_le_pow _ _
        _ ≤ (2 * n + 1) ^ j := Nat.pow_le_pow_left (by omega) _
        _ ≤ (2 * n + 1) ^ k := Nat.pow_le_pow_right (by omega)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = (k + 1) * (2 * n + 1) ^ k := by rw [Finset.card_range]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: the mathematical depth-first transition and its count invariant.

The transition below specifies a leaf operation by its exact count. It is not a
primitive implementation of that operation, and no bit-time bound is asserted.
The pending list retains the current node and one sibling per branch on the
active path; completed leaves are discarded immediately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

theorem formulaBitLength_le (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    Encoding.formulaBitLength F ≤ formulaBound n k :=
  (Encoding.formulaBitLength_upper F hF).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (SparsePriority.clause_card_le F k hF)) _)

theorem encodeBody_length_le (F : RawCNF n) (k : ℕ)
    (hC : ∀ C ∈ F, C.Nodup) (hF : (F.map ExecCNF.clauseSet).Nodup)
    (hwidth : WidthAtMost k (ExecCNF.formulaSet F)) :
    (encodeBody F).length ≤ formulaBound n k := by
  have h := formulaBitLength_le (ExecCNF.formulaSet F) k hwidth
  rw [Encoding.formulaBitLength_eq] at h
  rw [encodeBody, encodeRawCNFBody_length_eq F hC hF]
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CanonicalFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual canonical normalizer emits the ordered body consumed by the
disjoint DFS. Both sides retain the declared ambient variable universe. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem canonical_normalized_formula {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedFormula F =
      ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F) :=
  ExecCNFCodeTransport.normalizedInput_eq_normalize _

theorem canonical_normalized_body {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedBody F =
      DisjointReuse.SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate
        (ExecQuantitativeSparsify.formulaList F)) := by
  unfold SubexpNormalizationCorrectness.normalizedBody
  rw [canonical_normalized_formula]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
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


theorem Valid.normalize (F : RawCNF n) {k : ℕ} (hw : ∀ C ∈ F, C.length ≤ k) :
    Valid k (ExecCNF.normalize Literal.negate F) := by
  refine ⟨ExecCNF.normalize_literal_nodup _ _, ExecCNF.normalize_map_nodup _ _,
    normalize_width_le F hw, ?_, ?_⟩
  · rw [ExecCNF.normalize_set]
    exact SunflowerBranch.antichain_normalize _
  · rw [ExecCNF.normalize_set]
    exact fun _ hC => SAT.normalize_not_tautology hC

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeDFSIntegration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Connect the actual produced setup frame to canonical exact counting.
The remaining finite leaf-command and numerical-envelope premises are explicit
development seams, to be instantiated by the streamed native leaf integration. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem canonical_normalized_body_length_oai {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    (SubexpNormalizationCorrectness.normalizedBody F).length ≤
      SparseCountProgram.formulaBound n k := by
  have hv := SparseDFSRefinement.Valid.normalize (ExecQuantitativeSparsify.formulaList F)
    (ExecQuantitativeSparsify.formulaList_width F k hw)
  rw [canonical_normalized_body]
  exact SparseCountProgram.encodeBody_length_le _ k hv.literal_nodup hv.clause_nodup
    (formulaSet_width_le _ hv.width)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_normalized_body_length_oai
