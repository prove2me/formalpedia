-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:22:38.718408+00:00
-- url     : https://prove2.me/submissions/c56f5b54-e268-47cb-a0dc-88bff8aa5e12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSLoop_execute
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSNative_remaining_bytes_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit_body_refinement

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

omit [DecidableEq V] in
theorem Clause.eval_mono {a : Assignment V} {C D : Clause V} (h : C ⊆ D)
    (hC : C.eval a = true) : D.eval a = true := by
  obtain ⟨l, hl, ht⟩ := (Clause.eval_eq_true a C).mp hC
  exact (Clause.eval_eq_true a D).mpr ⟨l, h hl, ht⟩

omit [DecidableEq V] in
theorem CNF.eval_mono {a : Assignment V} {F G : CNF V} (h : F ⊆ G)
    (hG : G.eval a = true) : F.eval a = true := by
  apply (CNF.eval_eq_true a F).mpr
  intro C hC
  exact (CNF.eval_eq_true a G).mp hG C (h hC)

omit [DecidableEq V] in
theorem Clause.eval_of_isTautology {C : Clause V} (h : C.IsTautology)
    (a : Assignment V) : C.eval a = true := by
  obtain ⟨l, hl, hn⟩ := h
  apply (Clause.eval_eq_true a C).mpr
  cases he : l.eval a with
  | false => exact ⟨l.negate, hn, by simp [he]⟩
  | true => exact ⟨l, hl, he⟩

theorem eval_removeTautologies (a : Assignment V) (F : CNF V) :
    (removeTautologies F).eval a = F.eval a := by
  apply Bool.eq_iff_iff.mpr
  simp only [CNF.eval_eq_true]
  constructor
  · intro h C hC
    by_cases ht : C.IsTautology
    · exact Clause.eval_of_isTautology ht a
    · exact h C (Finset.mem_filter.mpr ⟨hC, ht⟩)
  · intro h C hC
    exact h C (Finset.mem_filter.mp hC).1

theorem exists_absorb_subset (F : CNF V) (C : Clause V) (hC : C ∈ F) :
    ∃ D ∈ absorb F, D ⊆ C := by
  classical
  revert hC
  refine Finset.strongInductionOn C ?_
  intro C ih hC
  by_cases hs : ∃ D ∈ F, D ⊂ C
  · obtain ⟨D, hD, hDC⟩ := hs
    obtain ⟨E, hE, hED⟩ := ih D hDC hD
    exact ⟨E, hE, hED.trans (Finset.ssubset_iff_subset_ne.mp hDC).1⟩
  · exact ⟨C, Finset.mem_filter.mpr ⟨hC, hs⟩, Finset.Subset.refl _⟩

theorem eval_absorb (a : Assignment V) (F : CNF V) :
    (absorb F).eval a = F.eval a := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    apply (CNF.eval_eq_true a F).mpr
    intro C hC
    obtain ⟨D, hD, hDC⟩ := exists_absorb_subset F C hC
    exact Clause.eval_mono hDC ((CNF.eval_eq_true a (absorb F)).mp h D hD)
  · exact CNF.eval_mono (absorb_subset F)

theorem eval_normalize (a : Assignment V) (F : CNF V) :
    (normalize F).eval a = F.eval a := by
  rw [normalize, eval_absorb, eval_removeTautologies]

theorem normalize_subset (F : CNF V) : normalize F ⊆ F :=
  (absorb_subset _).trans (Finset.filter_subset _ _)

theorem normalize_not_tautology {F : CNF V} {C : Clause V} (hC : C ∈ normalize F) :
    ¬ C.IsTautology :=
  (Finset.mem_filter.mp (absorb_subset (removeTautologies F) hC)).2

omit [DecidableEq V] in
theorem widthAtMost_of_subset {F G : CNF V} {k : ℕ} (h : F ⊆ G)
    (hG : WidthAtMost k G) : WidthAtMost k F :=
  fun C hC => hG C (h hC)

section Finite

variable [Fintype V]

theorem count_le (F : CNF V) : count F ≤ 2 ^ Fintype.card V := by
  calc
    count F ≤ (Finset.univ : Finset (Assignment V)).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card V := by simp [Assignment ]

theorem count_congr {F G : CNF V} (h : ∀ a, F.eval a = G.eval a) : count F = count G := by
  apply congrArg Finset.card
  ext a
  simp only [mem_satisfyingAssignments, h a]

theorem count_normalize (F : CNF V) : count (normalize F) = count F :=
  count_congr (fun a => eval_normalize a F)

end Finite
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem clause_union_true_iff (a : Assignment V) (C D : Clause V) :
    (C ∪ D).eval a = true ↔ C.eval a = true ∨ D.eval a = true := by
  simp only [Clause.eval_eq_true]
  constructor
  · rintro ⟨l, hl, ht⟩
    rcases Finset.mem_union.mp hl with hC | hD
    · exact Or.inl ⟨l, hC, ht⟩
    · exact Or.inr ⟨l, hD, ht⟩
  · rintro (⟨l, hl, ht⟩ | ⟨l, hl, ht⟩)
    · exact ⟨l, Finset.mem_union_left D hl, ht⟩
    · exact ⟨l, Finset.mem_union_right C hl, ht⟩

theorem cnf_union_true_iff (a : Assignment V) (F G : CNF V) :
    (F ∪ G).eval a = true ↔ F.eval a = true ∧ G.eval a = true := by
  simp only [CNF.eval_eq_true]
  constructor
  · intro h
    exact ⟨fun C hC => h C (Finset.mem_union_left G hC),
      fun C hC => h C (Finset.mem_union_right F hC)⟩
  · rintro ⟨hF, hG⟩ C hC
    rcases Finset.mem_union.mp hC with h | h
    · exact hF C h
    · exact hG C h

theorem clauses_true_iff (a : Assignment V) (H : Clause V) (P : CNF V) :
    (clauses H P).eval a = true ↔ H.eval a = true ∨ P.eval a = true := by
  constructor
  · intro h
    by_cases hH : H.eval a = true
    · exact Or.inl hH
    · right
      apply (CNF.eval_eq_true a P).mpr
      intro p hp
      have hc := (CNF.eval_eq_true a (clauses H P)).mp h (H ∪ p)
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      exact ((clause_union_true_iff a H p).mp hc).resolve_left hH
  · intro h
    apply (CNF.eval_eq_true a (clauses H P)).mpr
    intro C hC
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
    apply (clause_union_true_iff a H p).mpr
    exact h.imp_right (fun hP => (CNF.eval_eq_true a P).mp hP p hp)

end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

namespace Sunflower
variable {d : ℕ}

private theorem union_singleton_eq_insert (F : CNF V) (C : Clause V) :
    F ∪ {C} = insert C F := by
  ext D
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  exact or_comm

end Sunflower
end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

theorem sdiff_injective_on {F : CNF V} {H : Clause V}
    (hcore : ∀ C ∈ F, H ⊆ C) : Set.InjOn (fun C => C \ H) F := by
  intro C hC D hD heq
  change C \ H = D \ H at heq
  calc
    C = H ∪ (C \ H) := (Finset.union_sdiff_of_subset (hcore C hC)).symm
    _ = H ∪ (D \ H) := congrArg (fun P => H ∪ P) heq
    _ = D := Finset.union_sdiff_of_subset (hcore D hD)

theorem clauses_petalFamily {F : CNF V} {H : Clause V} (hcore : ∀ C ∈ F, H ⊆ C) :
    clauses H (petalFamily F H) = F := by
  ext C
  constructor
  · intro hC
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hp
    have hDC : D = C := (Finset.union_sdiff_of_subset (hcore D hD)).symm.trans heq
    exact hDC ▸ hD
  · intro hC
    exact Finset.mem_image.mpr ⟨C \ H, Finset.mem_image.mpr ⟨C, hC, rfl⟩,
      Finset.union_sdiff_of_subset (hcore C hC)⟩

end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch
open SubexponentialSAT.SAT
universe u
variable {V : Type u} [DecidableEq V]

theorem antichain_normalize (F : CNF V) : Antichain (normalize F) :=
  antichain_absorb _

end SubexponentialSAT.SunflowerBranch

namespace SubexponentialSAT.SunflowerBranch

open SubexponentialSAT.SAT
open scoped BigOperators
universe u
variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
theorem literalMass_mono {F G : CNF V} (h : F ⊆ G) : literalMass F ≤ literalMass G :=
  Finset.sum_le_sum_of_subset h

theorem literalMass_absorb_le (F : CNF V) : literalMass (absorb F) ≤ literalMass F :=
  literalMass_mono (absorb_subset F)

theorem literalMass_union_le (F G : CNF V) :
    literalMass (F ∪ G) ≤ literalMass F + literalMass G := by
  calc
    literalMass (F ∪ G) ≤ literalMass (F ∪ G) + literalMass (F ∩ G) := Nat.le_add_right _ _
    _ = literalMass F + literalMass G := Finset.sum_union_inter

theorem literalMass_insert_le (F : CNF V) (C : Clause V) :
    literalMass (insert C F) ≤ literalMass F + C.card := by
  have heq : insert C F = F ∪ {C} := by
    ext D
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    exact or_comm
  rw [heq]
  simpa only [literalMass_singleton] using literalMass_union_le F {C}

theorem literalMass_sdiff {F S : CNF V} (h : S ⊆ F) :
    literalMass (F \ S) + literalMass S = literalMass F := Finset.sum_sdiff h

omit [DecidableEq V] in
theorem clause_card_le_literalMass {F : CNF V} {C : Clause V} (hC : C ∈ F) :
    C.card ≤ literalMass F := by
  have hsub : ({C} : CNF V) ⊆ F := Finset.singleton_subset_iff.mpr hC
  simpa only [literalMass_singleton] using literalMass_mono hsub

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

theorem petal_filter_set (C H : Clause α) :
    clauseSet (C.filter (fun x => !decide (x ∈ H))) = clauseSet C \ clauseSet H := by
  ext x
  simp [clauseSet]

theorem petal_family_set (G : Formula α) (H : Clause α) :
    formulaSet (G.map (fun C => C.filter (fun x => !decide (x ∈ H)))) =
      (formulaSet G).image (fun C => C \ clauseSet H) := by
  ext D
  constructor
  · intro hD
    obtain ⟨C, hC, he⟩ := mem_formulaSet.mp hD
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hC
    exact Finset.mem_image.mpr ⟨clauseSet A, mem_formulaSet.mpr ⟨A, hA, rfl⟩,
      (petal_filter_set A H).symm.trans he⟩
  · intro hD
    obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hD
    obtain ⟨A, hA, rfl⟩ := mem_formulaSet.mp hC
    exact mem_formulaSet.mpr ⟨A.filter (fun x => !decide (x ∈ H)),
      List.mem_map.mpr ⟨A, hA, rfl⟩, (petal_filter_set A H).trans he⟩

end SubexponentialSAT.ExecCNFCodeTransport

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


/-- Set semantics of the exact list output, valid even with reordered or
repeated literals and repeated clauses in any of the supplied lists. -/
theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (result F selected H) =
      (insert (ExecCNF.clauseSet H) (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)).filter
        (fun C => ¬ ∃ D ∈ insert (ExecCNF.clauseSet H)
          (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected), D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_cons,
    ExecCNF.formulaSet_eraseClauses]

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

theorem petals_set {α : Type*} [DecidableEq α] (selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (petals selected H) =
      (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H) :=
  ExecCNFCodeTransport.petal_family_set selected H

theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    let P := (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H)
    let G := P ∪ (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)
    ExecCNF.formulaSet (result F selected H) = G.filter (fun C => ¬ ∃ D ∈ G, D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_append,
    ExecCNF.formulaSet_eraseClauses, petals_set]

end SubexponentialSAT.ExecPetalChildProgram

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

/-- No variable restriction or unit propagation occurs in this normalization. -/
theorem rawCount_normalize (F : RawCNF n) :
    rawCount (ExecCNF.normalize SAT.Literal.negate F) = rawCount F := by
  simp only [rawCount, ExecCNF.normalize_set, SAT.count_normalize]

theorem formulaSet_card_le_length (F : RawCNF n) :
    (ExecCNF.formulaSet F).card ≤ F.length := by
  simpa only [ExecCNF.formulaSet, List.length_map] using
    (F.map ExecCNF.clauseSet).toFinset_card_le

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsify
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Appendix A: literal-core branching with disjoint exact-count children. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch

open OAI.Algorithms.SubexponentialSAT.SAT

universe u
variable {V : Type u} [DecidableEq V]

theorem sdiff_injOn_selected (F : CNF V) (c : ℕ) (H : Clause V) :
    Set.InjOn (fun C => C \ H) (selected F c H) :=
  SunflowerBranch.sdiff_injective_on fun _ hC => (mem_selected.mp hC).2.2

theorem petals_card (F : CNF V) (c : ℕ) (H : Clause V) :
    (petals F c H).card = (selected F c H).card :=
  Finset.card_image_of_injOn (sdiff_injOn_selected F c H)

theorem clauses_petals (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.clauses H (petals F c H) = selected F c H :=
  SunflowerBranch.clauses_petalFamily fun _ hC => (mem_selected.mp hC).2.2

theorem negatedCoreUnits_eval (a : Assignment V) (H : Clause V) :
    (negatedCoreUnits H).eval a = true ↔ H.eval a = false := by
  simp only [CNF.eval_eq_true, negatedCoreUnits, Finset.forall_mem_image,
    Clause.eval_eq_true, Finset.mem_singleton, exists_eq_left, Literal.eval_negate,
    Bool.not_eq_true', ← Bool.not_eq_true, not_exists, not_and]

theorem eval_childA (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    (childA F c H).eval a = true ↔
      H.eval a = true ∧ (F \ selected F c H).eval a = true := by
  simp only [childA, eval_absorb, CNF.eval_insert, Bool.and_eq_true]

theorem eval_childB (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    (childB F c H).eval a = true ↔
      ((F \ selected F c H).eval a = true ∧ (petals F c H).eval a = true) ∧
        H.eval a = false := by
  rw [childB, eval_absorb, SunflowerBranch.cnf_union_true_iff,
    SunflowerBranch.cnf_union_true_iff, negatedCoreUnits_eval]

theorem eval_children_iff (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    F.eval a = true ↔
      (childA F c H).eval a = true ∨ (childB F c H).eval a = true := by
  have hF : F.eval a = true ↔ (F \ selected F c H).eval a = true ∧
      (H.eval a = true ∨ (petals F c H).eval a = true) := by
    have hsplit : F = (F \ selected F c H) ∪ selected F c H :=
      (Finset.sdiff_union_of_subset (selected_subset F c H)).symm
    have hselected : (selected F c H).eval a = true ↔
        H.eval a = true ∨ (petals F c H).eval a = true := by
      rw [← clauses_petals F c H, SunflowerBranch.clauses_true_iff]
    conv_lhs => rw [hsplit]
    rw [SunflowerBranch.cnf_union_true_iff, hselected]
  rw [hF, eval_childA, eval_childB]
  cases H.eval a <;> simp

theorem children_disjoint (a : Assignment V) (F : CNF V) (c : ℕ) (H : Clause V) :
    ¬ ((childA F c H).eval a = true ∧ (childB F c H).eval a = true) := by
  rintro ⟨hA, hB⟩
  have ht := ((eval_childA a F c H).mp hA).1
  have hf := ((eval_childB a F c H).mp hB).2
  rw [ht] at hf
  contradiction

theorem satisfyingAssignments_partition [Fintype V] (F : CNF V) (c : ℕ)
    (H : Clause V) :
    satisfyingAssignments F = satisfyingAssignments (childA F c H) ∪
      satisfyingAssignments (childB F c H) := by
  ext a
  simp only [mem_satisfyingAssignments, Finset.mem_union]
  exact eval_children_iff a F c H

theorem satisfyingAssignments_disjoint [Fintype V] (F : CNF V) (c : ℕ)
    (H : Clause V) :
    Disjoint (satisfyingAssignments (childA F c H))
      (satisfyingAssignments (childB F c H)) := by
  apply Finset.disjoint_left.mpr
  intro a hA hB
  exact children_disjoint a F c H
    ⟨(mem_satisfyingAssignments _ _).mp hA, (mem_satisfyingAssignments _ _).mp hB⟩

theorem count_children [Fintype V] (F : CNF V) (c : ℕ) (H : Clause V) :
    count F = count (childA F c H) + count (childB F c H) := by
  unfold count
  rw [satisfyingAssignments_partition, Finset.card_union_of_disjoint
    (satisfyingAssignments_disjoint F c H)]

open scoped BigOperators

theorem literalMass_selected (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.literalMass (selected F c H) = (selected F c H).card * c := by
  exact Finset.sum_const_nat fun _ hC => (mem_selected.mp hC).2.1

theorem literalMass_petals (F : CNF V) (c : ℕ) (H : Clause V) :
    SunflowerBranch.literalMass (petals F c H) =
      (selected F c H).card * (c - H.card) := by
  rw [← petals_card]
  exact Finset.sum_const_nat fun _ hP => petal_card hP

theorem literalMass_negatedCoreUnits (H : Clause V) :
    SunflowerBranch.literalMass (negatedCoreUnits H) = H.card := by
  have hinj : Set.InjOn (fun l : Literal V => ({l.negate} : Clause V)) H := by
    intro l _ m _ heq
    have hneg := Finset.singleton_injective heq
    simpa only [Literal.negate_negate] using congrArg Literal.negate hneg
  unfold SunflowerBranch.literalMass negatedCoreUnits
  rw [Finset.sum_image hinj]
  simp

theorem literalMass_childA_lt {F : CNF V} {c : ℕ} {H : Clause V}
    (hsel : (selected F c H).Nonempty) (hproper : H.card < c) :
    SunflowerBranch.literalMass (childA F c H) < SunflowerBranch.literalMass F := by
  obtain ⟨C, hC⟩ := hsel
  have hlt : H.card < SunflowerBranch.literalMass (selected F c H) :=
    (Finset.card_lt_card (core_strict_subset hC hproper)).trans_le
      (SunflowerBranch.clause_card_le_literalMass hC)
  have habsorb := SunflowerBranch.literalMass_absorb_le (insert H (F \ selected F c H))
  have hinsert := SunflowerBranch.literalMass_insert_le (F \ selected F c H) H
  have hsplit := SunflowerBranch.literalMass_sdiff (selected_subset F c H)
  change SunflowerBranch.literalMass (childA F c H) ≤ _ at habsorb
  omega

theorem literalMass_childB_lt {F : CNF V} {c : ℕ} {H : Clause V}
    (hH : H.Nonempty) (hproper : H.card < c) (hsize : 2 ≤ (selected F c H).card) :
    SunflowerBranch.literalMass (childB F c H) < SunflowerBranch.literalMass F := by
  have hmul : H.card < (selected F c H).card * H.card := by
    simpa using Nat.mul_lt_mul_of_pos_right (show 1 < (selected F c H).card by omega)
      (Finset.card_pos.mpr hH)
  have hlt : SunflowerBranch.literalMass (petals F c H) +
      SunflowerBranch.literalMass (negatedCoreUnits H) <
      SunflowerBranch.literalMass (selected F c H) := by
    rw [literalMass_petals, literalMass_negatedCoreUnits, literalMass_selected]
    calc
      (selected F c H).card * (c - H.card) + H.card <
          (selected F c H).card * (c - H.card) + (selected F c H).card * H.card :=
        Nat.add_lt_add_left hmul _
      _ = (selected F c H).card * c := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hproper.le]
  have habsorb := SunflowerBranch.literalMass_absorb_le
    (((F \ selected F c H) ∪ petals F c H) ∪ negatedCoreUnits H)
  have hunits := SunflowerBranch.literalMass_union_le
    ((F \ selected F c H) ∪ petals F c H) (negatedCoreUnits H)
  have hpetals := SunflowerBranch.literalMass_union_le (F \ selected F c H) (petals F c H)
  have hsplit := SunflowerBranch.literalMass_sdiff (selected_subset F c H)
  change SunflowerBranch.literalMass (childB F c H) ≤ _ at habsorb
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranch
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem Transition.mass_eq {s t : State n} (h : Transition s t) : mass t = mass s := by
  cases h with
  | idle => rfl
  | leaf node rest total => simp [mass, Nat.add_assoc]
  | branch node rest total c H =>
    simp only [mass, List.map_cons, List.sum_cons]
    rw [count_children node.formula c H]
    omega

theorem Transitions.mass_eq {steps : ℕ} {s t : State n}
    (h : Transitions steps s t) : mass t = mass s := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans hs.mass_eq

theorem Transitions.current_sum_le_pow {steps total : ℕ} {F : CNF (Fin n)}
    {node : Entry n} {rest : List (Entry n)}
    (h : Transitions steps (initial F) ⟨node :: rest, total⟩) :
    total + count node.formula ≤ 2 ^ n := by
  have hm := h.mass_eq
  rw [mass_initial] at hm
  have hc : count F ≤ 2 ^ n := by simpa using count_le F
  simp only [mass, List.map_cons, List.sum_cons] at hm
  omega

theorem priority_literalMass_lt {M c : ℕ} {F : CNF (Fin n)} {H : Clause (Fin n)}
    (hM : 2 ≤ M) (hpriority : SparsePriority.Priority F M c H) :
    SunflowerBranch.literalMass (childA F c H) < SunflowerBranch.literalMass F ∧
      SunflowerBranch.literalMass (childB F c H) < SunflowerBranch.literalMass F := by
  obtain ⟨⟨C, hC, hc, hHC⟩, hpos, hproper, hdegree⟩ :=
    hpriority.spec
  have hsel : (selected F c H).Nonempty := ⟨C, mem_selected.mpr ⟨hC, hc, hHC⟩⟩
  have hpow : M ≤ M ^ (c - H.card) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < M)
      (by omega : 1 ≤ c - H.card)
  exact ⟨literalMass_childA_lt hsel hproper,
    literalMass_childB_lt (Finset.card_pos.mp hpos) hproper
      (hM.trans (hpow.trans hdegree))⟩

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

theorem literalMass_le_card_mul (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    SunflowerBranch.literalMass F ≤ F.card * k := by
  calc
    SunflowerBranch.literalMass F ≤ ∑ _C ∈ F, k := Finset.sum_le_sum hF
    _ = F.card * k := by simp





theorem selectedPath_depth_add_literalMass_le {M : ℕ} {F G : CNF (Fin n)}
    {bits : List Bool} (hp : SparseCharging.SelectedPath M F bits G) (hM : 2 ≤ M) :
    bits.length + SunflowerBranch.literalMass G ≤ SunflowerBranch.literalMass F := by
  induction hp with
  | nil F => simp
  | @step F G bits c H b hpriority hp ih =>
    have hm := priority_literalMass_lt hM hpriority
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] at ih ⊢ <;> omega

theorem selectedPath_invariants {M k : ℕ} {F G : CNF (Fin n)}
    {bits : List Bool} (hp : SparseCharging.SelectedPath M F bits G)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : WidthAtMost k F) :
    SunflowerBranch.Antichain G ∧ (∀ C ∈ G, ¬ C.IsTautology) ∧ WidthAtMost k G := by
  revert hanti hnt hwidth
  induction hp with
  | nil F => exact fun ha hn hw => ⟨ha, hn, hw⟩
  | @step F G bits c H b hpriority hp ih =>
    intro ha hn hw
    obtain ⟨⟨C, hC, hc, hHC⟩, hpos, hproper, _⟩ := hpriority.spec
    have hsel : (selected F c H).Nonempty := ⟨C, mem_selected.mpr ⟨hC, hc, hHC⟩⟩
    cases b with
    | false =>
      apply ih (childA_antichain F c H) (childA_not_tautological hn hsel)
      exact childA_widthAtMost hw hsel hproper
    | true =>
      apply ih (childB_antichain F c H) (childB_not_tautological hn)
      exact childB_widthAtMost hw hsel (Finset.card_pos.mp hpos) hproper

theorem selectedPath_raw_depth_le (F : RawCNF n) {M k : ℕ}
    {G : CNF (Fin n)} {bits : List Bool}
    (hp : SparseCharging.SelectedPath M (normalize (ExecCNF.formulaSet F)) bits G)
    (hM : 2 ≤ M) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    bits.length ≤ F.length * k := by
  have hw := widthAtMost_of_subset (normalize_subset _) (formulaSet_width_le F hwidth)
  have hd := selectedPath_depth_add_literalMass_le hp hM
  have hm := literalMass_le_card_mul (normalize (ExecCNF.formulaSet F)) k hw
  have hc := Nat.mul_le_mul_right k
    ((Finset.card_le_card (normalize_subset (ExecCNF.formulaSet F))).trans
      (formulaSet_card_le_length F))
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

theorem selectedRaw_subset {α : Type*} [DecidableEq α]
    (F : List (List α)) (c : ℕ) (H : List α) : selectedRaw F c H ⊆ F :=
  List.filter_sublist.subset

theorem selectedRaw_set {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (selectedRaw F c H) =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  ext D
  simp only [ExecCNF.mem_formulaSet, DisjointBranch.mem_selected]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hCF, htest⟩ := List.mem_filter.mp hC
    obtain ⟨hc, hsub⟩ := Bool.and_eq_true_iff.mp htest
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨⟨C, hCF, rfl⟩, hcard.trans (of_decide_eq_true hc),
      (ExecCNF.subset_true H C).mp hsub⟩
  · rintro ⟨⟨C, hCF, rfl⟩, hc, hsub⟩
    refine ⟨C, List.mem_filter.mpr ⟨hCF, ?_⟩, rfl⟩
    apply Bool.and_eq_true_iff.mpr
    have hcard := List.toFinset_card_of_nodup (hF C hCF)
    exact ⟨decide_eq_true (hcard.symm.trans hc), (ExecCNF.subset_true H C).mpr hsub⟩

theorem selectedRaw_length {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (c : ℕ) (H : List (SAT.Literal V))
    (hF : ∀ C ∈ F, C.Nodup) (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    (selectedRaw F c H).length =
      SparsePriority.degree (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hn : ((selectedRaw F c H).map ExecCNF.clauseSet).Nodup :=
    (List.Sublist.map ExecCNF.clauseSet List.filter_sublist).nodup hdistinct
  have hc := List.toFinset_card_of_nodup hn
  change (ExecCNF.formulaSet (selectedRaw F c H)).card = _ at hc
  rw [selectedRaw_set F c H hF, List.length_map] at hc
  exact hc.symm

theorem masked_sublist {α : Type*} (mask : List Bool) (C : List α) :
    (masked mask C).Sublist C := by
  induction C generalizing mask with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [masked]
    split
    · exact .cons_cons x (ih mask.tail)
    · exact .cons x (ih mask.tail)

theorem masked_membership {α : Type*} [DecidableEq α] (C : List α) (H : Finset α)
    (suffix : List Bool) :
    masked (C.map (fun x => decide (x ∈ H)) ++ suffix) C = C.filter (fun x => decide (x ∈ H)) := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x ∈ H <;> simp [masked, hx, ih]

theorem exists_masked {α : Type*} [DecidableEq α] (k : ℕ) (C : List α) (H : Finset α)
    (hC : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ mask ∈ masks k, (masked mask C).toFinset = H := by
  let mask := C.map (fun x => decide (x ∈ H)) ++ List.replicate (k - C.length) false
  refine ⟨mask, (mem_masks mask k).mpr ?_, ?_⟩
  · simp [mask, Nat.add_sub_of_le hC]
  · rw [show masked mask C = C.filter (fun x => decide (x ∈ H)) from masked_membership C H _]
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨by simpa using hH h, h⟩⟩

theorem rawCandidates_complete {α : Type*} [DecidableEq α]
    (k : ℕ) (F : List (List α)) (C : List α) (H : Finset α)
    (hC : C ∈ F) (hwidth : C.length ≤ k) (hH : H ⊆ C.toFinset) :
    ∃ core, (C.length, core) ∈ rawCandidates k F ∧ core.toFinset = H ∧ core.Sublist C := by
  obtain ⟨mask, hm, he⟩ := exists_masked k C H hwidth hH
  refine ⟨masked mask C, ?_, he, masked_sublist mask C⟩
  exact List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨mask, hm, rfl⟩⟩

theorem rawCandidate_spec {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, C.length = c ∧ H.Sublist C := by
  obtain ⟨C, hC, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, _, hp⟩ := List.mem_map.mp hm
  obtain ⟨hc, hH⟩ := Prod.mk.inj hp
  exact ⟨C, hC, hc, hH ▸ masked_sublist mask C⟩

theorem represent_core {n : ℕ} (k : ℕ) (F : List (List (SAT.Literal (Fin n))))
    (c : ℕ) (H : SAT.Clause (Fin n))
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdegree : 0 < SparsePriority.degree (ExecCNF.formulaSet F) c H) :
    ∃ core, (c, core) ∈ rawCandidates k F ∧ ExecCNF.clauseSet core = H ∧ core.length = H.card := by
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hdegree
  obtain ⟨hCF, hc, hH⟩ := DisjointBranch.mem_selected.mp hC
  obtain ⟨rawC, hrawC, rfl⟩ := ExecCNF.mem_formulaSet.mp hCF
  have hrawlen : rawC.length = c :=
    (List.toFinset_card_of_nodup (hnodup rawC hrawC)).symm.trans hc
  obtain ⟨core, hcore, he, hsub⟩ :=
    rawCandidates_complete k F rawC H hrawC (hwidth rawC hrawC) hH
  have hnodupCore := hsub.nodup (hnodup rawC hrawC)
  refine ⟨core, hrawlen ▸ hcore, he, ?_⟩
  exact (List.toFinset_card_of_nodup hnodupCore).symm.trans (congrArg Finset.card he)

theorem RawPriority.toPriority {n : ℕ} {k : ℕ} {F : List (List (SAT.Literal (Fin n)))}
    {M c : ℕ} {H : List (SAT.Literal (Fin n))} (h : RawPriority k F M c H) (hM : 0 < M)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    SparsePriority.Priority (ExecCNF.formulaSet F) M c (ExecCNF.clauseSet H) := by
  obtain ⟨C, hCF, hc, hsub⟩ := rawCandidate_spec k F c H h.candidate
  have hHnodup := hsub.nodup (hnodup C hCF)
  have hHcard : (ExecCNF.clauseSet H).card = H.length := List.toFinset_card_of_nodup hHnodup
  have hCcard : (ExecCNF.clauseSet C).card = c :=
    (List.toFinset_card_of_nodup (hnodup C hCF)).trans hc
  refine ⟨⟨ExecCNF.clauseSet C, ExecCNF.mem_formulaSet.mpr ⟨C, hCF, rfl⟩, hCcard, ?_⟩,
    hHcard.symm ▸ h.core_nonempty, hHcard.symm ▸ h.core_proper, ?_, ?_, ?_⟩
  · intro l hl
    exact ExecCNF.mem_clauseSet.mpr (hsub.subset (ExecCNF.mem_clauseSet.mp hl))
  · simpa only [hHcard, selectedRaw_length F c H hnodup hdistinct] using h.threshold
  · intro d S hS hSd hdc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) d S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F d S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.minimum d core hcore (by omega) (by omega) hdc
    simpa only [selectedRaw_length F d core hnodup hdistinct, he, hlen] using hf
  · intro S hHS hSc
    by_cases hz : SparsePriority.degree (ExecCNF.formulaSet F) c S = 0
    · rw [hz]; exact pow_pos hM _
    obtain ⟨core, hcore, he, hlen⟩ := represent_core k F c S hwidth hnodup (Nat.pos_of_ne_zero hz)
    have hf := h.maximum core hcore (by omega) (by omega)
    simpa only [selectedRaw_length F c core hnodup hdistinct, he, hlen] using hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

theorem negatedUnits_set {V : Type*} [DecidableEq V] (H : List (Literal V)) :
    ExecCNF.formulaSet (negatedUnits Literal.negate H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) := by
  ext C
  simp [negatedUnits, ExecCNF.formulaSet, ExecCNF.clauseSet,
    DisjointBranch.negatedCoreUnits, Finset.mem_image]

theorem resultA_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (ExecCoreChildProgram.result F S H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  simpa only [hS, DisjointBranch.childA, SAT.absorb] using
    ExecCoreChildProgram.result_set F S H

theorem units_disjoint_selected {V : Type*} [DecidableEq V]
    (F : CNF V) (c : ℕ) (H : Clause V) (hc : 2 ≤ c) :
    Disjoint (DisjointBranch.negatedCoreUnits H) (DisjointBranch.selected F c H) := by
  apply Finset.disjoint_left.mpr
  intro U hU hsel
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hU
  have hcard := (DisjointBranch.mem_selected.mp hsel).2.1
  rw [Finset.card_singleton] at hcard
  omega

theorem resultB_set {V : Type*} [DecidableEq V]
    (F S : List (List (Literal V))) (H : List (Literal V)) (c : ℕ) (hc : 2 ≤ c)
    (hS : ExecCNF.formulaSet S =
      DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :
    ExecCNF.formulaSet (resultB Literal.negate F S H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) := by
  have hdisj := units_disjoint_selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) hc
  have hdiff :
      (DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪ ExecCNF.formulaSet F) \
        DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) =
      DisjointBranch.negatedCoreUnits (ExecCNF.clauseSet H) ∪
        (ExecCNF.formulaSet F \
          DisjointBranch.selected (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) := by
    rw [Finset.union_sdiff_distrib, hdisj.sdiff_eq_left]
  unfold resultB
  rw [ExecPetalChildProgram.result_set]
  change SAT.absorb (_ ∪ (_ \ _)) = _
  rw [ExecCNF.formulaSet_append, negatedUnits_set, hS, hdiff]
  unfold DisjointBranch.childB DisjointBranch.petals SunflowerBranch.petalFamily
  apply congrArg SAT.absorb
  ac_rfl

theorem resultA_clause_nodup {α : Type*} [DecidableEq α]
    (F S : List (List α)) (H : List α) :
    ((ExecCoreChildProgram.result F S H).map ExecCNF.clauseSet).Nodup :=
  ExecCNF.absorb_map_nodup _

theorem resultB_clause_nodup {α : Type*} [DecidableEq α]
    (negate : α → α) (F S : List (List α)) (H : List α) :
    ((resultB negate F S H).map ExecCNF.clauseSet).Nodup :=
  ExecCNF.absorb_map_nodup _

theorem resultA_literal_nodup {α : Type*} [DecidableEq α]
    (F S : List (List α)) (H : List α)
    (hF : ∀ C ∈ F, C.Nodup) (hH : H.Nodup) :
    ∀ C ∈ ExecCoreChildProgram.result F S H, C.Nodup := by
  intro C hC
  have h := ExecCNF.absorb_subset _ hC
  rcases List.mem_cons.mp h with rfl | h
  · exact hH
  · exact hF C (List.mem_filter.mp h).1

theorem resultB_literal_nodup {α : Type*} [DecidableEq α]
    (negate : α → α) (F S : List (List α)) (H : List α)
    (hF : ∀ C ∈ F, C.Nodup) (hS : ∀ C ∈ S, C.Nodup) :
    ∀ C ∈ resultB negate F S H, C.Nodup := by
  intro C hC
  have h := ExecCNF.absorb_subset _ hC
  rcases List.mem_append.mp h with h | h
  · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h
    exact (hS D hD).filter _
  · have hmem := (List.mem_filter.mp h).1
    rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hmem
      exact List.nodup_singleton _
    · exact hF C hmem

open BitProgram StructuredCalls

open ExecBranchControllerSupport

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
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

theorem childA_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childA F c H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultA_set F (selectedRaw F c H) H c
    (selectedRaw_set F c H hnodup)

theorem childB_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hc : 2 ≤ c) (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childB F c H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultB_set F (selectedRaw F c H) H c hc
    (selectedRaw_set F c H hnodup)

theorem Transition.model {k M : ℕ} {s t : Frontier n} (h : Transition k M s t) :
    SparseCountProgram.Transition s.model t.model := by
  cases h with
  | leaf node rest total _ => exact .leaf node.model (rest.map Node.model) total
  | branch node rest total c H hv hp =>
      have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
      have ha := childA_set node.formula c H hv.literal_nodup
      have hb := childB_set node.formula c H hc hv.literal_nodup
      simpa only [Frontier.model, Node.model, List.map_cons, ha, hb] using
        SparseCountProgram.Transition.branch node.model (rest.map Node.model) total c
          (ExecCNF.clauseSet H)

theorem Transitions.model {k M visits : ℕ} {s t : Frontier n}
    (h : Transitions k M visits s t) :
    SparseCountProgram.Transitions visits s.model t.model := by
  induction h with
  | refl => exact .refl _
  | cons first _ ih => exact .cons first.model ih

theorem Transitions.finished_count {k M visits total : ℕ} {F : RawCNF n}
    (h : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    total = rawCount F := by
  have hm := h.model.mass_eq
  simpa [Frontier.model, Node.model, SparseCountProgram.mass, rawCount] using hm

theorem Transitions.next_sum_le_pow {k M visits total : ℕ} {F : RawCNF n}
    {node : Node n} {rest : List (Node n)}
    (h : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ ⟨node :: rest, total⟩) :
    total + rawCount node.formula ≤ 2 ^ n := by
  have hr : SparseCountProgram.Transitions visits
      (SparseCountProgram.initial (ExecCNF.formulaSet F))
      ⟨node.model :: rest.map Node.model, total⟩ := h.model
  exact SparseCountProgram.Transitions.current_sum_le_pow
    (F := ExecCNF.formulaSet F) (node := node.model) (rest := rest.map Node.model) hr


theorem Valid.normalize (F : RawCNF n) {k : ℕ} (hw : ∀ C ∈ F, C.length ≤ k) :
    Valid k (ExecCNF.normalize Literal.negate F) := by
  refine ⟨ExecCNF.normalize_literal_nodup _ _, ExecCNF.normalize_map_nodup _ _,
    normalize_width_le F hw, ?_, ?_⟩
  · rw [ExecCNF.normalize_set]
    exact SunflowerBranch.antichain_normalize _
  · rw [ExecCNF.normalize_set]
    exact fun _ hC => SAT.normalize_not_tautology hC

theorem width_of_formulaSet (F : RawCNF n) {k : ℕ}
    (hnodup : ∀ C ∈ F, C.Nodup) (hw : WidthAtMost k (ExecCNF.formulaSet F)) :
    ∀ C ∈ F, C.length ≤ k := by
  intro C hC
  have h := hw (ExecCNF.clauseSet C) (ExecCNF.mem_formulaSet.mpr ⟨C, hC, rfl⟩)
  simpa only [ExecCNF.clauseSet, List.toFinset_card_of_nodup (hnodup C hC)] using h

theorem Valid.children {k M c : ℕ} {F : RawCNF n} {H : List (Literal (Fin n))}
    (hv : Valid k F) (hp : RawPriority k F M c H) (hM : 0 < M) :
    Valid k (childA F c H) ∧ Valid k (childB F c H) := by
  have hpriority := hp.toPriority hM hv.width hv.literal_nodup hv.clause_nodup
  obtain ⟨C, hCF, _, hsub⟩ := rawCandidate_spec k F c H hp.candidate
  have hH := hsub.nodup (hv.literal_nodup C hCF)
  have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
  have ha := childA_set F c H hv.literal_nodup
  have hb := childB_set F c H hc hv.literal_nodup
  have hna := DisjointBranchProgram.resultA_literal_nodup F (selectedRaw F c H) H
    hv.literal_nodup hH
  have hnb := DisjointBranchProgram.resultB_literal_nodup Literal.negate F (selectedRaw F c H) H
    hv.literal_nodup (fun D hD => hv.literal_nodup D (selectedRaw_subset F c H hD))
  have pathA : SparseCharging.SelectedPath M (ExecCNF.formulaSet F) [false]
      (DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :=
    .step false hpriority (.nil _)
  have pathB : SparseCharging.SelectedPath M (ExecCNF.formulaSet F) [true]
      (DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :=
    .step true hpriority (.nil _)
  have ia := SparseCountProgram.selectedPath_invariants pathA hv.antichain hv.not_tautological
    (formulaSet_width_le F hv.width)
  have ib := SparseCountProgram.selectedPath_invariants pathB hv.antichain hv.not_tautological
    (formulaSet_width_le F hv.width)
  rw [← ha] at ia
  rw [← hb] at ib
  exact ⟨⟨hna, DisjointBranchProgram.resultA_clause_nodup _ _ _,
      width_of_formulaSet _ hna ia.2.2, ia.1, ia.2.1⟩,
    ⟨hnb, DisjointBranchProgram.resultB_clause_nodup _ _ _ _,
      width_of_formulaSet _ hnb ib.2.2, ib.1, ib.2.1⟩⟩


theorem Transition.pending_valid {k M : ℕ} {s t : Frontier n}
    (h : Transition k M s t) (hM : 0 < M)
    (hvalid : ∀ node ∈ s.pending, Valid k node.formula) :
    ∀ node ∈ t.pending, Valid k node.formula := by
  cases h with
  | leaf node rest total _ => exact fun e he => hvalid e (List.mem_cons_of_mem _ he)
  | branch node rest total c H hv hp =>
      have hc := hv.children hp hM
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hc.1
      rcases List.mem_cons.mp he with rfl | he
      · exact hc.2
      · exact hvalid e (List.mem_cons_of_mem _ he)

theorem Transitions.pending_valid {k M visits : ℕ} {s t : Frontier n}
    (h : Transitions k M visits s t) (hM : 0 < M)
    (hvalid : ∀ node ∈ s.pending, Valid k node.formula) :
    ∀ node ∈ t.pending, Valid k node.formula := by
  induction h with
  | refl => exact hvalid
  | cons first _ ih => exact ih (first.pending_valid hM hvalid)

theorem selectedPath_append {M : ℕ} {F G H : CNF (Fin n)} {left right : List Bool}
    (hp : SparseCharging.SelectedPath M F left G)
    (hq : SparseCharging.SelectedPath M G right H) :
    SparseCharging.SelectedPath M F (left ++ right) H := by
  induction hp with
  | nil => exact hq
  | step b hpriority _ ih => exact .step b hpriority (ih hq)

theorem Transition.pending_paths {k M : ℕ} {s t : Frontier n} {root : RawCNF n}
    (h : Transition k M s t) (hM : 0 < M)
    (hpaths : ∀ node ∈ s.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula)) :
    ∀ node ∈ t.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula) := by
  cases h with
  | leaf node rest total _ => exact fun e he => hpaths e (List.mem_cons_of_mem _ he)
  | branch node rest total c H hv hp =>
      obtain ⟨bits, hlen, hpath⟩ := hpaths node (List.mem_cons_self)
      have hpriority := hp.toPriority hM hv.width hv.literal_nodup hv.clause_nodup
      have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · refine ⟨bits ++ [false], by simp [hlen], ?_⟩
        rw [childA_set node.formula c H hv.literal_nodup]
        exact selectedPath_append hpath (.step false hpriority (.nil _))
      rcases List.mem_cons.mp he with rfl | he
      · refine ⟨bits ++ [true], by simp [hlen], ?_⟩
        rw [childB_set node.formula c H hc hv.literal_nodup]
        exact selectedPath_append hpath (.step true hpriority (.nil _))
      · exact hpaths e (List.mem_cons_of_mem _ he)

theorem Transitions.pending_paths {k M visits : ℕ} {s t : Frontier n} {root : RawCNF n}
    (h : Transitions k M visits s t) (hM : 0 < M)
    (hpaths : ∀ node ∈ s.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula)) :
    ∀ node ∈ t.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula) := by
  induction h with
  | refl => exact hpaths
  | cons first _ ih => exact ih (first.pending_paths hM hpaths)

theorem Transitions.normalized_pending_invariants {k M visits : ℕ} {s : Frontier n}
    (F : RawCNF n) (hM : 2 ≤ M) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (h : Transitions k M visits ⟨[⟨ExecCNF.normalize Literal.negate F, 0⟩], 0⟩ s) :
    (∀ node ∈ s.pending, Valid k node.formula) ∧
      ∀ node ∈ s.pending, node.depth ≤ F.length * k := by
  have hv := h.pending_valid (by omega) (by
    intro node hnode
    obtain rfl := List.mem_singleton.mp hnode
    exact Valid.normalize F hwidth)
  have hp := h.pending_paths (root := ExecCNF.normalize Literal.negate F) (by omega) (by
    intro node hnode
    obtain rfl := List.mem_singleton.mp hnode
    exact ⟨[], rfl, .nil _⟩)
  refine ⟨hv, ?_⟩
  intro node hnode
  obtain ⟨bits, hlen, hpath⟩ := hp node hnode
  rw [ExecCNF.normalize_set] at hpath
  rw [← hlen]
  exact SparseCountProgram.selectedPath_raw_depth_le F hpath hM hwidth



theorem Transitions.trans {k M a b : ℕ} {s t u : Frontier n}
    (h₁ : Transitions k M a s t) (h₂ : Transitions k M b t u) :
    Transitions k M (a + b) s u := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons s v t a hs _ ih =>
      simpa only [Nat.add_assoc, Nat.add_comm 1 b] using Transitions.cons hs (ih h₂)

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseSelectorRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual root selector call and its typed Appendix A certificates.
The success and terminal conclusions, return instruction, and every-prefix
storage estimate all describe the same concrete execution. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement

open BitProgram StructuredCalls SparseDFSProgram SparsePriorityProgram

variable {n : ℕ}

/-- Normalized node syntax has a uniform polynomial bound for fixed `k`.
The binary threshold word is charged separately, with its actual bit length. -/
theorem inputVolume_le_formulaBound (F : RawCNF n) (base : List Bool) (k : ℕ)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hnodup : ∀ C ∈ F, C.Nodup)
    (hdistinct : (F.map ExecCNF.clauseSet).Nodup) :
    inputVolume F base ≤ SparseCountProgram.formulaBound n k + base.length + 1 := by
  have h := SparseCountProgram.encodeBody_length_le F k hnodup hdistinct
    (formulaSet_width_le F hwidth)
  unfold inputVolume
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Instantiate the loop invariant using actual normalized formulas, concrete
frontier bytes and the count-mass invariant. Only the concrete streamed leaf
execution remains an intermediate contract for integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

theorem visitTime_mono (k n a b thresholdLength leafTime bound : ℕ) (hab : a ≤ b) :
    visitTime k n a thresholdLength leafTime bound ≤
      visitTime k n b thresholdLength leafTime bound := by
  have hp := Nat.mul_le_mul_left (SparsePriorityProgram.Selector.selectorCoefficient k)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_right hab thresholdLength) 1) 4)
  have hq := Nat.mul_le_mul_left 621000
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hab) 3) 2)
  have hm := max_le_max hq (le_refl (leafTime + 100 * (n + 1)))
  unfold visitTime
  omega

/-- A closed outer loop relative to the actual finite leaf command's contract.
All other algorithmic services are the concrete routines in `body_refinement`.
The resource inequalities below are numerical envelopes, discharged by fixed
polynomials before exposing the final machine theorem. -/
theorem normalized_loop_oai (k : ℕ) (threshold : List Bool) (leaf : Code)
    (F : RawCNF n) (d : Data) (leafTime parameterBound bound : ℕ)
    (hk : 2 ≤ k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hb : Boundary threshold ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ d)
    (hdimension : BinaryArithmetic.toNat (d.stacks 264) =
      4 * BinaryArithmetic.toNat threshold ^ (k - 1))
    (hambient : BinaryArithmetic.toNat (d.stacks 267) = n)
    (hparameterLength : (d.stacks 264).length ≤ parameterBound)
    (hambientLength : (d.stacks 267).length ≤ n + 1)
    (hbound : ∀ i, (d.stacks i).length ≤ bound)
    (hpop : n + 1 + SparseDFSBoundarySpace.frontierBound (SparseCountProgram.formulaBound n k)
      (F.length * k) + 11 * SparseCountProgram.formulaBound n k + 13 ≤ bound)
    (hselect : (SparsePriorityProgram.Selector.selectorCoefficient k + 24) *
      (SparseCountProgram.formulaBound n k + threshold.length + 1) ^ 4 ≤ bound)
    (hbranch : SparseDFSBoundarySpace.frontierBound (SparseCountProgram.formulaBound n k)
      (F.length * k) + (n + 1) +
      620001 * (4 * SparseCountProgram.formulaBound n k + 3) ^ 2 ≤ bound)
    (hadd : 100 * (n + 1) ≤ bound)
    (hleaf : LeafContract (n := n) k threshold parameterBound leaf leafTime bound) :
    ∃ visits t e, t ≤ visits *
        (visitTime k n (SparseCountProgram.formulaBound n k) threshold.length leafTime bound + 1) + 1 ∧
      BoundedEval (loop k leaf) t d e bound ∧
      Boundary (n := n) threshold ⟨[], rawCount F⟩ e ∧
      Transitions k (BinaryArithmetic.toNat threshold) visits
        ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩ ⟨[], rawCount F⟩ := by
  let initial : Frontier n := ⟨[⟨ExecCNF.normalize SAT.Literal.negate F, 0⟩], 0⟩
  let I : Frontier n → Data → Prop := fun s e =>
    (∃ visits, Transitions k (BinaryArithmetic.toNat threshold) visits initial s) ∧
      Boundary threshold s e ∧ (∀ i, (e.stacks i).length ≤ bound) ∧
      BinaryArithmetic.toNat (e.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1) ∧
      BinaryArithmetic.toNat (e.stacks 267) = n ∧
      (e.stacks 264).length ≤ parameterBound ∧ (e.stacks 267).length ≤ n + 1
  have start : I initial d :=
    ⟨⟨0, .refl _⟩, hb, hbound, hdimension, hambient, hparameterLength, hambientLength⟩
  have step : ∀ (node : Node n) rest total e, I ⟨node :: rest, total⟩ e →
      ∃ next t, t ≤ visitTime k n (SparseCountProgram.formulaBound n k)
          threshold.length leafTime bound ∧ ∃ f, BoundedEval (body k leaf) t e f bound ∧
        Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧ I next f := by
    intro node rest total e invariant
    obtain ⟨⟨visits, trace⟩, boundary, sourceBound, dimension, ambient,
      parameterLength, ambientLength⟩ := invariant
    have valid := (trace.normalized_pending_invariants F hM hwidth).1 node (List.mem_cons_self)
    have bodyLen := SparseCountProgram.encodeBody_length_le node.formula k valid.literal_nodup
      valid.clause_nodup (formulaSet_width_le node.formula valid.width)
    have pendingLen := remaining_bytes_le F node rest hM hwidth trace
    have inputVolume := SparseSelectorRefinement.inputVolume_le_formulaBound node.formula threshold k
      valid.width valid.literal_nodup valid.clause_nodup
    obtain ⟨next, t, ht, f, he, transition, nextBoundary, setupFrame⟩ :=
      body_refinement threshold leaf node rest total parameterBound leafTime bound e hk hM valid boundary
        dimension ambient parameterLength ambientLength trace.next_sum_le_pow sourceBound
        (by omega)
        ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputVolume 4)).trans hselect)
        (by
          have hp := Nat.mul_le_mul_left 620001
            (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 4 bodyLen) 3) 2)
          omega)
        hadd hleaf
    refine ⟨next, t, ht.trans (visitTime_mono k n _ _ threshold.length leafTime bound bodyLen),
      f, he, transition, ?_⟩
    refine ⟨⟨visits + 1, trace.trans (.cons transition (.refl _))⟩,
      nextBoundary, he.final_bound, ?_, ?_, ?_, ?_⟩
    · rw [setupFrame 264 (by simp)]
      exact dimension
    · rw [setupFrame 267 (by simp)]
      exact ambient
    · rw [setupFrame 264 (by simp)]
      exact parameterLength
    · rw [setupFrame 267 (by simp)]
      exact ambientLength
  obtain ⟨visits, t, total, e, ht, he, transitions, final⟩ := DFSLoop.execute k
    (BinaryArithmetic.toNat threshold) threshold leaf
    (visitTime k n (SparseCountProgram.formulaBound n k) threshold.length leafTime bound)
    bound I hM (fun _ _ h => h.2.1) (fun _ _ h => h.2.2.1) step initial d start
  have total_eq : total = rawCount F := by
    simpa only [rawCount_normalize] using transitions.finished_count
  subst total
  exact ⟨visits, t, e, ht, he, final.2.1, transitions⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop_oai
