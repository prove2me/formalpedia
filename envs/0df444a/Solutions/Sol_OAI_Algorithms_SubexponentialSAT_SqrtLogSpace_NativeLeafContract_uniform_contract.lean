-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:40:57.608291+00:00
-- url     : https://prove2.me/submissions/a37d8292-251c-4c9c-926c-08733af609c7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_loadLeaf_input_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_local_execution
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafDispatch_command_execution
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafExecution_call_export_execution

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Sunflower
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The elementary sunflower bound and its literal-occurrence corollary. -/
namespace SubexponentialSAT.Sunflower

open Finset
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Distinct unit sets give the separately specified bound `L₁ = 1`. -/
theorem unit_literal_occurrence_le (F : Finset (Finset α)) (x : α) :
    (F.filter (fun s => s.card = 1 ∧ x ∈ s)).card ≤ 1 := by
  have hsub : F.filter (fun s => s.card = 1 ∧ x ∈ s) ⊆ {{x}} := by
    intro s hs
    obtain ⟨_, hcard, hx⟩ := mem_filter.mp hs
    apply mem_singleton.mpr
    obtain ⟨y, rfl⟩ := card_eq_one.mp hcard
    have hxy : x = y := mem_singleton.mp hx
    rw [hxy]
  simpa using card_le_card hsub


/-- Summing the width-specific degrees bounds the total degree of one literal. -/
theorem literal_total_occurrence_le (F : Finset (Finset α)) (k : ℕ)
    (b : ℕ → ℕ) (x : α) (hWidth : ∀ s ∈ F, s.card ≤ k)
    (hBound : ∀ j, j ≤ k →
      (F.filter (fun s => s.card = j ∧ x ∈ s)).card ≤ b j) :
    (F.filter (fun s => x ∈ s)).card ≤ ∑ j ∈ range (k + 1), b j := by
  have hsub : F.filter (fun s => x ∈ s) ⊆
      (range (k + 1)).biUnion (fun j => F.filter (fun s => s.card = j ∧ x ∈ s)) := by
    intro s hs
    obtain ⟨hsF, hxs⟩ := mem_filter.mp hs
    apply mem_biUnion.mpr
    refine ⟨s.card, mem_range.mpr ?_, mem_filter.mpr ⟨hsF, rfl, hxs⟩⟩
    have := hWidth s hsF
    omega
  calc
    (F.filter (fun s => x ∈ s)).card ≤
        ((range (k + 1)).biUnion
          (fun j => F.filter (fun s => s.card = j ∧ x ∈ s))).card := card_le_card hsub
    _ ≤ ∑ j ∈ range (k + 1), (F.filter (fun s => s.card = j ∧ x ∈ s)).card :=
      card_biUnion_le
    _ ≤ ∑ j ∈ range (k + 1), b j := by
      apply sum_le_sum
      intro j hj
      exact hBound j (by have := mem_range.mp hj; omega)

/-- A variable has two signs, so a common literal-degree cap gives twice that cap
for the number of clauses containing the variable. -/
theorem variable_occurrence_le_of_literal_bound {V : Type*} [DecidableEq V]
    (F : SAT.CNF V) (B : ℕ)
    (hBound : ∀ x : SAT.Literal V, (F.filter (fun s => x ∈ s)).card ≤ B) :
    SAT.OccurrenceAtMost (2 * B) F := by
  intro v
  let pos : SAT.Literal V := ⟨v, true⟩
  let neg : SAT.Literal V := ⟨v, false⟩
  have hsub : F.filter (fun C => ∃ l ∈ C, l.variable = v) ⊆
      (F.filter (fun C => pos ∈ C)) ∪ (F.filter (fun C => neg ∈ C)) := by
    intro C hC
    obtain ⟨hCF, l, hl, hv⟩ := mem_filter.mp hC
    rcases l with ⟨w, sign⟩
    change w = v at hv
    subst w
    cases sign with
    | false => exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hCF, hl⟩))
    | true => exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hCF, hl⟩))
  calc
    SAT.occurrences v F ≤
        ((F.filter (fun C => pos ∈ C)) ∪ (F.filter (fun C => neg ∈ C))).card :=
      card_le_card hsub
    _ ≤ (F.filter (fun C => pos ∈ C)).card +
        (F.filter (fun C => neg ∈ C)).card := card_union_le _ _
    _ ≤ B + B := Nat.add_le_add (hBound pos) (hBound neg)
    _ = 2 * B := by omega

end SubexponentialSAT.Sunflower

end OAI.Algorithms
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

private theorem mem_violating_of_degree {F : CNF (Fin n)} {M c : ℕ}
    {H : Clause (Fin n)} (hM : 0 < M) (hH : 0 < H.card) (hc : H.card < c)
    (hd : M ^ (c - H.card) ≤ degree F c H) :
    (c, H) ∈ violatingCandidates F M := by
  apply (mem_violatingCandidates F M c H).mpr
  have hpos : 0 < (selected F c H).card := lt_of_lt_of_le (pow_pos hM _) hd
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  exact ⟨⟨C, (mem_selected.mp hC).1, (mem_selected.mp hC).2⟩, hH, hc, hd⟩

theorem select_none_degree_lt {F : CNF (Fin n)} {M c : ℕ} {H : Clause (Fin n)}
    (hM : 0 < M) (h : select F M = none) (hH : 0 < H.card) (hc : H.card < c) :
    degree F c H < M ^ (c - H.card) := by
  by_contra hnot
  have hm := mem_violating_of_degree hM hH hc (Nat.le_of_not_gt hnot)
  have he : violatingCandidates F M = [] := List.argmin_eq_none.mp h
  simp [he] at hm


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriority
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sharp numerical budgets for disjoint counting sparsification

The frozen counting manuscript, Appendix A, lines 1991–2054. These numerical lemmas do not assert the
existence of a sparsification tree or a primitive implementation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget

open Finset
open scoped BigOperators

theorem sum_pow_le_twice_last (M : ℕ) (hM : 2 ≤ M) (j : ℕ) :
    ∑ i ∈ range (j + 1), M ^ i ≤ 2 * M ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ]
    have hp : 2 * M ^ j ≤ M ^ (j + 1) := by
      rw [pow_succ]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (M ^ j) hM
    omega

theorem occurrenceCap_le (k M : ℕ) (hk : 0 < k) (hM : 2 ≤ M) :
    occurrenceCap k M ≤ 4 * M ^ (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have h := sum_pow_le_twice_last M hM j
  dsimp [occurrenceCap]
  calc
    2 * ∑ i ∈ range (j + 1), M ^ i ≤ 2 * (2 * M ^ j) := Nat.mul_le_mul_left 2 h
    _ = 4 * M ^ (j + 1 - 1) := by simp; ring

open SparseCharging

theorem chooseExponent_spec (k a b : ℕ) (ha : 0 < a) :
    parameterTest k a b (chooseExponent k a b ha) = true :=
  Nat.find_spec (exists_parameter k a b ha)

theorem chooseM_spec (k a b : ℕ) (ha : 0 < a) :
    2 ≤ chooseM k a b ha ∧ rightConstant k ≤ chooseM k a b ha ∧
      rightConstant k * Nat.clog 2 (4 * depthConstant k (chooseM k a b ha) *
        chooseM k a b ha) * b ≤ a * chooseM k a b ha := by
  simpa only [parameterTest, chooseM, decide_eq_true_eq] using chooseExponent_spec k a b ha

/-- Terminality of the actual priority selector gives the sharp occurrence cap.
Unused variables contribute zero occurrences and are retained in the ambient type. -/
theorem leaf_occurrences_le {n : ℕ} (F : SAT.CNF (Fin n)) (k M : ℕ)
    (hM : 2 ≤ M) (hWidth : ∀ C ∈ F, C.card ≤ k)
    (hTerminal : SparsePriority.select F M = none) :
    ∀ v, SAT.occurrences v F ≤ occurrenceCap k M := by
  apply Sunflower.variable_occurrence_le_of_literal_bound F
    (∑ j ∈ range k, M ^ j)
  intro x
  calc
    (F.filter (fun C => x ∈ C)).card ≤
        ∑ j ∈ range (k + 1), if j = 0 then 0 else M ^ (j - 1) := by
      apply Sunflower.literal_total_occurrence_le F k _ x hWidth
      intro j _
      rcases j with _ | j
      · have hempty : F.filter (fun C => C.card = 0 ∧ x ∈ C) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro C hC
          obtain ⟨_, hc, hx⟩ := Finset.mem_filter.mp hC
          rw [Finset.card_eq_zero.mp hc] at hx
          simp at hx
        rw [hempty]
        simp
      · cases j with
        | zero => simpa using Sunflower.unit_literal_occurrence_le F x
        | succ j =>
          have hd := SparsePriority.select_none_degree_lt (F := F) (M := M)
            (c := j + 1 + 1) (H := {x}) (by omega) hTerminal (by simp) (by simp)
          simpa [SparsePriority.degree, DisjointBranch.selected] using hd.le
    _ = ∑ j ∈ range k, M ^ j := by rw [Finset.sum_range_succ']; simp

theorem leaf_occurrences_le_power {n : ℕ} (F : SAT.CNF (Fin n)) (k M : ℕ)
    (hk : 0 < k) (hM : 2 ≤ M) (hWidth : ∀ C ∈ F, C.card ≤ k)
    (hTerminal : SparsePriority.select F M = none) :
    ∀ v, SAT.occurrences v F ≤ 4 * M ^ (k - 1) := by
  intro v
  exact (leaf_occurrences_le F k M hM hWidth hTerminal v).trans (occurrenceCap_le k M hk hM)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
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

theorem seq (h : BoundedEval first t a b B) (g : BoundedEval second u b c B) :
    BoundedEval (.seq first second) (t + u) a c B :=
  ⟨h.eval.seq g.eval, StructuredSpace.sequence_stack_bound h.eval g.eval 256 256 h.space g.space
    (compiled (.seq first second) 256 256) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 256 256)⟩

end BoundedEval

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical leaf input facts after the actual terminal dispatcher. The
number of clauses is bounded using the disjoint selector's occurrence
estimate; no OR-cover leaf multiplicity is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafInput

open DisjointReuse DisjointReuse.SparseDFSRefinement DisjointReuse.DFSVisit

variable {n k parameterBound : ℕ}

/-- Valid raw syntax has one record per semantic clause. -/
theorem length_eq_card (F : RawCNF n) (hv : Valid k F) :
    F.length = (ExecCNF.formulaSet F).card := by
  simpa only [ExecCNF.formulaSet, List.length_map] using
    (List.toFinset_card_of_nodup hv.clause_nodup).symm

/-- The terminal empty-clause test agrees with the semantic set input. -/
theorem empty_not_mem (F : RawCNF n) (h : [] ∉ F) :
    (∅ : SAT.Clause (Fin n)) ∉ ExecCNF.formulaSet F := by
  intro hm
  obtain ⟨C, hC, he⟩ := ExecCNF.mem_formulaSet.mp hm
  have hz : C = [] := List.toFinset_eq_empty_iff C |>.mp he
  exact h (hz ▸ hC)

/-- Incidence counting for nonempty clauses. This is the source's elementary
clause bound, independent of the overlapping sparsification controller. -/
theorem card_le_occurrences (G : SAT.CNF (Fin n)) (B : ℕ)
    (hB : ∀ v, SAT.occurrences v G ≤ B)
    (hempty : (∅ : SAT.Clause (Fin n)) ∉ G) : G.card ≤ n * B := by
  let occ := fun v : Fin n => G.filter (fun C => ∃ l ∈ C, l.variable = v)
  have hcover : G ⊆ Finset.univ.biUnion occ := by
    intro C hC
    have hne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro he
      exact hempty (he ▸ hC))
    obtain ⟨l, hl⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨l.variable, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hC, l, hl, rfl⟩⟩
  calc
    G.card ≤ (Finset.univ.biUnion occ).card := Finset.card_le_card hcover
    _ ≤ ∑ v : Fin n, (occ v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, B := Finset.sum_le_sum (fun v _ => hB v)
    _ = n * B := by simp

/-- The occurrence word on physical stack264 bounds the actual record count.
Both the selector and the input remain over the declared ambient Fin n. -/
theorem clauses_le_physical_occurrence (F : RawCNF n)
    (threshold : List Bool) (a : StructuredProgram.State 80 1220)
    (hk : 0 < k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hv : Valid k F) (hr : LeafReady k threshold parameterBound F a)
    (hs : SparsePriority.select (ExecCNF.formulaSet F)
      (BinaryArithmetic.toNat threshold) = none) (hempty : [] ∉ F) :
    F.length ≤ n * BinaryArithmetic.toNat (a.stacks 264) := by
  have ho := SparseBudget.leaf_occurrences_le_power (ExecCNF.formulaSet F) k
    (BinaryArithmetic.toNat threshold) hk hM (formulaSet_width_le F hv.width) hs
  rw [length_eq_card F hv, hr.dimension]
  exact card_le_occurrences _ _ ho (empty_not_mem F hempty)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafInput
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete shared-ABI loading, local execution and whole-count export for a
DFS leaf. The local command remains explicit; its actual execution proof is
supplied by the streamed leaf construction. No new machine service is defined. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution

open BitProgram StructuredCalls DisjointReuse DFSVisit

theorem outside_leaf_low (i : Fin 1220) (hi : i.val < 320) :
    ¬ ∃ j, ABI.leafStacks j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change 320 + j.val = i.val at hv
  omega

/-- Concrete input words, empty worker ports and reset registers are produced
by the loader. The local bound depends on those input sizes independently of
the suspended DFS frame. The caller supplies a proof of the explicit local
command, rather than an abstract evaluator or layout service. -/
theorem command_execution {n k parameterBound B localBound localTime : ℕ}
    (threshold : List Bool) (F : RawCNF n) (a : Data) (localCommand : Cmd 40 896)
    (hv : SparseDFSRefinement.Valid k F)
    (hr : LeafReady k threshold parameterBound F a)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hB : localBound ≤ B)
    (hlocal : ∀ d : LocalData,
      d.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      BinaryArithmetic.toNat (d.stacks 786) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) →
      (∀ i, (d.stacks i).length ≤
        SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → d.stacks i = []) →
      (∀ i, d.regs i = false) →
      ∃ steps ≤ localTime, ∃ e, Eval localCommand steps d e ∧
        e.stacks 788 = countWord (rawCount F) ∧
        ∀ q z, q ≤ steps → Trace (compiled localCommand 784 788) q
          (d.withPC (some (compiled localCommand 784 788).entry)) z →
          ∀ i, (z.stacks i).length ≤ localBound) :
    ∃ steps ≤ 3618 * B + localTime + 5446, ∃ e,
      BoundedEval (command localCommand) steps a e B ∧ LeafDone F a e ∧
      e.stacks 1219 = [] ∧ (∀ j, e.stacks (ABI.leafStacks j) = []) ∧
      (∀ i, (¬ ∃ j, ABI.leafStacks j = i) → i ≠ 263 → i ≠ 1219 →
        e.stacks i = a.stacks i) := by
  obtain ⟨loadSteps, b, hload, first, hformula, hn, hdimension, hsize,
      hempty, hregs, hframe⟩ := Native.loadLeaf_input_bound threshold F a hv hr ha
  obtain ⟨localSteps, hlocalSteps, c, he, hout, hp⟩ :=
    hlocal (projectState ABI.leafRegisters ABI.leafStacks b)
      hformula hn hdimension hsize hempty hregs
  obtain ⟨tailSteps, htail, e, second, hcount, hs, hclear, htailFrame⟩ :=
    call_export_execution localCommand b c he hp first.final_bound hB
  have frame (i : Fin 1220) (hi : ¬ ∃ j, ABI.leafStacks j = i)
      (hi263 : i ≠ 263) (hi1219 : i ≠ 1219) : e.stacks i = a.stacks i :=
    (htailFrame i hi hi263 hi1219).trans (hframe i hi hi1219)
  refine ⟨_, by omega, e, first.seq second, ?_, hs, hclear, frame⟩
  constructor
  · exact hcount.trans hout
  · exact (frame 30 (outside_leaf_low 30 (by decide)) (by decide) (by decide)).trans
      (hr.low_empty 30 (by decide))
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact frame _ (outside_leaf_low _ (by decide)) (by decide) (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform correctness and resources for the fixed native leaf. The final
contract instantiates the actual preparation, marked rounds and accepted
query; only numerical bounds produced by the outer program remain. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
open BitProgram StructuredCalls DisjointReuse DFSVisit SparseDFSRefinement

private theorem dispatch_total_time_le (steps bound localTime body formula n : ℕ)
    (ht : steps ≤ 6 * bound + 100 * (body + 1) + 11 * n +
      (3618 * bound + localTime + 5446) + 33)
    (hbody : body ≤ formula) :
    steps ≤ 3624 * bound + 100 * (formula + 1) + 11 * n + localTime + 5479 := by
  calc
    steps ≤ 6 * bound + 100 * (body + 1) + 11 * n +
        (3618 * bound + localTime + 5446) + 33 := ht
    _ ≤ 6 * bound + 100 * (formula + 1) + 11 * n +
        (3618 * bound + localTime + 5446) + 33 := by gcongr
    _ = 3624 * bound + 100 * (formula + 1) + 11 * n + localTime + 5479 := by ring

/-- The concrete terminal classifier, paid loading and full-word export use
one unchanged global stack cap. The remaining premise is the actual fixed
local command at the loader-produced input, discharged below by its query run. -/
theorem execution {n k parameterBound bound localBound localTime : ℕ}
    (threshold : List Bool) (F : RawCNF n) (a : State 80 1220)
    (hk : 0 < k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hv : Valid k F) (hr : LeafReady k threshold parameterBound F a)
    (hselect : SparsePriority.select (ExecCNF.formulaSet F)
      (BinaryArithmetic.toNat threshold) = none)
    (ha : ∀ i, (a.stacks i).length ≤ bound)
    (hlocalBound : localBound ≤ bound)
    (hclassifier : 101 * SparseCountProgram.formulaBound n k + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound)
    (hlocal : [] ∉ F → F ≠ [] →
      F.length ≤ n * (4 * BinaryArithmetic.toNat threshold ^ (k - 1)) →
      ∀ d : State 40 896,
      d.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      BinaryArithmetic.toNat (d.stacks 786) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) →
      (∀ i, (d.stacks i).length ≤
        SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → d.stacks i = []) →
      (∀ i, d.regs i = false) →
      ∃ steps ≤ localTime, ∃ e, Eval (NativeLeafProgram.localCommand k) steps d e ∧
        e.stacks 788 = countWord (rawCount F) ∧
        ∀ q z, q ≤ steps → Trace (NativeLeafProgram.localProgram k) q
          (d.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
          ∀ i, (z.stacks i).length ≤ localBound) :
    ∃ steps ≤ time n k localTime bound, ∃ e,
      BoundedEval (NativeLeafProgram.command k) steps a e bound ∧ LeafDone F a e := by
  have hbody : (a.stacks 265).length ≤ SparseCountProgram.formulaBound n k := by
    rw [hr.current]
    exact SparseCountProgram.encodeBody_length_le F k hv.literal_nodup hv.clause_nodup
      (formulaSet_width_le F hv.width)
  obtain ⟨steps, ht, e, he, hd⟩ := NativeLeafDispatch.command_execution
    (NativeLeafExecution.command (NativeLeafProgram.localCommand k))
    (3618 * bound + localTime + 5446) bound hr ha (by omega) hpower (by
      intro hz hn hready hframe
      have hm := NativeLeafInput.clauses_le_physical_occurrence F threshold a
        hk hM hv hr hselect hz
      rw [hr.dimension] at hm
      obtain ⟨t, htime, out, hrun, hdone, _, _, _⟩ :=
        NativeLeafExecution.command_execution threshold F _
          (NativeLeafProgram.localCommand k) hv hready hframe hlocalBound
          (hlocal hz hn hm)
      exact ⟨t, htime, out, hrun, hdone⟩)
  refine ⟨steps, ?_, e, he, hd⟩
  unfold time
  exact dispatch_total_time_le steps bound localTime (a.stacks 265).length
    (SparseCountProgram.formulaBound n k) n ht hbody

/-- Uniformly package the actual fixed-command executions for the existing
DFS contract. This is an internal composition lemma, not a final theorem
assuming a counting evaluator. -/
theorem contract_of_local_execution {n k parameterBound bound localBound localTime : ℕ}
    (threshold : List Bool) (hk : 0 < k) (hM : 2 ≤ BinaryArithmetic.toNat threshold)
    (hlocalBound : localBound ≤ bound)
    (hclassifier : 101 * SparseCountProgram.formulaBound n k + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound)
    (hlocal : ∀ F : RawCNF n, Valid k F → [] ∉ F → F ≠ [] →
      F.length ≤ n * (4 * BinaryArithmetic.toNat threshold ^ (k - 1)) →
      ∀ d : State 40 896,
      d.stacks 784 = SparseCountProgram.encodeBody F →
      BinaryArithmetic.toNat (d.stacks 785) = n →
      BinaryArithmetic.toNat (d.stacks 786) =
        4 * BinaryArithmetic.toNat threshold ^ (k - 1) →
      (∀ i, (d.stacks i).length ≤
        SparseCountProgram.formulaBound n k + (n + 1) + parameterBound) →
      (∀ i, i ≠ 784 → i ≠ 785 → i ≠ 786 → d.stacks i = []) →
      (∀ i, d.regs i = false) →
      ∃ steps ≤ localTime, ∃ e, Eval (NativeLeafProgram.localCommand k) steps d e ∧
        e.stacks 788 = countWord (rawCount F) ∧
        ∀ q z, q ≤ steps → Trace (NativeLeafProgram.localProgram k) q
          (d.withPC (some (NativeLeafProgram.localProgram k).entry)) z →
          ∀ i, (z.stacks i).length ≤ localBound) :
    LeafContract (n := n) k threshold parameterBound (NativeLeafProgram.command k)
      (time n k localTime bound) bound := by
  constructor
  intro F a hv hr hs ha
  exact execution threshold F a hk hM hv hr hs ha hlocalBound hclassifier hpower
    (hlocal F hv)

open SqrtLog Filter
open scoped Topology

/-- Uniform counting contract for the fixed native leaf. The remaining
hypotheses concern only numerical caps chosen by the outer program. There
is no local execution, query evaluator, successful code or resource service
premise. -/
theorem uniform_contract_oai (k parameterCoefficient parameterDegree : ℕ) (hk : 2 ≤ k) :
    ∃ Cs spaceDegree : ℕ, ∃ Ct At : ℝ, ∃ timeDegree cutoff : ℕ,
      1 ≤ Ct ∧ 1 ≤ At ∧ 1 ≤ timeDegree ∧
      ∀ n inputLength parameterBound bound : ℕ, cutoff ≤ n → n ≤ inputLength →
      parameterBound ≤ parameterCoefficient * (inputLength + 1) ^ parameterDegree →
      ∀ threshold : List Bool,
      BinaryArithmetic.toNat threshold = SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) →
      Cs * (inputLength + 1) ^ spaceDegree ≤ bound →
      101 * SparseCountProgram.formulaBound n k + 103 ≤ bound → 5 * n + 6 ≤ bound →
      LeafContract (n := n) k threshold parameterBound (NativeLeafProgram.command k)
        (time n k (Nat.ceil (SqrtLog.Statement.runtimeBound Ct At timeDegree inputLength n)) bound)
        bound := by
  obtain ⟨Cs, spaceDegree, Ct, At, timeDegree, cutoff, hCt, hAt, hdegree, hlocal⟩ :=
    local_execution k parameterCoefficient parameterDegree hk
  refine ⟨Cs, spaceDegree, Ct, At, timeDegree, cutoff, hCt, hAt, hdegree, ?_⟩
  intro n inputLength parameterBound bound hcut hnI hp threshold hthreshold hlocalBound hclassifier hpower
  apply contract_of_local_execution threshold (by omega) (by
    rw [hthreshold]
    exact (SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by omega)).1)
    hlocalBound hclassifier hpower
  intro F hv _hempty hne hmB a hformula hn hBword ha hempty _hregs
  exact hlocal n inputLength parameterBound hcut hnI hp F a hv hne
    (by simpa only [hthreshold] using hmB) ha hempty hformula hn
    (by simpa only [hthreshold] using hBword)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract_oai
