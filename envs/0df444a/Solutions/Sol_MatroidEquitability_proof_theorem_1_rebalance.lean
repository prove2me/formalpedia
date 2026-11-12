-- Prove2me | solution 1 for MatroidEquitability.proof_theorem_1_rebalance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:47.732748+00:00
-- url     : https://prove2.me/submissions/b6e53045-bf13-4529-a0d8-57388a43f7b6

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBasePartition
import Definitions.Def_MatroidEquitability_IsBlock

section
namespace MatroidEquitability

theorem chk_proof_theorem_1_rebalance {α : Type*} (M : Matroid α) [M.Finite] {k : ℕ} (w : α → ℝ)
    (B : Fin k → Set α) (hB : IsBasePartition M B) (i j : Fin k)
    (hi : ∀ t, setWeight w (B t) ≤ setWeight w (B i))
    (hj : ∀ t, setWeight w (B j) ≤ setWeight w (B t))
    (hgap : 1 < setWeight w (B i) - setWeight w (B j)) (B' : Set α)
    (hB' : IsBlock (M.restrict (B i ∪ B j)) B')
    (hbal : |setWeight w B' - setWeight w ((B i ∪ B j) \ B')| ≤ 1) :
    IsBlock (M.restrict (B i ∪ B j)) (B i) ∧
    IsBasePartition M (Function.update (Function.update B i B') j ((B i ∪ B j) \ B')) ∧
    ∃ m', IsGreatest (Set.range fun t =>
          setWeight w (Function.update (Function.update B i B') j ((B i ∪ B j) \ B') t)) m' ∧
      (m' < setWeight w (B i) ∨
        (m' = setWeight w (B i) ∧
          {t | setWeight w (Function.update (Function.update B i B') j ((B i ∪ B j) \ B') t) = m'}.ncard
            < {t | setWeight w (B t) = setWeight w (B i)}.ncard)) := by
  obtain ⟨hbase, hdisj, hcover⟩ := hB
  have hij : i ≠ j := by
    rintro rfl
    linarith
  have hdij : Disjoint (B i) (B j) := hdisj hij
  have hBsub : ∀ t, B t ⊆ M.E := fun t => (hbase t).subset_ground
  have hE'sub : B i ∪ B j ⊆ M.E := Set.union_subset (hBsub i) (hBsub j)
  have hspan : M.Spanning (B i ∪ B j) :=
    (hbase i).spanning.superset Set.subset_union_left hE'sub
  have hrb : ∀ X, (M.restrict (B i ∪ B j)).IsBase X → M.IsBase X :=
    fun X h => ((hspan.isBase_restrict_iff).1 h).1
  have hdiff : (B i ∪ B j) \ B i = B j := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union]
    constructor
    · rintro ⟨h | h, h2⟩
      · exact absurd h h2
      · exact h
    · intro h
      exact ⟨Or.inr h, fun h2 => Set.disjoint_left.1 hdij h2 h⟩
  have hB'1 : M.IsBase B' := hrb _ hB'.1
  have hB'2 : M.IsBase ((B i ∪ B j) \ B') := by
    have := hrb _ hB'.2
    simpa using this
  have hB'sub : B' ⊆ B i ∪ B j := fun x hx => by
    have := hB'.1.subset_ground
    simpa using this hx
  -- weights
  have hfin : (B i ∪ B j).Finite := M.ground_finite.subset hE'sub
  have hsum : setWeight w B' + setWeight w ((B i ∪ B j) \ B') =
      setWeight w (B i) + setWeight w (B j) := by
    unfold setWeight
    rw [← finsum_mem_union Set.disjoint_sdiff_right (hfin.subset hB'sub) hfin.sdiff,
      Set.union_sdiff_cancel hB'sub, finsum_mem_union hdij (M.ground_finite.subset (hBsub i))
        (M.ground_finite.subset (hBsub j))]
  have hlt1 : setWeight w B' < setWeight w (B i) := by
    rw [abs_le] at hbal; linarith
  have hlt2 : setWeight w ((B i ∪ B j) \ B') < setWeight w (B i) := by
    rw [abs_le] at hbal; linarith
  set B2 := Function.update (Function.update B i B') j ((B i ∪ B j) \ B') with hB2
  have hB2i : B2 i = B' := by simp [hB2, hij]
  have hB2j : B2 j = (B i ∪ B j) \ B' := by simp [hB2]
  have hB2t : ∀ t, t ≠ i → t ≠ j → B2 t = B t := by
    intro t h1 h2; simp [hB2, h1, h2]
  have hB2sub : ∀ t, (t = i ∨ t = j) → B2 t ⊆ B i ∪ B j := by
    rintro t (rfl | rfl)
    · rw [hB2i]; exact hB'sub
    · rw [hB2j]; exact Set.sdiff_subset
  have hB2base : ∀ t, M.IsBase (B2 t) := by
    intro t
    by_cases h1 : t = i
    · subst h1; rw [hB2i]; exact hB'1
    by_cases h2 : t = j
    · subst h2; rw [hB2j]; exact hB'2
    rw [hB2t t h1 h2]; exact hbase t
  have hpart : IsBasePartition M B2 := by
    refine ⟨hB2base, ?_, ?_⟩
    · intro s t hst
      simp only [Function.onFun]
      by_cases hs : s = i ∨ s = j
      · by_cases ht : t = i ∨ t = j
        · -- both in {i, j}
          rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
          · exact absurd rfl hst
          · rw [hB2i, hB2j]; exact Set.disjoint_sdiff_right
          · rw [hB2i, hB2j]; exact Set.disjoint_sdiff_left
          · exact absurd rfl hst
        · push Not at ht
          rw [hB2t t ht.1 ht.2]
          refine Disjoint.mono_left (hB2sub s hs) ?_
          exact Set.disjoint_union_left.2 ⟨hdisj (Ne.symm ht.1), hdisj (Ne.symm ht.2)⟩
      · push Not at hs
        rw [hB2t s hs.1 hs.2]
        by_cases ht : t = i ∨ t = j
        · refine Disjoint.mono_right (hB2sub t ht) ?_
          exact Set.disjoint_union_right.2 ⟨hdisj hs.1, hdisj hs.2⟩
        · push Not at ht
          rw [hB2t t ht.1 ht.2]; exact hdisj hst
    · apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun t => (hB2base t).subset_ground
      · rw [← hcover]
        intro x hx
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hx
        refine Set.mem_iUnion.2 ?_
        by_cases h1 : t = i ∨ t = j
        · have hxE : x ∈ B i ∪ B j := by rcases h1 with rfl | rfl <;> simp [ht]
          by_cases hx' : x ∈ B'
          · exact ⟨i, by rw [hB2i]; exact hx'⟩
          · exact ⟨j, by rw [hB2j]; exact ⟨hxE, hx'⟩⟩
        · push Not at h1
          exact ⟨t, by rw [hB2t t h1.1 h1.2]; exact ht⟩
  have hW2 : ∀ t, setWeight w (B2 t) ≤ setWeight w (B i) := by
    intro t
    by_cases h1 : t = i
    · subst h1; rw [hB2i]; exact hlt1.le
    by_cases h2 : t = j
    · subst h2; rw [hB2j]; exact hlt2.le
    rw [hB2t t h1 h2]; exact hi t
  refine ⟨⟨(hspan.isBase_restrict_iff).2 ⟨hbase i, Set.subset_union_left⟩, ?_⟩, hpart, ?_⟩
  · rw [Matroid.restrict_ground_eq, hdiff]
    exact (hspan.isBase_restrict_iff).2 ⟨hbase j, Set.subset_union_right⟩
  · have : Nonempty (Fin k) := ⟨i⟩
    obtain ⟨x, hx⟩ := Finite.exists_max (fun t => setWeight w (B2 t))
    refine ⟨setWeight w (B2 x), ⟨⟨x, rfl⟩, ?_⟩, ?_⟩
    · rintro _ ⟨y, rfl⟩; exact hx y
    · have hle : setWeight w (B2 x) ≤ setWeight w (B i) := hW2 x
      rcases hle.lt_or_eq with h | h
      · exact Or.inl h
      · right
        refine ⟨h, ?_⟩
        rw [h]
        apply Set.ncard_lt_ncard _ (Set.toFinite _)
        refine ⟨?_, ?_⟩
        · intro t ht
          simp only [Set.mem_setOf_eq] at ht ⊢
          by_cases h1 : t = i
          · subst h1; rfl
          by_cases h2 : t = j
          · subst h2; rw [hB2j] at ht; linarith
          rwa [hB2t t h1 h2] at ht
        · intro hsub
          have := hsub (show i ∈ {t | setWeight w (B t) = setWeight w (B i)} from rfl)
          simp only [Set.mem_setOf_eq] at this
          rw [hB2i] at this
          linarith

end MatroidEquitability
end

theorem solution : type_of% @MatroidEquitability.chk_proof_theorem_1_rebalance := @MatroidEquitability.chk_proof_theorem_1_rebalance
