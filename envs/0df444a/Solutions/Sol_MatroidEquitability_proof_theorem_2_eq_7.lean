-- Prove2me | solution 1 for MatroidEquitability.proof_theorem_2_eq_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:48.885509+00:00
-- url     : https://prove2.me/submissions/83957519-431a-4b82-be0b-1b380d9f82e8

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBlock
import Definitions.Def_MatroidEquitability_IsExchangeable
import Theorems.Thm_MatroidEquitability_theorem_3_exists

section
open scoped symmDiff


namespace MatroidEquitability.Dev.Core

open MatroidEquitability

lemma sw_union {α : Type*} (u : α → ℝ) {A C : Set α} (h : Disjoint A C) (hA : A.Finite)
    (hC : C.Finite) : setWeight u (A ∪ C) = setWeight u A + setWeight u C :=
  finsum_mem_union h hA hC

lemma sw_ncard {α : Type*} {A : Set α} (hA : A.Finite) :
    setWeight (fun _ => (1 : ℝ)) A = A.ncard := by
  unfold setWeight
  rw [finsum_mem_eq_finite_toFinset_sum _ hA]
  simp [Set.ncard_eq_toFinset_card _ hA]

lemma sw_symmDiff {α : Type*} (u : α → ℝ) {A X : Set α} (hA : A.Finite) (hX : X.Finite) :
    setWeight u (A ∆ X) = setWeight u A - setWeight u (X ∩ A) + setWeight u (X \ A) := by
  have h1 : A = (A \ X) ∪ (X ∩ A) := by ext; simp; tauto
  have h2 : A ∆ X = (A \ X) ∪ (X \ A) := rfl
  have d1 : Disjoint (A \ X) (X ∩ A) := by
    rw [Set.disjoint_left]; intro a ha hb; exact ha.2 hb.1
  have d2 : Disjoint (A \ X) (X \ A) := by
    rw [Set.disjoint_left]; intro a ha hb; exact hb.2 ha.1
  have e1 := sw_union u d1 (hA.subset Set.sdiff_subset) (hX.subset Set.inter_subset_left)
  have e2 := sw_union u d2 (hA.subset Set.sdiff_subset) (hX.subset Set.sdiff_subset)
  rw [← h1] at e1
  rw [h2, e2]; linarith

lemma ncard_symmDiff' {α : Type*} {A X : Set α} (hA : A.Finite) (hX : X.Finite) :
    ((A ∆ X).ncard : ℝ) = A.ncard - (X ∩ A).ncard + (X \ A).ncard := by
  have := sw_symmDiff (fun _ => (1:ℝ)) hA hX
  rwa [sw_ncard (hA.symmDiff hX), sw_ncard hA, sw_ncard (hX.subset Set.inter_subset_left),
    sw_ncard (hX.subset Set.sdiff_subset)] at this


lemma exch_core {α : Type*} (M : Matroid α) [M.Finite] (u : α → ℝ)
    (hu : ∀ e ∈ M.E, 0 ≤ u e ∧ u e ≤ 1) (S : Set α) (hS : S = {e ∈ M.E | u e = 1})
    (P Q : Set α) (hP : M.IsBase P) (hdisj : Disjoint P Q) (hU : P ∪ Q = M.E)
    (t : α) (ht : t ∈ Q \ S) (X : Set α) (hX : IsExchangeable M P Q t S X) :
    M.E \ (P ∆ X) = Q ∆ X ∧ M.E \ (Q ∆ X) = P ∆ X ∧
    setWeight u (P ∆ X) = setWeight u P - 1 + u t ∧
    setWeight u (Q ∆ X) = setWeight u Q + 1 - u t ∧ 0 ≤ u t ∧ u t < 1 := by
  obtain ⟨-, hXPQ, htX, hXS, hb1, -⟩ := hX
  have hfin : M.E.Finite := M.ground_finite
  have hPf : P.Finite := hfin.subset (hU ▸ Set.subset_union_left)
  have hQf : Q.Finite := hfin.subset (hU ▸ Set.subset_union_right)
  have hXf : X.Finite := (hPf.union hQf).subset hXPQ
  have hXP : X \ P = X ∩ Q := by
    ext e; simp only [Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hXPQ h1).resolve_left h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => Set.disjoint_left.mp hdisj h h2⟩
  have hXQ : X \ Q = X ∩ P := by
    ext e; simp only [Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hXPQ h1).resolve_right h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => Set.disjoint_left.mp hdisj h2 h⟩
  have hE1 : M.E \ (P ∆ X) = Q ∆ X := by
    ext e
    have := fun h : e ∈ M.E => (hU ▸ h : e ∈ P ∪ Q)
    have h2 : e ∈ X → e ∈ P ∪ Q := fun h => hXPQ h
    have hd : ¬ (e ∈ P ∧ e ∈ Q) := fun h => Set.disjoint_left.mp hdisj h.1 h.2
    simp only [Set.mem_sdiff, Set.symmDiff_def, Set.mem_union, Set.mem_sdiff, ← hU] at *
    tauto
  have hE2 : M.E \ (Q ∆ X) = P ∆ X := by
    ext e
    have h2 : e ∈ X → e ∈ P ∪ Q := fun h => hXPQ h
    have hd : ¬ (e ∈ P ∧ e ∈ Q) := fun h => Set.disjoint_left.mp hdisj h.1 h.2
    simp only [Set.mem_sdiff, Set.symmDiff_def, Set.mem_union, Set.mem_sdiff, ← hU] at *
    tauto
  -- weights of the pieces
  have htE : t ∈ M.E := hU ▸ Or.inr ht.1
  have hut : 0 ≤ u t ∧ u t < 1 := by
    refine ⟨(hu t htE).1, lt_of_le_of_ne (hu t htE).2 ?_⟩
    intro h; apply ht.2; rw [hS]; exact ⟨htE, h⟩
  have hone : ∀ e ∈ X, e ≠ t → u e = 1 := by
    intro e he het
    have := hXS he
    rcases this with h | h
    · exact absurd h het
    · rw [hS] at h; exact h.2
  have hXPf : (X ∩ P).Finite := hXf.subset Set.inter_subset_left
  have hXQf : (X ∩ Q).Finite := hXf.subset Set.inter_subset_left
  have wXP : setWeight u (X ∩ P) = (X ∩ P).ncard := by
    rw [← sw_ncard hXPf]
    unfold setWeight
    refine finsum_mem_congr rfl ?_
    intro e he
    apply hone e he.1
    rintro rfl
    exact Set.disjoint_left.mp hdisj he.2 ht.1
  have tXQ : t ∈ X ∩ Q := ⟨htX, ht.1⟩
  have wXQ : setWeight u (X ∩ Q) = u t + ((X ∩ Q).ncard - 1 : ℝ) := by
    have hsplit : X ∩ Q = insert t ((X ∩ Q) \ {t}) := by
      ext e; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · intro h; by_cases h' : e = t
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
      · rintro (rfl | h)
        · exact tXQ
        · exact h.1
    have hrest : (((X ∩ Q) \ {t})).Finite := hXQf.subset Set.sdiff_subset
    have h1 : setWeight u (X ∩ Q) = u t + setWeight u ((X ∩ Q) \ {t}) := by
      conv_lhs => rw [hsplit]
      unfold setWeight
      rw [finsum_mem_insert _ (by simp) hrest]
    have h2 : setWeight u ((X ∩ Q) \ {t}) = ((X ∩ Q) \ {t}).ncard := by
      rw [← sw_ncard hrest]
      unfold setWeight
      refine finsum_mem_congr rfl ?_
      intro e he
      exact hone e he.1.1 he.2
    have h3 := Set.ncard_sdiff_singleton_add_one tXQ hXQf
    have h3' : (((X ∩ Q) \ {t}).ncard : ℝ) = (X ∩ Q).ncard - 1 := by
      have : (((X ∩ Q) \ {t}).ncard : ℝ) + 1 = (X ∩ Q).ncard := by exact_mod_cast h3
      linarith
    rw [h1, h2, h3']
  have hcard : ((P ∆ X).ncard : ℝ) = P.ncard := by
    exact_mod_cast hb1.ncard_eq_ncard_of_isBase hP
  have hc := ncard_symmDiff' hPf hXf
  rw [hXP] at hc
  have hn : ((X ∩ P).ncard : ℝ) = (X ∩ Q).ncard := by linarith
  have s1 := sw_symmDiff u hPf hXf
  have s2 := sw_symmDiff u hQf hXf
  rw [hXP, wXP, wXQ] at s1
  rw [hXQ, wXP, wXQ] at s2
  refine ⟨hE1, hE2, ?_, ?_, hut.1, hut.2⟩
  · rw [s1, hn]; ring
  · rw [s2, hn]; ring

end MatroidEquitability.Dev.Core

namespace MatroidEquitability

/-- The claim (7) of the proof of Theorem 2. -/
theorem chk_proof_theorem_2_eq_7 {α : Type*} (M : Matroid α) [M.Finite] (u : α → ℝ)
    (hu : ∀ e ∈ M.E, 0 ≤ u e ∧ u e ≤ 1) (S : Set α) (hS : S = {e ∈ M.E | u e = 1}) (B : Set α)
    (hB : IsBlock M B)
    (hgap : ∀ C, IsBlock M C → ¬ (setWeight u B - 1 ≤ setWeight u C ∧ setWeight u C < setWeight u B)) :
    ((B ∩ S).ncard : ℝ) ≤ (S.ncard : ℝ) / 2 := by
  by_contra hcon
  push_neg at hcon
  have hSE : S ⊆ M.E := by rw [hS]; exact fun e he => he.1
  have hSf : S.Finite := M.ground_finite.subset hSE
  have hBE : B ⊆ M.E := hB.1.subset_ground
  have hdisj : Disjoint B (M.E \ B) := Set.disjoint_sdiff_right
  have hU : B ∪ (M.E \ B) = M.E := Set.union_diff_cancel hBE
  have hDS : (M.E \ B) ∩ S = S \ B := by
    ext e; simp only [Set.mem_inter_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨_, h⟩, h2⟩; exact ⟨h2, h⟩
    · rintro ⟨h, h2⟩; exact ⟨⟨hSE h, h2⟩, h⟩
  have hsum := Set.ncard_inter_add_ncard_diff_eq_ncard S B hSf
  have hsum' : ((S ∩ B).ncard : ℝ) + (S \ B).ncard = S.ncard := by exact_mod_cast hsum
  have hcomm : S ∩ B = B ∩ S := Set.inter_comm _ _
  rw [hcomm] at hsum'
  have hcard : ((M.E \ B) ∩ S).ncard < (B ∩ S).ncard := by
    rw [hDS]
    have : ((S \ B).ncard : ℝ) < (B ∩ S).ncard := by linarith
    exact_mod_cast this
  obtain ⟨t, ht, X, hX⟩ := theorem_3_exists M B (M.E \ B) S hB.1 hB.2 hdisj hSE hcard
  obtain ⟨hE1, -, w1, -, h0, h1⟩ := Dev.Core.exch_core M u hu S hS B (M.E \ B) hB.1 hdisj hU t ht X hX
  have hblock : IsBlock M (B ∆ X) := by
    refine ⟨hX.2.2.2.2.1, ?_⟩
    rw [hE1]; exact hX.2.2.2.2.2
  exact hgap _ hblock ⟨by linarith, by linarith⟩

end MatroidEquitability
end

theorem solution : type_of% @MatroidEquitability.chk_proof_theorem_2_eq_7 := @MatroidEquitability.chk_proof_theorem_2_eq_7
