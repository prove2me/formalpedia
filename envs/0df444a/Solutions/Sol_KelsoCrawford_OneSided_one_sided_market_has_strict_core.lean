-- Prove2me | solution 1 for KelsoCrawford.OneSided.one_sided_market_has_strict_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T11:42:54.806979+00:00
-- url     : https://prove2.me/submissions/be949d5b-9461-4172-9c5b-dd99fb8e7741

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_KelsoCrawford_OneSided_OneSided

set_option autoImplicit false

namespace KC09dd81b6

open KelsoCrawford.OneSided

theorem mono {W : Type} [DecidableEq W] (v : Finset W → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C) {D E : Finset W} (h : D ⊆ E) :
    v D ≤ v E := by
  have key : ∀ S : Finset W, v D ≤ v (S ∪ D) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S _ ih =>
      rw [Finset.insert_union]
      have := hMP a (S ∪ D)
      linarith
  have := key (E \ D)
  rwa [Finset.sdiff_union_of_subset h] at this

theorem sub_step {W : Type} [Fintype W] [DecidableEq W] (v : Finset W → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hGS : GrossSubstitutesOn v Set.univ) (i : W) (C : Finset W) (hi : i ∉ C) :
    v (insert i C) ≤ v C + v {i} := by
  by_contra hcon
  push_neg at hcon
  set t : ℝ := (v {i} + (v (insert i C) - v C)) / 2 with ht
  have hvi : 0 ≤ v {i} := by
    have := hMP i ∅; simpa [hNFL] using this
  have ht1 : v {i} < t := by rw [ht]; linarith
  have ht2 : t < v (insert i C) - v C := by rw [ht]; linarith
  have htpos : 0 < t := by linarith
  have hvU : 0 ≤ v Finset.univ := by
    have := mono v hMP (Finset.empty_subset (Finset.univ : Finset W)); linarith
  set B : ℝ := v Finset.univ + t with hB
  have hBpos : 0 < B := by rw [hB]; linarith
  let s : W → ℝ := fun j => if j = i then t else if j ∈ C then 0 else B
  let s' : W → ℝ := fun j => if j = i then t else B
  have hs_nn : ∀ j, 0 ≤ s j := by
    intro j; simp only [s]; split_ifs <;> linarith
  have hs'_nn : ∀ j, 0 ≤ s' j := by
    intro j; simp only [s']; split_ifs <;> linarith
  have hle : s ≤ s' := by
    intro j; simp only [s, s']; split_ifs <;> linarith
  have hpC : profit v (insert i C) s = v (insert i C) - t := by
    unfold profit
    rw [Finset.sum_insert hi]
    have : ∑ j ∈ C, s j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [s, hji, hj]
    simp only [s, if_pos rfl] at this ⊢
    rw [this]; ring
  have hvC0 : 0 ≤ v (insert i C) := by
    have := mono v hMP (Finset.empty_subset (insert i C)); linarith
  have hdem : IsDemanded v s (insert i C) := by
    intro D
    rw [hpC]
    unfold profit
    by_cases hD : D ⊆ insert i C
    · by_cases hiD : i ∈ D
      · have hsum : t ≤ ∑ j ∈ D, s j := by
          have := Finset.single_le_sum (fun j _ => hs_nn j) hiD
          simpa [s] using this
        have := mono v hMP hD
        linarith
      · have hDC : D ⊆ C := by
          intro j hj
          have := hD hj
          rcases Finset.mem_insert.1 this with h | h
          · exact absurd (h ▸ hj) hiD
          · exact h
        have hsum : 0 ≤ ∑ j ∈ D, s j := Finset.sum_nonneg (fun j _ => hs_nn j)
        have := mono v hMP hDC
        linarith
    · obtain ⟨j, hjD, hjn⟩ := Finset.not_subset.1 hD
      have hsj : s j = B := by
        have hji : j ≠ i := fun h => hjn (h ▸ Finset.mem_insert_self _ _)
        have hjC : j ∉ C := fun h => hjn (Finset.mem_insert_of_mem h)
        simp [s, hji, hjC]
      have hsum : B ≤ ∑ j ∈ D, s j := by
        have := Finset.single_le_sum (fun j _ => hs_nn j) hjD
        simpa [hsj] using this
      have := mono v hMP (Finset.subset_univ D)
      linarith
  obtain ⟨C', hC'dem, hsub⟩ := hGS s (Set.mem_univ _) s' (Set.mem_univ _) hle (insert i C) hdem
  have hiC' : i ∈ C' := by
    apply hsub
    simp [s, s']
  have h0 := hC'dem ∅
  unfold profit at h0
  simp only [Finset.sum_empty, hNFL, sub_zero] at h0
  by_cases hsing : C' = {i}
  · subst hsing
    simp [s'] at h0
    linarith
  · obtain ⟨j, hjC', hji⟩ : ∃ j ∈ C', j ≠ i := by
      by_contra hno
      push_neg at hno
      apply hsing
      ext x; constructor
      · intro hx; simp [hno x hx]
      · intro hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hiC'
    have hsum : t + B ≤ ∑ k ∈ C', s' k := by
      have hsub2 : ({i, j} : Finset W) ⊆ C' := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hiC'
        · exact hjC'
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun k _ _ => hs'_nn k)
      rw [Finset.sum_pair (Ne.symm hji)] at this
      simpa [s', hji] using this
    have := mono v hMP (Finset.subset_univ C')
    linarith

theorem subadd {W : Type} [Fintype W] [DecidableEq W] (v : Finset W → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hGS : GrossSubstitutesOn v Set.univ) (C : Finset W) :
    v C ≤ ∑ j ∈ C, v {j} := by
  induction C using Finset.induction_on with
  | empty => simp [hNFL]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have := sub_step v hMP hNFL hGS a S ha
    linarith

end KC09dd81b6

open KelsoCrawford.OneSided in
theorem solution {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hGS : GrossSubstitutesOn v Set.univ) :
    ∃ (P : Finpartition (Finset.univ : Finset W)) (s : W → ℝ),
      IsOneSidedStrictCore v P s := by
  refine ⟨⊥, fun j => v {j}, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro j
    have := hMP j ∅
    simpa [hNFL] using this
  · rw [Finpartition.parts_bot, Finset.sum_map]
    simp
  · rintro ⟨C, r, hr, hsum, j, hjC, hlt⟩
    have h1 : ∑ k ∈ C, v {k} < ∑ k ∈ C, r k :=
      Finset.sum_lt_sum hr ⟨j, hjC, hlt⟩
    have h2 := KC09dd81b6.subadd v hMP hNFL hGS C
    linarith
