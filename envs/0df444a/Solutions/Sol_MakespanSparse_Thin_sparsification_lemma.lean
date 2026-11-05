-- Prove2me | solution 1 for MakespanSparse.Thin.sparsification_lemma
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:41:42.7432+00:00
-- url     : https://prove2.me/submissions/4cb29a4c-f3cc-47a9-97a4-25e5bd50b111

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

open MakespanSparse.Thin

theorem solution (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k) (T : ℕ)
    (c : Fin d → ℕ) (hc : IsConfig π T c) (hcx : ¬ IsSimple T c) :
    ∃ c₁ c₂ : Fin d → ℕ, IsConfig π T c₁ ∧ IsConfig π T c₂ ∧
      ∑ k, π k * c₁ k = ∑ k, π k * c k ∧ ∑ k, π k * c₂ k = ∑ k, π k * c k ∧
      2 • c = c₁ + c₂ ∧ supp c₁ ⊂ supp c ∧ supp c₂ ⊂ supp c := by
  classical
  -- weight of the restriction `c^S`
  set w : Finset (Fin d) → ℕ := fun S => ∑ k ∈ S, π k * c k with hw
  have hwtot : w (supp c) = ∑ k, π k * c k := by
    simp only [hw, supp]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · simp only [not_not] at h; simp [h]
  have hwle : ∀ S ⊆ supp c, w S ≤ T := by
    intro S hS
    calc w S ≤ w (supp c) := Finset.sum_le_sum_of_subset hS
      _ = _ := hwtot
      _ ≤ T := hc
  -- 2^|supp c| > T + 1
  have hcard : T + 1 < 2 ^ (supp c).card := by
    unfold IsSimple at hcx
    push Not at hcx
    have h1 : ((T : ℝ) + 1) < (2 : ℝ) ^ ((supp c).card : ℝ) := by
      rwa [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)] at hcx
    rw [Real.rpow_natCast] at h1
    exact_mod_cast h1
  -- pigeonhole
  have hmaps : ∀ S ∈ (supp c).powerset, w S ∈ Finset.range (T + 1) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (hwle S hS))
  obtain ⟨S, hS, R, hR, hSR, hwSR⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simpa [Finset.card_powerset] using hcard) hmaps
  rw [Finset.mem_powerset] at hS hR
  set S' := S \ R with hS'
  set R' := R \ S with hR'
  have hsplit : ∀ A B : Finset (Fin d), w A = w (A \ B) + w (A ∩ B) := by
    intro A B
    simp only [hw]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter A B), Finset.sdiff_union_inter]
  have hwS'R' : w S' = w R' := by
    have h1 : w S = w S' + w (S ∩ R) := hsplit S R
    have h2 : w R = w R' + w (S ∩ R) := by
      have := hsplit R S; rw [Finset.inter_comm] at this; exact this
    omega
  have hS'sub : S' ⊆ supp c := fun k hk => hS (Finset.mem_sdiff.1 hk).1
  have hR'sub : R' ⊆ supp c := fun k hk => hR (Finset.mem_sdiff.1 hk).1
  have hdisj : Disjoint S' R' := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact (Finset.mem_sdiff.1 hk').2 (Finset.mem_sdiff.1 hk).1
  -- weight zero on a subset of supp c forces emptiness
  have hw0 : ∀ A ⊆ supp c, w A = 0 → A = ∅ := by
    intro A hA h0
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have := (Finset.sum_eq_zero_iff.1 h0) k hk
    have hck : c k ≠ 0 := by
      have := hA hk; simp [supp] at this; exact this
    exact (Nat.mul_ne_zero (hπ k).ne' hck) this
  have hS'ne : S'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have hsub : S ⊆ R := Finset.sdiff_eq_empty_iff_subset.1 hE
    have hwR : w R' = 0 := by rw [← hwS'R', hE]; simp [hw]
    have hR'E := hw0 R' hR'sub hwR
    have : R ⊆ S := Finset.sdiff_eq_empty_iff_subset.1 hR'E
    exact hSR (Finset.Subset.antisymm hsub this)
  have hR'ne : R'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have hsub : R ⊆ S := Finset.sdiff_eq_empty_iff_subset.1 hE
    have hwS : w S' = 0 := by rw [hwS'R', hE]; simp [hw]
    have hS'E := hw0 S' hS'sub hwS
    have : S ⊆ R := Finset.sdiff_eq_empty_iff_subset.1 hS'E
    exact hSR (Finset.Subset.antisymm this hsub)
  -- the two new configurations
  let c₁ : Fin d → ℕ := fun k => if k ∈ S' then 0 else if k ∈ R' then 2 * c k else c k
  let c₂ : Fin d → ℕ := fun k => if k ∈ R' then 0 else if k ∈ S' then 2 * c k else c k
  have key : ∀ (X Y : Finset (Fin d)), Disjoint X Y → X ⊆ supp c → Y ⊆ supp c → w X = w Y →
      ∑ k, π k * (if k ∈ X then 0 else if k ∈ Y then 2 * c k else c k) = ∑ k, π k * c k := by
    intro X Y hXY _ _ hXYw
    have e : ∀ k, π k * (if k ∈ X then 0 else if k ∈ Y then 2 * c k else c k) +
        (if k ∈ X then π k * c k else 0) = π k * c k + (if k ∈ Y then π k * c k else 0) := by
      intro k
      by_cases hX : k ∈ X
      · have hY : k ∉ Y := Finset.disjoint_left.1 hXY hX
        simp [hX, hY]
      · by_cases hY : k ∈ Y
        · simp [hX, hY]; ring
        · simp [hX, hY]
    have hsum := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => e k)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.univ_inter] at hsum
    have : ∑ k ∈ X, π k * c k = ∑ k ∈ Y, π k * c k := hXYw
    omega
  have hc₁w : ∑ k, π k * c₁ k = ∑ k, π k * c k := key S' R' hdisj hS'sub hR'sub hwS'R'
  have hc₂w : ∑ k, π k * c₂ k = ∑ k, π k * c k :=
    key R' S' hdisj.symm hR'sub hS'sub hwS'R'.symm
  have hsupp : ∀ (X Y : Finset (Fin d)), Disjoint X Y → X ⊆ supp c → X.Nonempty →
      supp (fun k => if k ∈ X then 0 else if k ∈ Y then 2 * c k else c k) ⊂ supp c := by
    intro X Y _ hXs hXne
    rw [Finset.ssubset_iff_of_subset]
    · obtain ⟨k, hk⟩ := hXne
      exact ⟨k, hXs hk, by simp [supp, hk]⟩
    · intro k hk
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      intro h0
      apply hk
      split_ifs <;> simp [h0]
  refine ⟨c₁, c₂, ?_, ?_, hc₁w, hc₂w, ?_, hsupp S' R' hdisj hS'sub hS'ne,
    hsupp R' S' hdisj.symm hR'sub hR'ne⟩
  · unfold IsConfig; rw [hc₁w]; exact hc
  · unfold IsConfig; rw [hc₂w]; exact hc
  · funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c₁, c₂]
    by_cases hX : k ∈ S'
    · have hY : k ∉ R' := Finset.disjoint_left.1 hdisj hX
      simp [hX, hY]
    · by_cases hY : k ∈ R'
      · simp [hX, hY]
      · simp [hX, hY]; ring
