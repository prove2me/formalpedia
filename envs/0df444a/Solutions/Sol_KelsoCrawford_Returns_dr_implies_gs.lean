-- Prove2me | solution 1 for KelsoCrawford.Returns.dr_implies_gs
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:44:22.659048+00:00
-- url     : https://prove2.me/submissions/ea32479f-644e-491e-be7d-988380914ae8

import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Returns_Technology
open KelsoCrawford.Returns KelsoCrawford.Process
open scoped BigOperators

private lemma marginal (m : ℕ) (v : ℕ → ℝ) (hv : DR m v)
    (a b : ℕ) (hab : a ≤ b) (hb : b + 1 ≤ m) :
    v (b+1) - v b ≤ v (a+1) - v a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hh := hv (b+1) (by omega) hb
    simp only [Nat.add_sub_cancel] at hh
    exact hh.trans (ih (by omega))

theorem solution {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ)
    (hDR : DR (Fintype.card W) ybar) :
    GrossSubstitutesOn (fun C : Finset W => ybar C.card) Set.univ := by
  classical
  intro s hs s' hs' hss A hA
  let y := fun C : Finset W => ybar C.card
  let K := A.filter (fun i => s' i = s i)
  obtain ⟨B₀, _, hB₀⟩ := (Finset.univ : Finset (Finset W)).exists_max_image
    (fun B => profit y B s') (by simp)
  have hB₀' : IsDemanded y s' B₀ := fun C => hB₀ C (by simp)
  let D := (Finset.univ : Finset (Finset W)).filter (IsDemanded y s')
  have hD : D.Nonempty := ⟨B₀, by simp [D, hB₀']⟩
  obtain ⟨B, hBD, hmax⟩ := D.exists_max_image (fun B => (K ∩ B).card) hD
  have hB : IsDemanded y s' B := (Finset.mem_filter.mp hBD).2
  refine ⟨B, hB, ?_⟩
  intro i hi
  by_contra hiB
  have hiA : i ∈ A := (Finset.mem_filter.mp hi).1
  have his : s' i = s i := (Finset.mem_filter.mp hi).2
  have improve (B' : Finset W) (hprofit : profit y B s' ≤ profit y B' s')
      (hsub : K ∩ B ⊆ K ∩ B') (hi' : i ∈ B') : False := by
    have hd' : IsDemanded y s' B' := fun C => (hB C).trans hprofit
    have hm := hmax B' (by simp [D, hd'])
    have hstrict : K ∩ B ⊂ K ∩ B' := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub, ?_⟩
      intro he
      have : i ∈ K ∩ B' := Finset.mem_inter.mpr ⟨hi, hi'⟩
      rw [← he] at this
      exact hiB (Finset.mem_inter.mp this).2
    exact (not_lt_of_ge hm) (Finset.card_lt_card hstrict)
  by_cases hc : B.card < A.card
  · have ha0 : 0 < A.card := Finset.card_pos.mpr ⟨i, hiA⟩
    have hh := marginal (Fintype.card W) ybar hDR B.card (A.card-1)
      (by omega) (by have := Finset.card_le_univ A; omega)
    have hcA : (A.erase i).card = A.card-1 := Finset.card_erase_of_mem hiA
    have hcB : (insert i B).card = B.card+1 := Finset.card_insert_of_notMem hiB
    have hsA := hA (A.erase i)
    have sumA : ∑ j ∈ A.erase i, s j = (∑ j ∈ A, s j) - s i := by
      have := Finset.sum_erase_add A s hiA; linarith
    have hpr : profit y B s' ≤ profit y (insert i B) s' := by
      unfold profit y at *
      dsimp only at hsA
      rw [hcA, sumA] at hsA
      rw [hcB, Finset.sum_insert hiB, his]
      have he : A.card-1+1 = A.card := by omega
      rw [he] at hh
      linarith
    apply improve (insert i B) hpr
    · intro j hj; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hj).1,
        Finset.mem_insert_of_mem (Finset.mem_inter.mp hj).2⟩
    · simp
  · have hjex : ∃ j ∈ B, j ∉ A := by
      by_contra hnone
      have hsub : B ⊆ A := by
        intro j hj
        by_contra hjA
        exact hnone ⟨j, hj, hjA⟩
      have he : B = A := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact hiB (he.symm ▸ hiA)
    obtain ⟨j, hjB, hjA⟩ := hjex
    have hij : i ≠ j := by intro he; exact hjA (he ▸ hiA)
    have hiswap : j ∉ A.erase i := fun hj => hjA (Finset.mem_of_mem_erase hj)
    have hjswap : i ∉ B.erase j := fun hi => hiB (Finset.mem_of_mem_erase hi)
    have hsA := hA (insert j (A.erase i))
    have hcA : (insert j (A.erase i)).card = A.card := by
      rw [Finset.card_insert_of_notMem hiswap, Finset.card_erase_of_mem hiA]
      have := Finset.card_pos.mpr ⟨i, hiA⟩; omega
    have hcB : (insert i (B.erase j)).card = B.card := by
      rw [Finset.card_insert_of_notMem hjswap, Finset.card_erase_of_mem hjB]
      have := Finset.card_pos.mpr ⟨j, hjB⟩; omega
    have sumA : ∑ k ∈ A.erase i, s k = (∑ k ∈ A, s k) - s i := by
      have := Finset.sum_erase_add A s hiA; linarith
    have sumB : ∑ k ∈ B.erase j, s' k = (∑ k ∈ B, s' k) - s' j := by
      have := Finset.sum_erase_add B s' hjB; linarith
    have hpr : profit y B s' ≤ profit y (insert i (B.erase j)) s' := by
      unfold profit y at *
      dsimp only at hsA
      rw [hcA, Finset.sum_insert hiswap, sumA] at hsA
      rw [hcB, Finset.sum_insert hjswap, sumB, his]
      have hh := hss j
      linarith
    apply improve (insert i (B.erase j)) hpr
    · intro k hk
      have hkK := (Finset.mem_inter.mp hk).1
      have hkB := (Finset.mem_inter.mp hk).2
      have hkj : k ≠ j := by
        intro he; have := (Finset.mem_filter.mp hkK).1; exact hjA (he ▸ this)
      exact Finset.mem_inter.mpr ⟨hkK, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hkj, hkB⟩)⟩
    · simp

#print axioms solution
