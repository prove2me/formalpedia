-- Prove2me | solution 1 for KelsoCrawford.Returns.two_workers_gs_iff_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:48:04.418686+00:00
-- url     : https://prove2.me/submissions/5fb00d6c-61a9-4698-9fe8-42c52baacf23

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

private theorem symmetric_gs {W : Type} [Fintype W] [DecidableEq W] (ybar : ℕ → ℝ)
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

private lemma additive_gs {W : Type} [Fintype W] [DecidableEq W]
    (z y : Finset W → ℝ) (v : W → ℝ)
    (hy : ∀ C, y C = z C + ∑ i ∈ C, v i)
    (hz : GrossSubstitutesOn z Set.univ) : GrossSubstitutesOn y Set.univ := by
  classical
  have hp (s : W → ℝ) (C : Finset W) :
      profit y C s = profit z C (fun i => s i - v i) := by
    unfold profit
    rw [hy C, Finset.sum_sub_distrib]; ring
  intro s hs s' hs' hss C hC
  have hd : IsDemanded z (fun i => s i - v i) C := by
    intro B; simpa only [← hp] using hC B
  obtain ⟨B, hB, hsub⟩ := hz _ (by trivial) _ (by trivial)
    (fun i => sub_le_sub_right (hss i) _) C hd
  refine ⟨B, ?_, ?_⟩
  · intro A; simpa only [hp] using hB A
  · intro i hi
    apply hsub
    rcases Finset.mem_filter.mp hi with ⟨hi, he⟩
    exact Finset.mem_filter.mpr ⟨hi, by rw [he]⟩

private lemma two_cases {W : Type} [Fintype W] [DecidableEq W]
    (a b : W) (hu : (Finset.univ : Finset W) = {a,b}) (C : Finset W) :
    C = ∅ ∨ C = {a} ∨ C = {b} ∨ C = {a,b} := by
  have hsub : C ⊆ {a,b} := hu ▸ Finset.subset_univ C
  by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
  · right; right; right; ext i; specialize @hsub i; simp only [Finset.mem_insert, Finset.mem_singleton] at *; aesop
  · right; left; ext i; specialize @hsub i; simp only [Finset.mem_insert, Finset.mem_singleton] at *; aesop
  · right; right; left; ext i; specialize @hsub i; simp only [Finset.mem_insert, Finset.mem_singleton] at *; aesop
  · left; ext i; specialize @hsub i; simp only [Finset.mem_insert, Finset.mem_singleton] at *; simp; aesop

theorem solution {W : Type} [Fintype W] [DecidableEq W]
    (hW : Fintype.card W = 2) (y : Finset W → ℝ) (hy0 : y ∅ = 0) :
    GrossSubstitutesOn y Set.univ ↔ Subadditive y := by
  classical
  obtain ⟨a,b,hab,hu⟩ := Finset.card_eq_two.mp (show (Finset.univ : Finset W).card = 2 by simpa using hW)
  have hba : b ≠ a := hab.symm
  have classify := two_cases a b hu
  let δ := y {a,b} - y {a} - y {b}
  have hpair : ({b,a} : Finset W) = {a,b} := Finset.pair_comm b a
  have sub_iff : Subadditive y ↔ δ ≤ 0 := by
    constructor
    · intro h; have hh := h {a} {b} (by simp [hab]); simp only [Finset.singleton_union] at hh; dsimp [δ]; linarith
    · intro h C D hd
      rcases classify C with rfl | rfl | rfl | rfl <;>
        rcases classify D with rfl | rfl | rfl | rfl <;>
        simp_all [Finset.disjoint_left, δ, hpair] <;> linarith
  rw [sub_iff]
  constructor
  · intro hgs
    by_contra hδ
    have hd : 0 < δ := lt_of_not_ge hδ
    let s : W → ℝ := fun i => y {i} + δ/3
    let s' : W → ℝ := fun i => if i = a then y {i} + 2*δ else s i
    have hss : s ≤ s' := by intro i; dsimp [s',s]; split_ifs <;> linarith
    have hdemand : IsDemanded y s {a,b} := by
      intro C
      rcases classify C with rfl | rfl | rfl | rfl <;>
        simp [profit, s, hab, hba, hy0] <;> dsimp [δ] at * <;> linarith
    obtain ⟨C,hC,hkeep⟩ := hgs s (by trivial) s' (by trivial) hss {a,b} hdemand
    have hbC : b ∈ C := hkeep (by simp [s', hba])
    have hz := hC ∅
    rcases classify C with rfl | rfl | rfl | rfl
    · simpa using hbC
    · simpa [hba] using hbC
    · simp [profit, s', s, hy0, hba] at hz; linarith
    · simp [profit, s', s, hy0, hab, hba] at hz; dsimp [δ] at *; linarith
  · intro hδ
    let v : ℕ → ℝ := fun k => if k = 2 then δ else 0
    have hDR : DR (Fintype.card W) v := by
      intro w hw hw2
      have he : w = 1 := by omega
      subst w
      simp [v]; exact hδ
    have hy : ∀ C : Finset W, y C = v C.card + ∑ i ∈ C, y {i} := by
      intro C
      rcases classify C with rfl | rfl | rfl | rfl <;>
        simp [v, hab, hba, hy0, δ] <;> ring
    exact additive_gs _ _ _ hy (symmetric_gs v hDR)

#print axioms solution
