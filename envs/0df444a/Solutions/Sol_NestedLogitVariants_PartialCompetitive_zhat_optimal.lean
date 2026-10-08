-- Prove2me | solution 1 for NestedLogitVariants.PartialCompetitive.zhat_optimal
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T13:20:23.06682+00:00
-- url     : https://prove2.me/submissions/f6849287-79fc-4abb-a29a-7f034ea32aa8

import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack
open NestedLogitVariants.PartialCompetitive
open Finset
set_option maxHeartbeats 1000000

private lemma gz_bounds {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (ε : ℝ) (j : Fin n) :
    0 ≤ zhat I i ε j ∧ zhat I i ε j ≤ (if I.v i j ≤ ε then 1 else 0) := by
  unfold zhat
  split_ifs
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · exact ⟨le_refl _, le_refl _⟩

private lemma gz_eligible {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (ε : ℝ) (j : Fin n)
    (hj : 0 < zhat I i ε j) : I.v i j ≤ ε := by
  by_contra h
  simp [zhat, h] at hj

private lemma prefix_step {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (ε : ℝ) (j k : Fin n) (hjk : j < k) (hj : I.v i j ≤ ε) :
    prefixLoad I i ε j + I.v i j ≤ prefixLoad I i ε k := by
  classical
  let A := univ.filter (fun l : Fin n => l < j ∧ I.v i l ≤ ε)
  let B := univ.filter (fun l : Fin n => l < k ∧ I.v i l ≤ ε)
  have hn : j ∉ A := by simp [A]
  have hs : insert j A ⊆ B := by
    intro l hl
    rcases mem_insert.mp hl with rfl | hl
    · simp [B, hjk, hj]
    · obtain ⟨_, hl, he⟩ := mem_filter.mp hl
      simp [B, lt_trans hl hjk, he]
  have h := sum_le_sum_of_subset_of_nonneg hs (fun l _ _ => (hI.v_pos i l).le)
  simpa [A, B, sum_insert hn, prefixLoad, add_comm] using h

private lemma gz_pos_prefix {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (ε : ℝ) (j : Fin n) (hj : 0 < zhat I i ε j) :
    prefixLoad I i ε j < ε := by
  have he := gz_eligible I i ε j hj
  rw [zhat, if_pos he] at hj
  have hr : 0 < (ε - prefixLoad I i ε j) / I.v i j :=
    lt_of_lt_of_le ((lt_max_iff.mp hj).resolve_left (lt_irrefl _)) (min_le_right _ _)
  have := (div_pos_iff.mp hr).resolve_right (fun h => (not_lt_of_ge (hI.v_pos i j).le) h.2)
  linarith [this.1]

private lemma gz_full {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (ε : ℝ) (j : Fin n) (he : I.v i j ≤ ε)
    (hp : prefixLoad I i ε j + I.v i j ≤ ε) : zhat I i ε j = 1 := by
  have hdiv : 1 ≤ (ε - prefixLoad I i ε j) / I.v i j :=
    (le_div_iff₀ (hI.v_pos i j)).2 (by linarith)
  simp [zhat, he, min_eq_left hdiv]

private lemma gz_later_zero {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (ε : ℝ) (j k : Fin n) (hj : I.v i j ≤ ε)
    (hjn : zhat I i ε j < 1) (hjk : j < k) : zhat I i ε k = 0 := by
  have hp : ε < prefixLoad I i ε j + I.v i j := by
    by_contra h
    have := gz_full I hI i ε j hj (le_of_not_gt h)
    linarith
  have hpk : ε ≤ prefixLoad I i ε k := by linarith [prefix_step I hI i ε j k hjk hj]
  unfold zhat
  split_ifs with hk
  · have hd : (ε - prefixLoad I i ε k) / I.v i k ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (hI.v_pos i k).le
    exact max_eq_left (le_trans (min_le_right _ _) hd)
  · rfl

private lemma gz_before_full {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (ε : ℝ) (j k : Fin n) (hj : I.v i j ≤ ε)
    (hk : 0 < zhat I i ε k) (hjk : j < k) : zhat I i ε j = 1 := by
  exact gz_full I hI i ε j hj (le_trans (prefix_step I hI i ε j k hjk hj)
    (gz_pos_prefix I hI i ε k hk).le)

private lemma load_split {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (ε : ℝ) (k : Fin n)
    (hbef : ∀ j, j < k → I.v i j ≤ ε → zhat I i ε j = 1)
    (haft : ∀ j, k < j → zhat I i ε j = 0) :
    ∑ j, I.v i j * zhat I i ε j = prefixLoad I i ε k + I.v i k * zhat I i ε k := by
  classical
  have heq : (fun j => I.v i j * zhat I i ε j) =
      (fun j => (if j < k ∧ I.v i j ≤ ε then I.v i j else 0) +
        (if j = k then I.v i k * zhat I i ε k else 0)) := by
    funext j
    rcases lt_trichotomy j k with hj | rfl | hj
    · by_cases he : I.v i j ≤ ε
      · simp [hj, he, ne_of_lt hj, hbef j hj he]
      · simp [hj, he, ne_of_lt hj, zhat]
    · simp
    · simp [not_lt_of_ge hj.le, ne_of_gt hj, haft j hj]
  rw [heq, sum_add_distrib]
  simp only [sum_ite_eq', mem_univ, if_true]
  rw [← sum_filter]
  rfl

private lemma gz_capacity {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε) : ∑ j, I.v i j * zhat I i ε j ≤ ε := by
  classical
  let P := univ.filter (fun j : Fin n => 0 < zhat I i ε j)
  by_cases hP : P.Nonempty
  · let k := P.max' hP
    have hk : 0 < zhat I i ε k := (mem_filter.mp (max'_mem P hP)).2
    have he := gz_eligible I i ε k hk
    have hb := gz_before_full I hI i ε
    have ha : ∀ j, k < j → zhat I i ε j = 0 := by
      intro j hj
      have hn : ¬ 0 < zhat I i ε j := by
        intro hp
        have hmem : j ∈ P := mem_filter.mpr ⟨mem_univ _, hp⟩
        exact (not_le_of_gt hj) (le_max' P j hmem)
      exact le_antisymm (le_of_not_gt hn) (gz_bounds I i ε j).1
    rw [load_split I i ε k (fun j hj he => hb j k he hk hj) ha]
    have hp := gz_pos_prefix I hI i ε k hk
    have hd : 0 ≤ (ε - prefixLoad I i ε k) / I.v i k :=
      div_nonneg (by linarith) (hI.v_pos i k).le
    have hz : zhat I i ε k ≤ (ε - prefixLoad I i ε k) / I.v i k := by
      rw [zhat, if_pos he]
      exact max_le hd (min_le_right _ _)
    have hz' := (le_div_iff₀ (hI.v_pos i k)).mp hz
    nlinarith
  · have hz : ∀ j, zhat I i ε j = 0 := by
      intro j
      have hn : ¬ 0 < zhat I i ε j := by
        intro hp
        exact hP ⟨j, mem_filter.mpr ⟨mem_univ _, hp⟩⟩
      exact le_antisymm (le_of_not_gt hn) (gz_bounds I i ε j).1
    simp [hz, hε]

private lemma cutoff_data {ι : Type*} {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hex : ∃ j, I.v i j ≤ ε ∧ zhat I i ε j < 1) :
    ∃ k : Fin n,
      (∀ j, j < k → I.v i j ≤ ε → zhat I i ε j = 1) ∧
      (∀ j, k < j → zhat I i ε j = 0) ∧
      (∑ j, I.v i j * zhat I i ε j = ε) := by
  classical
  let D := univ.filter (fun j : Fin n => I.v i j ≤ ε ∧ zhat I i ε j < 1)
  have hD : D.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  let k := D.min' hD
  have hk : I.v i k ≤ ε ∧ zhat I i ε k < 1 := (mem_filter.mp (min'_mem D hD)).2
  have hb : ∀ j, j < k → I.v i j ≤ ε → zhat I i ε j = 1 := by
    intro j hj he
    have hle : zhat I i ε j ≤ 1 := by simpa [he] using (gz_bounds I i ε j).2
    by_contra hn
    have hmem : j ∈ D := mem_filter.mpr ⟨mem_univ _, he, lt_of_le_of_ne hle hn⟩
    exact (not_le_of_gt hj) (min'_le D j hmem)
  have ha : ∀ j, k < j → zhat I i ε j = 0 :=
    fun j hj => gz_later_zero I hI i ε k j hk.1 hk.2 hj
  refine ⟨k, hb, ha, le_antisymm (gz_capacity I hI i ε hε) ?_⟩
  rw [load_split I i ε k hb ha]
  have hr : (ε - prefixLoad I i ε k) / I.v i k < 1 := by
    by_contra hn
    have hz : zhat I i ε k = 1 := by
      simp [zhat, hk.1, min_eq_left (le_of_not_gt hn)]
    linarith [hk.2]
  have hz : (ε - prefixLoad I i ε k) / I.v i k ≤ zhat I i ε k := by
    rw [zhat, if_pos hk.1, min_eq_right hr.le]
    exact le_max_right _ _
  have hz' := (div_le_iff₀ (hI.v_pos i k)).mp hz
  nlinarith

open NestedLogitVariants.PartialCompetitive in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    feas11 I i ε (zhat I i ε) ∧
      (∀ z : Fin n → ℝ, feas11 I i ε z →
        ∑ j, I.r i j * I.v i j * z j ≤ ∑ j, I.r i j * I.v i j * zhat I i ε j) ∧
      (∀ j k : Fin n, zhat I i ε j ∈ Set.Ioo (0 : ℝ) 1 → zhat I i ε k ∈ Set.Ioo (0 : ℝ) 1 →
        j = k) := by
  classical
  refine ⟨⟨gz_capacity I hI i ε hε, gz_bounds I i ε⟩, ?_, ?_⟩
  · intro z hz
    by_cases hex : ∃ j, I.v i j ≤ ε ∧ zhat I i ε j < 1
    · obtain ⟨k, hb, ha, hsat⟩ := cutoff_data I hI i ε hε hex
      have hpoint : ∀ j, I.r i j * (I.v i j * (z j - zhat I i ε j)) ≤
          I.r i k * (I.v i j * (z j - zhat I i ε j)) := by
        intro j
        by_cases he : I.v i j ≤ ε
        · have hz1 : z j ≤ 1 := by simpa [he] using (hz.2 j).2
          rcases lt_trichotomy j k with hj | rfl | hj
          · rw [hb j hj he]
            exact mul_le_mul_of_nonpos_right (hI.r_antitone i hj.le)
              (mul_nonpos_of_nonneg_of_nonpos (hI.v_pos i j).le (by linarith))
          · exact le_refl _
          · rw [ha j hj]
            exact mul_le_mul_of_nonneg_right (hI.r_antitone i hj.le)
              (mul_nonneg (hI.v_pos i j).le (by linarith [(hz.2 j).1]))
        · have hz0 : z j = 0 := le_antisymm (by simpa [he] using (hz.2 j).2) (hz.2 j).1
          simp [zhat, he, hz0]
      have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => hpoint j)
      have hs : (∑ j, I.r i j * I.v i j * z j) - (∑ j, I.r i j * I.v i j * zhat I i ε j) ≤
          I.r i k * ((∑ j, I.v i j * z j) - ε) := by
        have hl : (∑ j, I.r i j * (I.v i j * (z j - zhat I i ε j))) =
            (∑ j, I.r i j * I.v i j * z j) - (∑ j, I.r i j * I.v i j * zhat I i ε j) := by
          simp only [mul_sub, sum_sub_distrib, mul_assoc]
        have hr : (∑ j, I.r i k * (I.v i j * (z j - zhat I i ε j))) =
            I.r i k * ((∑ j, I.v i j * z j) - ε) := by
          rw [← mul_sum]
          simp only [mul_sub, sum_sub_distrib, hsat]
        rwa [hl, hr] at hsum
      have hn : I.r i k * ((∑ j, I.v i j * z j) - ε) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hI.r_nonneg i k) (sub_nonpos.mpr hz.1)
      linarith
    · apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le)
      by_cases he : I.v i j ≤ ε
      · have hge : 1 ≤ zhat I i ε j := le_of_not_gt (fun h => hex ⟨j, he, h⟩)
        exact le_trans (by simpa [he] using (hz.2 j).2) hge
      · simpa [zhat, he] using (hz.2 j).2
  · intro j k hj hk
    rcases lt_trichotomy j k with h | h | h
    · have := gz_later_zero I hI i ε j k (gz_eligible I i ε j hj.1) hj.2 h
      linarith [hk.1]
    · exact h
    · have := gz_later_zero I hI i ε k j (gz_eligible I i ε k hk.1) hk.2 h
      linarith [hj.1]

#print axioms solution


