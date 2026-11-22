-- Prove2me | solution 1 for HardyLittlewoodMaximal.vitali_covering_lemma_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:16:29.22995+00:00
-- url     : https://prove2.me/submissions/cef9a9a6-53c5-460d-9a30-4711d34327bc

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_HardyLittlewoodMaximal_vitali_covering_lemma_euclidean

/-- Greedy selection in a finite family of nonempty sets carrying a "size" `r`: there is a
pairwise disjoint subfamily `u` such that every member of the family meets a member of `u` of
size at least its own. -/
theorem finite_greedy {ι α : Type*} (B : ι → Set α) (r : ι → ℝ) (hB : ∀ i, (B i).Nonempty) :
    ∀ (n : ℕ) (t : Finset ι), t.card ≤ n →
      ∃ u : Finset ι, u ⊆ t ∧ (↑u : Set ι).PairwiseDisjoint B ∧
        ∀ a ∈ t, ∃ b ∈ u, (B a ∩ B b).Nonempty ∧ r a ≤ r b := by
  classical
  intro n
  induction n with
  | zero =>
    intro t ht
    have ht0 : t = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp ht)
    subst ht0
    exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | succ n ih =>
    intro t ht
    rcases t.eq_empty_or_nonempty with ht0 | hne
    · subst ht0
      exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · obtain ⟨b₀, hb₀t, hb₀max⟩ := Finset.exists_max_image t r hne
      -- the members of the family which do not meet `B b₀`
      set t' : Finset ι := (t.erase b₀).filter (fun a => Disjoint (B a) (B b₀)) with ht'
      have ht't : t' ⊆ t := fun a ha =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_filter a ha)
      have hcard : t'.card ≤ n := by
        have h1 : t'.card ≤ (t.erase b₀).card := Finset.card_filter_le _ _
        have h2 : (t.erase b₀).card = t.card - 1 := Finset.card_erase_of_mem hb₀t
        omega
      obtain ⟨u', hu't', hu'disj, hu'cov⟩ := ih t' hcard
      have hu'B : ∀ b ∈ u', Disjoint (B b) (B b₀) := fun b hb =>
        (Finset.mem_filter.mp (hu't' hb)).2
      have hb₀u' : b₀ ∉ u' := fun h =>
        Finset.notMem_erase b₀ t (Finset.mem_of_mem_filter b₀ (hu't' h))
      refine ⟨insert b₀ u', ?_, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hb₀t
        · exact ht't (hu't' ha)
      · rw [Finset.coe_insert]
        refine (Set.pairwiseDisjoint_insert_of_notMem (by exact_mod_cast hb₀u')).mpr ⟨hu'disj, ?_⟩
        intro b hb
        exact (hu'B b (by exact_mod_cast hb)).symm
      · intro a ha
        by_cases hab : a = b₀
        · subst hab
          exact ⟨a, Finset.mem_insert_self _ _, by simpa using hB a, le_refl _⟩
        · by_cases hdisj : Disjoint (B a) (B b₀)
          · have hat' : a ∈ t' :=
              Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hab, ha⟩, hdisj⟩
            obtain ⟨b, hbu', hab', hr⟩ := hu'cov a hat'
            exact ⟨b, Finset.mem_insert_of_mem hbu', hab', hr⟩
          · exact ⟨b₀, Finset.mem_insert_self _ _, Set.not_disjoint_iff_nonempty_inter.mp hdisj,
              hb₀max a ha⟩

/-- If two balls meet and the first has radius at most that of the second, then the first is
contained in the three-fold enlargement of the second. -/
theorem ball_subset_ball_three {α : Type*} [PseudoMetricSpace α] {x y : α} {r s : ℝ}
    (h : (ball x r ∩ ball y s).Nonempty) (hrs : r ≤ s) : ball x r ⊆ ball y (3 * s) := by
  obtain ⟨z, hzx, hzy⟩ := h
  intro w hw
  rw [mem_ball] at hw hzx hzy ⊢
  have h1 : dist w y ≤ dist w x + dist x z + dist z y := dist_triangle4 w x z y
  have h2 : dist x z < r := by rwa [dist_comm]
  linarith

/-- In `ℝ^d`, the ball of three times the radius has `3 ^ d` times the volume. -/
theorem volume_ball_three (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    volume (ball x (3 * r)) = 3 ^ d * volume (ball x r) := by
  rw [Measure.addHaar_ball_mul_of_pos volume x (by norm_num : (0 : ℝ) < 3) r,
    Measure.addHaar_ball_center volume x r, finrank_euclideanSpace_fin,
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

end Sol_HardyLittlewoodMaximal_vitali_covering_lemma_euclidean

open Sol_HardyLittlewoodMaximal_vitali_covering_lemma_euclidean in
theorem solution (d : ℕ) (𝒞 : Set (Set (EuclideanSpace ℝ (Fin d))))
    (h𝒞 : ∀ B ∈ 𝒞, ∃ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r ∧ B = Metric.ball x r)
    (c : ℝ≥0∞) (hc : c < volume (⋃₀ 𝒞)) :
    ∃ s : Finset (Set (EuclideanSpace ℝ (Fin d))),
      (↑s : Set (Set (EuclideanSpace ℝ (Fin d)))) ⊆ 𝒞 ∧
      (↑s : Set (Set (EuclideanSpace ℝ (Fin d)))).PairwiseDisjoint id ∧
      c / 3 ^ d < ∑ B ∈ s, volume B := by
  classical
  -- centres and radii of the balls of the family
  have h𝒞' : ∀ B : 𝒞, ∃ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r ∧ (B : Set _) = ball x r :=
    fun B => h𝒞 B.1 B.2
  choose x r hr hB using h𝒞'
  -- the union is open, hence inner regular: a compact `K` inside it with `c < volume K`
  have hopen : IsOpen (⋃₀ 𝒞) := by
    refine isOpen_sUnion fun B hBmem => ?_
    obtain ⟨y, ρ, -, rfl⟩ := h𝒞 B hBmem
    exact isOpen_ball
  obtain ⟨K, hKU, hKc, hcK⟩ := hopen.exists_lt_isCompact hc
  -- finitely many balls of the family cover `K`
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun B : 𝒞 => (B : Set (EuclideanSpace ℝ (Fin d))))
    (fun B => by rw [hB B]; exact isOpen_ball)
    (by rwa [Set.sUnion_eq_iUnion] at hKU)
  -- greedy selection among them
  obtain ⟨u, -, hudisj, hucov⟩ := finite_greedy
    (fun B : 𝒞 => (B : Set (EuclideanSpace ℝ (Fin d)))) r
    (fun B => by rw [hB B]; exact nonempty_ball.mpr (hr B)) t.card t le_rfl
  -- the three-fold enlargements of the selected balls cover `K`
  have hKcov : K ⊆ ⋃ b ∈ u, ball (x b) (3 * r b) := by
    intro y hy
    obtain ⟨a, hat, hya⟩ := Set.mem_iUnion₂.mp (ht hy)
    obtain ⟨b, hbu, hab, hrab⟩ := hucov a hat
    refine Set.mem_iUnion₂.mpr ⟨b, hbu, ?_⟩
    rw [hB a, hB b] at hab
    rw [hB a] at hya
    exact ball_subset_ball_three hab hrab hya
  -- the measure estimate
  have hmeas : c < 3 ^ d * ∑ b ∈ u, volume ((b : Set (EuclideanSpace ℝ (Fin d)))) := by
    calc c < volume K := hcK
      _ ≤ volume (⋃ b ∈ u, ball (x b) (3 * r b)) := measure_mono hKcov
      _ ≤ ∑ b ∈ u, volume (ball (x b) (3 * r b)) := measure_biUnion_finset_le u _
      _ = ∑ b ∈ u, 3 ^ d * volume ((b : Set (EuclideanSpace ℝ (Fin d)))) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [volume_ball_three, ← hB b]
      _ = 3 ^ d * ∑ b ∈ u, volume ((b : Set (EuclideanSpace ℝ (Fin d)))) := by
          rw [Finset.mul_sum]
  -- pass from the selected indices to the selected sets
  refine ⟨u.image (fun B : 𝒞 => (B : Set (EuclideanSpace ℝ (Fin d)))), ?_, ?_, ?_⟩
  · intro B hBmem
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hBmem)
    exact b.2
  · intro B₁ hB₁ B₂ hB₂ hne
    obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hB₁)
    obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hB₂)
    have hne' : b₁ ≠ b₂ := fun h => hne (by rw [h])
    exact hudisj (by exact_mod_cast hb₁) (by exact_mod_cast hb₂) hne'
  · rw [Finset.sum_image (fun b₁ _ b₂ _ h => Subtype.ext h)]
    exact ENNReal.div_lt_of_lt_mul' hmeas
