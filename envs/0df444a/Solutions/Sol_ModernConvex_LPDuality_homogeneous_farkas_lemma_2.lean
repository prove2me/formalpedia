-- Prove2me | solution 2 for ModernConvex.LPDuality.homogeneous_farkas_lemma
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:06:18.32835+00:00
-- url     : https://prove2.me/submissions/8fdba5a5-39cc-4de1-b859-43ccf7e5624a

import Mathlib
set_option autoImplicit false
open Matrix

theorem solution {m n : ℕ} (a : Fin n → ℝ) (as : Fin m → Fin n → ℝ) :
    (¬ ∃ x : Fin n → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ as i ⬝ᵥ x) ↔
      ∃ l : Fin m → ℝ, 0 ≤ l ∧ a = ∑ i, l i • as i := by
  classical
  have cara :
      ∀ (k : ℕ) (s : Finset (Fin m)) (l : Fin m → ℝ), s.card = k → (∀ i ∈ s, 0 ≤ l i) →
        ∃ t : Finset (Fin m), LinearIndependent ℝ (fun i : t => as i) ∧
          ∃ l' : Fin m → ℝ, (∀ i, 0 ≤ l' i) ∧ (∀ i ∉ t, l' i = 0) ∧
            ∑ i ∈ s, l i • as i = ∑ i ∈ t, l' i • as i := by
    classical
    intro k
    induction k with
    | zero =>
      intro s l hs _
      have : s = ∅ := Finset.card_eq_zero.mp hs
      subst this
      refine ⟨∅, linearIndependent_empty_type, fun _ => 0, fun _ => le_refl _, fun _ _ => rfl, by simp⟩
    | succ k ih =>
      intro s l hs hl
      by_cases hli : LinearIndependent ℝ (fun i : s => as i)
      · refine ⟨s, hli, fun i => if i ∈ s then l i else 0, ?_, ?_, ?_⟩
        · intro i; by_cases h : i ∈ s
          · simp [h, hl i h]
          · simp [h]
        · intro i hi; simp [hi]
        · apply Finset.sum_congr rfl; intro i hi; simp [hi]
      · -- dependent family
        obtain ⟨g0, hg0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
        -- choose g with a positive entry
        obtain ⟨g, hg, ip, hip⟩ : ∃ g : s → ℝ, ∑ i, g i • (fun i : s => as i) i = 0 ∧ ∃ i, 0 < g i := by
          rcases lt_or_gt_of_ne hi0 with h | h
          · refine ⟨fun i => - g0 i, ?_, i0, by simpa using h⟩
            simp only [neg_smul, Finset.sum_neg_distrib, hg0, neg_zero]
          · exact ⟨g0, hg0, i0, h⟩
        set G : Fin m → ℝ := fun i => if h : i ∈ s then g ⟨i, h⟩ else 0 with hG
        have hGsum : ∑ i ∈ s, G i • as i = 0 := by
          rw [← hg]
          rw [← Finset.sum_coe_sort s (fun i => G i • as i)]
          apply Finset.sum_congr rfl
          intro i _
          simp [hG, i.2]
        have hGpos : ∃ i ∈ s, 0 < G i := ⟨ip.1, ip.2, by simp [hG, hip]⟩
        set P := s.filter (fun i => 0 < G i) with hP
        have hPne : P.Nonempty := by
          obtain ⟨i, hi, hpos⟩ := hGpos
          exact ⟨i, by simp [hP, hi, hpos]⟩
        obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => l i / G i) hPne
        have hjs : j ∈ s := (Finset.mem_filter.mp hjP).1
        have hjpos : 0 < G j := (Finset.mem_filter.mp hjP).2
        set c := l j / G j with hc
        have hc0 : 0 ≤ c := div_nonneg (hl j hjs) hjpos.le
        set l'' : Fin m → ℝ := fun i => l i - c * G i with hl''
        have hl''nn : ∀ i ∈ s, 0 ≤ l'' i := by
          intro i hi
          by_cases hGi : 0 < G i
          · have hmin := hjmin i (by simp [hP, hi, hGi])
            have : c * G i ≤ l i := by
              have := (le_div_iff₀ hGi).mp hmin
              linarith
            simp only [hl'']; linarith
          · have : G i ≤ 0 := not_lt.mp hGi
            simp only [hl'']; nlinarith [hl i hi]
        have hl''j : l'' j = 0 := by
          simp only [hl'', hc]; field_simp; ring
        have hsum'' : ∑ i ∈ s, l'' i • as i = ∑ i ∈ s, l i • as i := by
          have : ∑ i ∈ s, l'' i • as i = ∑ i ∈ s, l i • as i - c • ∑ i ∈ s, G i • as i := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            simp only [hl'']; rw [sub_smul, mul_smul]
          rw [this, hGsum]; simp
        have hcard : (s.erase j).card = k := by
          rw [Finset.card_erase_of_mem hjs, hs]; rfl
        obtain ⟨t, ht, l', hl'nn, hl'0, hl'sum⟩ := ih (s.erase j) l'' hcard
          (fun i hi => hl''nn i (Finset.mem_of_mem_erase hi))
        refine ⟨t, ht, l', hl'nn, hl'0, ?_⟩
        rw [← hl'sum, Finset.sum_erase _ (by simp [hl''j]), hsum'']
  have hclosed :
      IsClosed {v : Fin n → ℝ | ∃ l : Fin m → ℝ, 0 ≤ l ∧ v = ∑ i, l i • as i} := by
    classical
    have hK : {v : Fin n → ℝ | ∃ l : Fin m → ℝ, 0 ≤ l ∧ v = ∑ i, l i • as i}
        = ⋃ t ∈ {t : Finset (Fin m) | LinearIndependent ℝ (fun i : t => as i)},
            ((Fintype.linearCombination ℝ (fun i : t => as i)) '' {l | 0 ≤ l}) := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
      constructor
      · rintro ⟨l, hl, rfl⟩
        obtain ⟨t, ht, l', hl'nn, hl'0, hsum⟩ := cara _ Finset.univ l rfl (fun i _ => hl i)
        refine ⟨t, ht, fun i => l' i, fun i => hl'nn i, ?_⟩
        rw [Fintype.linearCombination_apply, Finset.sum_coe_sort t (fun i => l' i • as i), ← hsum]
      · rintro ⟨t, ht, f, hf, rfl⟩
        refine ⟨fun i => if h : i ∈ t then f ⟨i, h⟩ else 0, ?_, ?_⟩
        · intro i; by_cases h : i ∈ t
          · simpa [h] using hf ⟨i, h⟩
          · simp [h]
        · rw [Fintype.linearCombination_apply]
          symm
          rw [← Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by simp [hi]),
            ← Finset.sum_coe_sort t]
          apply Finset.sum_congr rfl
          intro i _
          simp [i.2]
    rw [hK]
    refine Set.Finite.isClosed_biUnion (Set.toFinite _) ?_
    intro t ht
    have hinj : Function.Injective (Fintype.linearCombination ℝ (fun i : t => as i)) :=
      linearIndependent_iff_injective_fintypeLinearCombination.mp ht
    exact (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)).isClosedMap _
      (isClosed_Ici (a := (0 : t → ℝ)))
  constructor
  · intro h
    by_contra hnot
    set K : Set (Fin n → ℝ) := {v | ∃ l : Fin m → ℝ, 0 ≤ l ∧ v = ∑ i, l i • as i} with hKdef
    have hKc : IsClosed K := hclosed
    have hKconv : Convex ℝ K := by
      intro v hv w hw s t hs ht hst
      obtain ⟨l, hl, rfl⟩ := hv
      obtain ⟨l', hl', rfl⟩ := hw
      refine ⟨s • l + t • l', ?_, ?_⟩
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hl i; have := hl' i
        simp only [Pi.zero_apply] at *
        positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul]
    have haK : a ∉ K := fun hmem => hnot hmem
    obtain ⟨f, u, hfa, hfb⟩ := geometric_hahn_banach_point_closed hKconv hKc haK
    have h0 : (0 : Fin n → ℝ) ∈ K := ⟨0, le_refl _, by simp⟩
    have hu : u < 0 := by simpa using hfb 0 h0
    have hnn : ∀ b ∈ K, 0 ≤ f b := by
      intro b hb
      by_contra hneg
      push Not at hneg
      obtain ⟨l, hl, rfl⟩ := hb
      set b := ∑ i, l i • as i with hbdef
      have hscale : ∀ t : ℝ, 0 ≤ t → t • b ∈ K := by
        intro t ht
        refine ⟨t • l, ?_, ?_⟩
        · intro i; simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact mul_nonneg ht (hl i)
        · simp only [hbdef, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]
      set t := (u / f b) + 1 with ht
      have ht0 : 0 ≤ t := by
        have : 0 < u / f b := div_pos_of_neg_of_neg hu hneg
        linarith
      have := hfb _ (hscale t ht0)
      rw [map_smul, smul_eq_mul] at this
      have hne : f b ≠ 0 := hneg.ne
      have h2 : t * f b = u + f b := by
        rw [ht]; field_simp
      linarith
    -- representing f by a vector x
    set x : Fin n → ℝ := fun k => f (fun j => if k = j then 1 else 0) with hx
    have hfx : ∀ v : Fin n → ℝ, f v = v ⬝ᵥ x := by
      intro v
      have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) v
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, dotProduct]
      simp [hx]
    apply h
    refine ⟨x, ?_, ?_⟩
    · rw [← hfx]; linarith
    · intro i
      rw [← hfx]
      exact hnn _ ⟨Pi.single i 1, by intro j; simp [Pi.single_apply]; split_ifs <;> simp, by simp⟩
  · rintro ⟨l, hl, rfl⟩ ⟨x, hx1, hx2⟩
    have : (∑ i, l i • as i) ⬝ᵥ x = ∑ i, l i * (as i ⬝ᵥ x) := by
      rw [sum_dotProduct]
      simp [smul_dotProduct]
    rw [this] at hx1
    have : 0 ≤ ∑ i, l i * (as i ⬝ᵥ x) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hl i) (hx2 i))
    linarith
