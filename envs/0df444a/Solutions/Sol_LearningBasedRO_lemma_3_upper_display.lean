-- Prove2me | solution 1 for LearningBasedRO.lemma_3_upper_display
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:15:03.554255+00:00
-- url     : https://prove2.me/submissions/c023c976-88eb-4320-972e-be9463adacd9

import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

private lemma orderStat_ge_iff_card_lt {n : ℕ} (y : Fin n → ℝ) (q : ℝ) (r : ℕ)
    (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    q ≤ orderStat y r ↔ (Finset.univ.filter (fun j => y j < q)).card < r := by
  have hr : 1 ≤ r ∧ r ≤ n := ⟨hr1, hrn⟩
  let idx : Fin n := ⟨r - 1, by omega⟩
  let σ : Equiv.Perm (Fin n) := Tuple.sort y
  have hos : orderStat y r = y (σ idx) := dif_pos hr
  rw [hos]
  have hmono : Monotone (y ∘ σ) := Tuple.monotone_sort y
  constructor
  · intro hq
    have hsub :
        Finset.map σ.symm.toEmbedding (Finset.univ.filter (fun j => y j < q)) ⊆
          Finset.Iio idx := by
      intro m hm
      rcases Finset.mem_map.mp hm with ⟨j, hj, rfl⟩
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Iio]
      by_contra hge
      have hle : idx ≤ σ.symm j := le_of_not_gt hge
      have hval : y (σ idx) ≤ y (σ (σ.symm j)) := hmono hle
      rw [σ.apply_symm_apply] at hval
      linarith [hj.2]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_map, Fin.card_Iio] at hcard
    change (Finset.univ.filter (fun j => y j < q)).card ≤ r - 1 at hcard
    omega
  · intro hlt
    by_contra hnot
    have hlt_q : y (σ idx) < q := lt_of_not_ge hnot
    have hsub :
        Finset.map σ.toEmbedding (Finset.Iic idx) ⊆
          Finset.univ.filter (fun j => y j < q) := by
      intro j hj
      rcases Finset.mem_map.mp hj with ⟨m, hm, rfl⟩
      rw [Finset.mem_Iic] at hm
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, lt_of_le_of_lt (hmono hm) hlt_q⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_map, Fin.card_Iic] at hcard
    change (r - 1) + 1 ≤ (Finset.univ.filter (fun j => y j < q)).card at hcard
    omega

end LearningBasedRO

open LearningBasedRO in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (q : ℝ) (hq : μ (Set.Iic q) = ENNReal.ofReal (1 - ϵ))
    (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    {y : Fin n → ℝ | q ≤ orderStat y r} =
        {y : Fin n → ℝ | (Finset.univ.filter (fun j => y j < q)).card < r} ∧
      (Measure.pi fun _ : Fin n => μ) {y | q ≤ orderStat y r} =
        ENNReal.ofReal (∑ k ∈ Finset.range r, binomTerm n ϵ k) := by
  have hset :
      {y : Fin n → ℝ | q ≤ orderStat y r} =
        {y : Fin n → ℝ | (Finset.univ.filter (fun j => y j < q)).card < r} := by
    ext y
    exact orderStat_ge_iff_card_lt y q r hr1 hrn
  refine ⟨hset, ?_⟩
  rw [hset]
  let A : Set ℝ := Set.Iio q
  have hA_meas : MeasurableSet A := measurableSet_Iio
  have hμA : μ A = ENNReal.ofReal (1 - ϵ) := by
    have hIic : Set.Iic q = A ∪ {q} := by
      ext x
      simp [A, le_iff_lt_or_eq]
    have hdisj : Disjoint A {q} := by simp [A]
    rw [hIic, measure_union hdisj (measurableSet_singleton q), measure_singleton, add_zero] at hq
    exact hq
  have hμAc : μ Aᶜ = ENNReal.ofReal ϵ := by
    have hsum : ENNReal.ofReal (1 - ϵ) + ENNReal.ofReal ϵ = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith), sub_add_cancel, ENNReal.ofReal_one]
    rw [measure_compl hA_meas (measure_ne_top μ A), measure_univ, hμA, ← hsum,
      ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
  let cyl : Finset (Fin n) → Set (Fin n → ℝ) :=
    fun S => Set.univ.pi (fun j => if j ∈ S then A else Aᶜ)
  have hcyl_meas : ∀ S, MeasurableSet (cyl S) := fun S =>
    MeasurableSet.univ_pi fun j => by
      by_cases hj : j ∈ S <;> simp [hj, hA_meas, hA_meas.compl]
  have hcyl_mem : ∀ S y, y ∈ cyl S ↔ Finset.univ.filter (fun j => y j < q) = S := by
    intro S y
    constructor
    · intro hy
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hj := hy j (Set.mem_univ j)
      by_cases hjs : j ∈ S <;> simp [A, hjs] at hj ⊢ <;> exact hj
    · intro hS j _
      rw [← hS]
      by_cases hj : y j < q
      · simp [A, hj]
      · simp [A, hj, not_lt.mp hj]
  have hcyl_prob : ∀ S : Finset (Fin n),
      (Measure.pi fun _ : Fin n => μ) (cyl S) =
        ENNReal.ofReal (1 - ϵ) ^ S.card * ENNReal.ofReal ϵ ^ (n - S.card) := by
    intro S
    rw [Measure.pi_pi]
    have hterm : ∀ j : Fin n,
        μ (if j ∈ S then A else Aᶜ) =
          if j ∈ S then ENNReal.ofReal (1 - ϵ) else ENNReal.ofReal ϵ := by
      intro j
      split_ifs <;> simp [hμA, hμAc]
    simp_rw [hterm, Finset.prod_ite, Finset.prod_const]
    have h1 : Finset.univ.filter (fun j : Fin n => j ∈ S) = S := by
      ext j; simp
    have h2 : (Finset.univ.filter (fun j : Fin n => j ∉ S)).card = n - S.card := by
      have hc : Finset.univ.filter (fun j : Fin n => j ∉ S) = Sᶜ := by
        ext j; simp
      rw [hc, Finset.card_compl, Fintype.card_fin]
    rw [h1, h2]
  let layer : ℕ → Set (Fin n → ℝ) :=
    fun k => ⋃ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), cyl S
  have hlayer_mem : ∀ k y,
      y ∈ layer k ↔ (Finset.univ.filter (fun j => y j < q)).card = k := by
    intro k y
    simp only [layer, Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      hcyl_mem]
    constructor
    · rintro ⟨S, rfl, rfl⟩
      rfl
    · intro hk
      exact ⟨_, hk, rfl⟩
  have hlayer_meas : ∀ k, MeasurableSet (layer k) := fun k =>
    Finset.measurableSet_biUnion _ fun S _ => hcyl_meas S
  have hlayer_prob : ∀ k, k ≤ n →
      (Measure.pi fun _ : Fin n => μ) (layer k) = ENNReal.ofReal (binomTerm n ϵ k) := by
    intro k _hk
    have hdisj : Set.PairwiseDisjoint
        (Finset.powersetCard k (Finset.univ : Finset (Fin n)) : Set (Finset (Fin n))) cyl := by
      intro S₁ _ S₂ _ hne
      refine Set.disjoint_left.mpr fun y hy1 hy2 => hne ?_
      rw [← (hcyl_mem S₁ y).mp hy1, (hcyl_mem S₂ y).mp hy2]
    rw [measure_biUnion_finset hdisj (fun S _ => hcyl_meas S)]
    have hcongr :
        ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            (Measure.pi fun _ : Fin n => μ) (cyl S) =
          ∑ _S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            (ENNReal.ofReal (1 - ϵ) ^ k * ENNReal.ofReal ϵ ^ (n - k)) := by
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [hcyl_prob S, (Finset.mem_powersetCard.mp hS).2]
    rw [hcongr, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h1e : 0 ≤ 1 - ϵ := by linarith
    have he : 0 ≤ ϵ := by linarith
    have hchoose : 0 ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
    rw [binomTerm, ENNReal.ofReal_mul (mul_nonneg hchoose (pow_nonneg h1e k)),
      ENNReal.ofReal_mul hchoose, ENNReal.ofReal_natCast, ENNReal.ofReal_pow h1e,
      ENNReal.ofReal_pow he, mul_assoc]
  have hevent :
      {y : Fin n → ℝ | (Finset.univ.filter (fun j => y j < q)).card < r} =
        ⋃ k ∈ Finset.range r, layer k := by
    ext y
    simp [hlayer_mem]
  have hdisj_layers :
      Set.PairwiseDisjoint (Finset.range r : Set ℕ) layer := by
    intro k₁ _ k₂ _ hne
    refine Set.disjoint_left.mpr fun y hy1 hy2 => hne ?_
    rw [← (hlayer_mem k₁ y).mp hy1, (hlayer_mem k₂ y).mp hy2]
  rw [hevent, measure_biUnion_finset hdisj_layers (fun k _ => hlayer_meas k)]
  have hsum_eq :
      ∑ k ∈ Finset.range r, (Measure.pi fun _ : Fin n => μ) (layer k) =
        ∑ k ∈ Finset.range r, ENNReal.ofReal (binomTerm n ϵ k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    exact hlayer_prob k (le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hrn)
  rw [hsum_eq, ← ENNReal.ofReal_sum_of_nonneg]
  intro k _
  unfold binomTerm
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
    (pow_nonneg (by linarith) _)
