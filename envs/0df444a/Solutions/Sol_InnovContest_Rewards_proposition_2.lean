-- Prove2me | solution 1 for InnovContest.Rewards.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:39:50.807991+00:00
-- url     : https://prove2.me/submissions/890206de-9b4e-437d-a54e-0b0d8ddb739e

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model

open MeasureTheory Set

namespace InnovContest.Rewards

theorem amin_mem_Icc (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ) :
    amin M r cp ∈ Icc (0 : ℝ) 1 := by
  classical
  unfold amin
  split_ifs with h
  · constructor
    · exact le_csInf h (fun x hx => hx.1.1)
    · obtain ⟨x, hx⟩ := h
      exact (csInf_le ⟨0, fun y hy => hy.1.1⟩ hx).trans hx.1.2
  · exact ⟨zero_le_one, le_rfl⟩

theorem abilityLaw_apply (M : AbilityModel) {s : Set ℝ} (hs : MeasurableSet s) :
    abilityLaw M s = ∫⁻ y in s ∩ Icc (0 : ℝ) 1, ENNReal.ofReal (M.f y) := by
  unfold abilityLaw
  rw [withDensity_apply _ hs, Measure.restrict_restrict hs]

theorem integrableOn_f (M : AbilityModel) : IntegrableOn M.f (Icc (0 : ℝ) 1) :=
  M.hf.integrableOn_compact isCompact_Icc

theorem abilityLaw_Icc_eq (M : AbilityModel) {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Icc (0 : ℝ) 1) :
    abilityLaw M s = ENNReal.ofReal (∫ y in s, M.f y) := by
  rw [abilityLaw_apply M hs, inter_eq_left.mpr hsub]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact (integrableOn_f M).mono_set hsub
  · filter_upwards [ae_restrict_mem hs] with y hy
    exact (M.hpos y (hsub hy)).le

theorem F_eq_integral (M : AbilityModel) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    M.F a = ∫ y in Ioc 0 a, M.f y := by
  rw [M.hF a ha, intervalIntegral.integral_of_le ha.1]

theorem F_nonneg (M : AbilityModel) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : 0 ≤ M.F a := by
  rw [F_eq_integral M ha]
  apply setIntegral_nonneg measurableSet_Ioc
  intro y hy
  exact (M.hpos y ⟨hy.1.le, hy.2.trans ha.2⟩).le

theorem abilityLaw_Iio (M : AbilityModel) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    abilityLaw M (Iio a) = ENNReal.ofReal (M.F a) := by
  rw [abilityLaw_apply M measurableSet_Iio]
  have h1 : Iio a ∩ Icc (0 : ℝ) 1 = Ico 0 a := by
    ext y; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le.trans ha.2 |>.trans' le_rfl⟩
  rw [h1, F_eq_integral M ha, ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ico]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact (integrableOn_f M).mono_set (fun y hy => ⟨hy.1, hy.2.le.trans ha.2⟩)
  · filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact (M.hpos y ⟨hy.1, hy.2.le.trans ha.2⟩).le

theorem abilityLaw_univ (M : AbilityModel) : abilityLaw M univ = 1 := by
  rw [abilityLaw_apply M MeasurableSet.univ, univ_inter]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_f M)]
  · rw [integral_Icc_eq_integral_Ioc, ← F_eq_integral M ⟨zero_le_one, le_rfl⟩, M.hF1,
      ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact (M.hpos y hy).le

instance abilityLaw_isProb (M : AbilityModel) : IsProbabilityMeasure (abilityLaw M) :=
  ⟨abilityLaw_univ M⟩

theorem abilityLaw_Ici (M : AbilityModel) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    abilityLaw M (Ici a) = ENNReal.ofReal (1 - M.F a) := by
  have hc : Ici a = (Iio a)ᶜ := by ext; simp
  rw [hc, prob_compl_eq_one_sub measurableSet_Iio, abilityLaw_Iio M ha,
    ← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (F_nonneg M ha)]

theorem F_le_one (M : AbilityModel) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : M.F a ≤ 1 := by
  have h := prob_le_one (μ := abilityLaw M) (s := Iio a)
  rw [abilityLaw_Iio M ha] at h
  exact (ENNReal.ofReal_le_one).mp h

instance profileLaw_isProb (M : AbilityModel) : IsProbabilityMeasure (profileLaw M) := by
  unfold profileLaw; infer_instance

/-- Binomial count of coordinates above a threshold `α ∈ [0,1]`. -/
theorem count_above (M : AbilityModel) (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    (profileLaw M).real
      {A | ((Finset.univ : Finset (Fin M.n)).filter (fun i => α ≤ A i)).card = k} =
      (M.n.choose k : ℝ) * (1 - M.F α) ^ k * (M.F α) ^ (M.n - k) := by
  classical
  set T : Finset (Fin M.n) → Set (Fin M.n → ℝ) :=
    fun S => Set.pi univ (fun i => if i ∈ S then Ici α else Iio α) with hT
  have hset : {A : Fin M.n → ℝ |
      ((Finset.univ : Finset (Fin M.n)).filter (fun i => α ≤ A i)).card = k} =
      ⋃ S ∈ (Finset.univ : Finset (Fin M.n)).powersetCard k, T S := by
    ext A
    simp only [mem_setOf_eq, mem_iUnion, Finset.mem_powersetCard, hT, Set.mem_pi,
      mem_univ, true_implies, exists_prop]
    constructor
    · intro h
      refine ⟨_, ⟨Finset.filter_subset _ _, h⟩, fun i => ?_⟩
      by_cases hi : α ≤ A i
      · simp [hi]
      · simp [hi, not_le.mp hi]
    · rintro ⟨S, ⟨_, hS⟩, hA⟩
      have : (Finset.univ : Finset (Fin M.n)).filter (fun i => α ≤ A i) = S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := hA i
        by_cases hi : i ∈ S
        · simp only [hi, if_true, mem_Ici] at this; simp [hi, this]
        · simp only [hi, if_false, mem_Iio] at this; simp [hi, not_le.mpr this]
      rw [this, hS]
  have hdisj : Set.PairwiseDisjoint
      (↑((Finset.univ : Finset (Fin M.n)).powersetCard k)) T := by
    intro S _ S' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro A hA hA'
    apply hne
    ext i
    have h1 := hA i (mem_univ _)
    have h2 := hA' i (mem_univ _)
    by_cases hi : i ∈ S <;> by_cases hi' : i ∈ S' <;> simp_all
    · exact absurd h1 (not_le.mpr h2)
    · exact absurd h2 (not_le.mpr h1)
  have hmeas : ∀ S ∈ (Finset.univ : Finset (Fin M.n)).powersetCard k, MeasurableSet (T S) := by
    intro S _
    apply MeasurableSet.univ_pi
    intro i
    split_ifs
    · exact measurableSet_Ici
    · exact measurableSet_Iio
  have hTS : ∀ S ∈ (Finset.univ : Finset (Fin M.n)).powersetCard k,
      profileLaw M (T S) = ENNReal.ofReal (1 - M.F α) ^ k * ENNReal.ofReal (M.F α) ^ (M.n - k) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    unfold profileLaw
    rw [hT, Measure.pi_pi]
    have : ∀ i : Fin M.n, abilityLaw M (if i ∈ S then Ici α else Iio α) =
        if i ∈ S then ENNReal.ofReal (1 - M.F α) else ENNReal.ofReal (M.F α) := by
      intro i
      split_ifs
      · exact abilityLaw_Ici M hα
      · exact abilityLaw_Iio M hα
    simp_rw [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    congr 2
    · simp [hS.2]
    · have : (Finset.univ.filter (fun i : Fin M.n => i ∉ S)) = Sᶜ := by ext; simp
      rw [this, Finset.card_compl, Fintype.card_fin, hS.2]
  have hm : profileLaw M {A : Fin M.n → ℝ |
      ((Finset.univ : Finset (Fin M.n)).filter (fun i => α ≤ A i)).card = k} =
      (M.n.choose k : ENNReal) *
        (ENNReal.ofReal (1 - M.F α) ^ k * ENNReal.ofReal (M.F α) ^ (M.n - k)) := by
    rw [hset, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hTS, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [measureReal_def, hm]
  have h0 : 0 ≤ M.F α := F_nonneg M hα
  have h1 : 0 ≤ 1 - M.F α := by linarith [F_le_one M hα]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1]
  simp [mul_assoc]

end InnovContest.Rewards

open InnovContest.Rewards in
theorem solution (M : AbilityModel) (budget cp : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) (hcp : 0 ≤ cp) (k : ℕ) (hk : k ≤ M.n) :
    (profileLaw M).real
      {A | ((Finset.univ : Finset (Fin M.n)).filter
        (fun i => amin M r cp ≤ A i)).card = k} =
      (M.n.choose k : ℝ) * (1 - M.F (amin M r cp)) ^ k *
        (M.F (amin M r cp)) ^ (M.n - k) :=
  count_above M _ (amin_mem_Icc M r cp) k
