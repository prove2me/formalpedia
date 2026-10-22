-- Prove2me | solution 1 for InnovContest.Rewards.first_term_wta_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:19:01.990979+00:00
-- url     : https://prove2.me/submissions/f33de945-cdc6-4049-a403-67a1f65a4870

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


open MeasureTheory Set

namespace InnovContest.Rewards

/-- The entry set whose infimum is `amin`. -/
def entrySet (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ) : Set ℝ :=
  {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ cp ≤ expReward M r a}

theorem amin_le_of_mem (M : AbilityModel) (r : ℕ → ℝ) (cp a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hc : cp ≤ expReward M r a) : amin M r cp ≤ a := by
  classical
  have hmem : a ∈ {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ cp ≤ expReward M r a} := ⟨ha, hc⟩
  unfold amin
  split_ifs with hne
  · exact csInf_le ⟨0, fun y hy => hy.1.1⟩ hmem
  · exact absurd ⟨a, hmem⟩ hne

theorem le_amin_of_forall (M : AbilityModel) (r : ℕ → ℝ) (cp c : ℝ) (hc1 : c ≤ 1)
    (h : ∀ a ∈ Icc (0 : ℝ) 1, cp ≤ expReward M r a → c ≤ a) : c ≤ amin M r cp := by
  classical
  unfold amin
  split_ifs with hne
  · exact le_csInf hne (fun a ha => h a ha.1 ha.2)
  · exact hc1

theorem amin_eq_one_of_lt (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ)
    (h : ∀ a ∈ Icc (0 : ℝ) 1, expReward M r a < cp) : amin M r cp = 1 := by
  apply le_antisymm (amin_mem_Icc M r cp).2
  apply le_amin_of_forall M r cp 1 le_rfl
  intro a ha hc
  exact absurd hc (not_le.mpr (h a ha))

theorem ordCDF_nonneg (n j : ℕ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ ordCDF n j q := by
  unfold ordCDF
  apply Finset.sum_nonneg
  intro i _
  have : 0 ≤ 1 - q := by linarith [hq.2]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq.1 _)) (pow_nonneg this _)

theorem ordCDF_zero (n : ℕ) (q : ℝ) : ordCDF n 0 q = 1 := by
  unfold ordCDF
  have h := add_pow q (1 - q) n
  rw [show q + (1 - q) = 1 by ring, one_pow] at h
  refine Eq.trans ?_ h.symm
  rw [Finset.range_eq_Ico]
  have : Finset.Icc 0 n = Finset.Ico 0 (n + 1) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [this]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem ordCDF_top (n : ℕ) (q : ℝ) : ordCDF n n q = q ^ n := by
  unfold ordCDF
  simp

theorem F_mem_Icc (M : AbilityModel) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    M.F a ∈ Icc (0 : ℝ) 1 := ⟨F_nonneg M ha, F_le_one M ha⟩

/-- Abel summation for the reward differentials. -/
theorem abel_sum (r : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * (r j - r (j + 1)) =
      ∑ j ∈ Finset.Icc 1 n, r j - n * r (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    push_cast; ring

theorem expReward_equalSplit (M : AbilityModel) (budget : ℝ) (m : ℕ)
    (hm1 : 1 ≤ m) (hmn : m ≤ M.n) (a : ℝ) :
    expReward M (equalSplit budget m) a =
      budget / m * ordCDF (M.n - 1) (M.n - m) (M.F a) := by
  unfold expReward
  rw [Finset.sum_eq_single m]
  · simp [equalSplit, hm1]
  · intro j hj hjm
    rw [Finset.mem_Icc] at hj
    have : equalSplit budget m j - equalSplit budget m (j + 1) = 0 := by
      unfold equalSplit
      rcases lt_or_gt_of_ne hjm with h | h
      · rw [if_pos ⟨hj.1, h.le⟩, if_pos ⟨by omega, by omega⟩]; ring
      · rw [if_neg (by omega), if_neg (by omega)]; ring
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hm1, hmn⟩) h

theorem equalSplit_feasible (n : ℕ) (budget : ℝ) (hb : 0 ≤ budget) (m : ℕ)
    (hm1 : 1 ≤ m) (hmn : m ≤ n) : Feasible n budget (equalSplit budget m) := by
  have hbm : 0 ≤ budget / m := div_nonneg hb (Nat.cast_nonneg m)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [equalSplit]
  · intro j _ _
    unfold equalSplit
    split_ifs <;> first | exact le_rfl | exact hbm | omega
  · intro j hj
    unfold equalSplit
    rw [if_neg (by omega)]
  · unfold equalSplit
    split_ifs <;> first | exact hbm | exact le_rfl
  · unfold equalSplit
    rw [← Finset.sum_filter]
    have : (Finset.Icc 1 n).filter (fun j => 1 ≤ j ∧ j ≤ m) = Finset.Icc 1 m := by
      ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [this, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    rw [show m + 1 - 1 = m by omega, mul_div_cancel₀ _ hm0]

/-- The LP bound: at a fixed ability, a feasible allocation's expected reward is at most that of
some equal split. -/
theorem expReward_le_equalSplit (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ∃ m ∈ Finset.Icc 1 M.n, expReward M r a ≤ expReward M (equalSplit budget m) a := by
  obtain ⟨hr0, hdec, hzero, hrn, hsum⟩ := hr
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  have hne : (Finset.Icc 1 M.n).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩⟩
  set H : ℕ → ℝ := fun j => ordCDF (M.n - 1) (M.n - j) (M.F a) with hH
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 M.n) (fun j => H j / j) hne
  refine ⟨m, hm, ?_⟩
  rw [Finset.mem_Icc] at hm
  rw [expReward_equalSplit M budget m hm.1 hm.2]
  have hq := F_mem_Icc M ha
  have hHm : 0 ≤ H m / m := div_nonneg (ordCDF_nonneg _ _ hq) (Nat.cast_nonneg m)
  have hδ : ∀ j ∈ Finset.Icc 1 M.n, 0 ≤ r j - r (j + 1) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases lt_or_eq_of_le hj.2 with h | h
    · linarith [hdec j hj.1 hj.2]
    · rw [h, hzero (M.n + 1) (by omega)]; linarith
  have step1 : expReward M r a ≤
      ∑ j ∈ Finset.Icc 1 M.n, (r j - r (j + 1)) * ((j : ℝ) * (H m / m)) := by
    unfold expReward
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (hδ j hj)
    have h1 := hmax j hj
    have hj0 : (0 : ℝ) < j := by
      have := (Finset.mem_Icc.mp hj).1; exact_mod_cast this
    have : H j = j * (H j / j) := by field_simp
    calc ordCDF (M.n - 1) (M.n - j) (M.F a) = H j := rfl
      _ = j * (H j / j) := this
      _ ≤ j * (H m / m) := mul_le_mul_of_nonneg_left h1 hj0.le
  have step2 : ∑ j ∈ Finset.Icc 1 M.n, (r j - r (j + 1)) * ((j : ℝ) * (H m / m)) =
      (∑ j ∈ Finset.Icc 1 M.n, r j) * (H m / m) := by
    have abel_sum_zero : ∑ j ∈ Finset.Icc 1 M.n, (j : ℝ) * (r j - r (j + 1)) =
        ∑ j ∈ Finset.Icc 1 M.n, r j := by
      rw [abel_sum, hzero (M.n + 1) (by omega)]; ring
    rw [← abel_sum_zero, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  calc expReward M r a ≤ _ := step1
    _ = (∑ j ∈ Finset.Icc 1 M.n, r j) * (H m / m) := step2
    _ ≤ budget * (H m / m) := mul_le_mul_of_nonneg_right hsum hHm
    _ = budget / m * ordCDF (M.n - 1) (M.n - m) (M.F a) := by rw [hH]; ring

theorem continuousOn_F (M : AbilityModel) : ContinuousOn M.F (Icc (0 : ℝ) 1) := by
  have h : ContinuousOn (fun a => ∫ y in (0 : ℝ)..a, M.f y) (Icc (0 : ℝ) 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := M.f)
      (a := 0) (b := 1) (by rw [uIcc_of_le zero_le_one]; exact integrableOn_f M)
    rwa [uIcc_of_le zero_le_one] at this
  exact h.congr (fun a ha => M.hF a ha)

/-- Winner-take-all with `budget > cp` attracts entry below the top ability. -/
theorem amin_wta_lt_one (M : AbilityModel) (budget cp : ℝ) (hbudget : cp < budget) :
    amin M (equalSplit budget 1) cp < 1 := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  set g : ℝ → ℝ := fun a => budget * M.F a ^ (M.n - 1) with hg
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ((continuousOn_F M).pow _)
  have hg1 : g 1 = budget := by simp [hg, M.hF1]
  have hcw := hgc 1 ⟨zero_le_one, le_rfl⟩
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨ε, hε, hball⟩ := hcw (budget - cp) (by linarith)
  set x : ℝ := max 0 (1 - ε / 2) with hx
  have hx0 : 0 ≤ x := le_max_left _ _
  have hx1 : x < 1 := max_lt (by norm_num) (by linarith)
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, hx1.le⟩
  have hdist : dist x 1 < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : 1 - ε / 2 ≤ x := le_max_right _ _
      linarith
    · linarith
  have hgx := hball hxI hdist
  rw [Real.dist_eq, hg1, abs_lt] at hgx
  have hle : amin M (equalSplit budget 1) cp ≤ x := by
    apply amin_le_of_mem M _ cp x hxI
    rw [expReward_equalSplit M budget 1 le_rfl hn1, ordCDF_top]
    simp only [Nat.cast_one, div_one]
    have : g x = budget * M.F x ^ (M.n - 1) := rfl
    linarith
  linarith

/-- An even split across all `n` ranks attracts nobody when `budget < n cp`. -/
theorem amin_all_eq_one (M : AbilityModel) (budget cp : ℝ)
    (hupper : budget < (M.n : ℝ) * cp) : amin M (equalSplit budget M.n) cp = 1 := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  apply amin_eq_one_of_lt
  intro a _
  rw [expReward_equalSplit M budget M.n hn1 le_rfl, Nat.sub_self, ordCDF_zero, mul_one]
  have hn0 : (0 : ℝ) < M.n := by exact_mod_cast (show 0 < M.n by omega)
  rw [div_lt_iff₀ hn0]; linarith

theorem sup_filter_mem (s : Finset ℕ) (p : ℕ → Prop) {inst : DecidablePred p}
    (h : ∃ m ∈ s, p m) : (s.filter p).sup id ∈ s ∧ p ((s.filter p).sup id) := by
  have hne : (s.filter p).Nonempty := by
    obtain ⟨m, hm, hp⟩ := h; exact ⟨m, Finset.mem_filter.mpr ⟨hm, hp⟩⟩
  obtain ⟨ms, hms, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [hsup]
  exact Finset.mem_filter.mp hms

theorem mstarP_spec (M : AbilityModel) (budget cp : ℝ) :
    mstarP M budget cp ∈ Finset.Icc 1 M.n ∧
      ∀ k ∈ Finset.Icc 1 M.n, amin M (equalSplit budget (mstarP M budget cp)) cp ≤
        amin M (equalSplit budget k) cp := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  have hne : (Finset.Icc 1 M.n).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩⟩
  obtain ⟨m0, hm0, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 M.n)
    (fun m => amin M (equalSplit budget m) cp) hne
  unfold mstarP
  exact sup_filter_mem _ _ ⟨m0, hm0, hmin⟩

end InnovContest.Rewards



open MeasureTheory Set

namespace InnovContest.Rewards

theorem failProb_eq (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ) :
    failProb M r cp = M.F (amin M r cp) ^ M.n := by
  have h := count_above M (amin M r cp) (amin_mem_Icc M r cp) 0
  have hs : {A : Fin M.n → ℝ | ∀ i, A i < amin M r cp} =
      {A | ((Finset.univ : Finset (Fin M.n)).filter (fun i => amin M r cp ≤ A i)).card = 0} := by
    ext A
    simp only [Set.mem_setOf_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_le]
  unfold failProb
  rw [hs, h]
  simp

theorem intervalIntegrable_f (M : AbilityModel) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : IntervalIntegrable M.f volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply (integrableOn_f M).mono_set
  intro x hx
  rw [mem_uIcc] at hx
  rcases hx with hx | hx
  · exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  · exact ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩

theorem F_sub_eq (M : AbilityModel) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : M.F b - M.F a = ∫ y in a..b, M.f y := by
  rw [M.hF a ha, M.hF b hb]
  exact intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_f M ⟨le_rfl, zero_le_one⟩ hb)
    (intervalIntegrable_f M ⟨le_rfl, zero_le_one⟩ ha)

theorem F_mono (M : AbilityModel) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) : M.F a ≤ M.F b := by
  have h := F_sub_eq M ha hb
  have : 0 ≤ ∫ y in a..b, M.f y := by
    apply intervalIntegral.integral_nonneg hab
    intro y hy
    exact (M.hpos y ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩).le
  linarith

theorem F_strictMono (M : AbilityModel) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) : M.F a < M.F b := by
  have h := F_sub_eq M ha hb
  have : 0 < ∫ y in a..b, M.f y := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_f M ha hb) _ hab
    intro y hy
    exact M.hpos y ⟨ha.1.trans hy.1.le, hy.2.le.trans hb.2⟩
  linarith

theorem failProb_mono (M : AbilityModel) (r s : ℕ → ℝ) (cp : ℝ)
    (h : amin M r cp ≤ amin M s cp) : failProb M r cp ≤ failProb M s cp := by
  rw [failProb_eq, failProb_eq]
  exact pow_le_pow_left₀ (F_nonneg M (amin_mem_Icc M r cp))
    (F_mono M (amin_mem_Icc M r cp) (amin_mem_Icc M s cp) h) _

theorem failProb_strictMono (M : AbilityModel) (r s : ℕ → ℝ) (cp : ℝ)
    (h : amin M r cp < amin M s cp) : failProb M r cp < failProb M s cp := by
  rw [failProb_eq, failProb_eq]
  have hn : M.n ≠ 0 := by have := M.hn; omega
  exact pow_lt_pow_left₀ (F_strictMono M (amin_mem_Icc M r cp) (amin_mem_Icc M s cp) h)
    (F_nonneg M (amin_mem_Icc M r cp)) hn

theorem feasible_antitone (n : ℕ) (budget : ℝ) (r : ℕ → ℝ) (hr : Feasible n budget r)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n + 1) : r j ≤ r i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    exact (hr.2.1 k (le_trans hi hik) (by omega)).trans (ih (by omega))

theorem feasible_nonneg (n : ℕ) (budget : ℝ) (r : ℕ → ℝ) (hr : Feasible n budget r)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) : 0 ≤ r j :=
  hr.2.2.2.1.trans (feasible_antitone n budget r hr hj1 hjn (by omega))

theorem expReward_nonneg (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : 0 ≤ expReward M r a := by
  unfold expReward
  apply Finset.sum_nonneg
  intro j hj
  rw [Finset.mem_Icc] at hj
  apply mul_nonneg _ (ordCDF_nonneg _ _ (F_mem_Icc M ha))
  have := feasible_antitone M.n budget r hr hj.1 (Nat.le_succ j) (by omega)
  linarith

theorem numRewards_wta (n : ℕ) (hn : 1 ≤ n) (budget : ℝ) (hb : 0 < budget) :
    numRewards n (equalSplit budget 1) = 1 := by
  unfold numRewards
  have : (Finset.Icc 1 n).filter (fun j => 0 < equalSplit budget 1 j) = {1} := by
    ext j
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    unfold equalSplit
    constructor
    · rintro ⟨_, h3⟩
      split_ifs at h3 with h
      · omega
      · exact absurd h3 (lt_irrefl 0)
    · rintro rfl
      refine ⟨⟨le_rfl, hn⟩, ?_⟩
      simpa using hb
  rw [this, Finset.card_singleton]

theorem single_reward_zero (n : ℕ) (budget : ℝ) (r : ℕ → ℝ) (hr : Feasible n budget r)
    (h1 : numRewards n r ≤ 1) {j : ℕ} (hj : 2 ≤ j) : r j = 0 := by
  by_cases hjn : n < j
  · exact hr.2.2.1 j hjn
  push_neg at hjn
  have h2n : 2 ≤ n := hj.trans hjn
  have hr2 : r 2 ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    have hr1 : 0 < r 1 := lt_of_lt_of_le hpos (feasible_antitone n budget r hr le_rfl
      (by norm_num) (by omega))
    have hsub : ({1, 2} : Finset ℕ) ⊆ (Finset.Icc 1 n).filter (fun j => 0 < r j) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hr1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, h2n⟩, hpos⟩
    have := Finset.card_le_card hsub
    unfold numRewards at h1
    simp at this
    omega
  have := feasible_antitone n budget r hr (by norm_num : 1 ≤ 2) hj (by omega)
  have := feasible_nonneg n budget r hr (by omega : 1 ≤ j) hjn
  linarith

theorem amin_wta_le_single (M : AbilityModel) (budget cp : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) (h1 : numRewards M.n r ≤ 1) :
    amin M (equalSplit budget 1) cp ≤ amin M r cp := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  apply le_amin_of_forall M r cp _ (amin_mem_Icc M _ cp).2
  intro a ha hc
  apply amin_le_of_mem M _ cp a ha
  have hz := fun j (hj : 2 ≤ j) => single_reward_zero M.n budget r hr h1 hj
  have hexp : expReward M r a = r 1 * ordCDF (M.n - 1) (M.n - 1) (M.F a) := by
    unfold expReward
    rw [Finset.sum_eq_single 1]
    · rw [hz 2 le_rfl, sub_zero]
    · intro j hj hj1
      rw [Finset.mem_Icc] at hj
      rw [hz j (by omega), hz (j + 1) (by omega), sub_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩) h
  have hr1 : r 1 ≤ budget := by
    have hs := hr.2.2.2.2
    have : r 1 ≤ ∑ j ∈ Finset.Icc 1 M.n, r j :=
      Finset.single_le_sum (fun j hj => feasible_nonneg M.n budget r hr
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2) (Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩)
    linarith
  rw [expReward_equalSplit M budget 1 le_rfl hn1]
  rw [hexp] at hc
  have hH := ordCDF_nonneg (M.n - 1) (M.n - 1) (F_mem_Icc M ha)
  simp only [Nat.cast_one, div_one]
  nlinarith

theorem objective_lt_wta (M : AbilityModel) (budget cp cf : ℝ) (hcf : 0 ≤ cf) (r : ℕ → ℝ)
    (hG : bestExpected M r cp < bestExpected M (equalSplit budget 1) cp)
    (hD : failProb M (equalSplit budget 1) cp ≤ failProb M r cp) :
    firmObjective M r cp cf < firmObjective M (equalSplit budget 1) cp cf := by
  unfold firmObjective
  nlinarith [mul_le_mul_of_nonneg_left hD hcf]

theorem amin_zero (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) : amin M r 0 = 0 := by
  apply le_antisymm _ (amin_mem_Icc M r 0).1
  exact amin_le_of_mem M r 0 0 ⟨le_rfl, zero_le_one⟩
    (expReward_nonneg M budget r hr ⟨le_rfl, zero_le_one⟩)

theorem failProb_zero (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) : failProb M r 0 = 0 := by
  rw [failProb_eq, amin_zero M budget r hr]
  have hF0 : M.F 0 = 0 := by
    rw [M.hF 0 ⟨le_rfl, zero_le_one⟩, intervalIntegral.integral_same]
  rw [hF0]
  exact zero_pow (by have := M.hn; omega)


end InnovContest.Rewards


open MeasureTheory Set

namespace InnovContest.Rewards

theorem continuous_ordCDF (N k : ℕ) : Continuous (fun q : ℝ => ordCDF N k q) := by
  unfold ordCDF
  exact continuous_finset_sum _ (fun i _ => by fun_prop)

theorem ordCDF_le_one (N k : ℕ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ordCDF N k q ≤ 1 := by
  rw [← ordCDF_zero N q]
  unfold ordCDF
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
  · intro i _ _
    have : 0 ≤ 1 - q := by linarith [hq.2]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq.1 _)) (pow_nonneg this _)

/-- Cross-multiplied monotonicity of `ordCDF N k q / q ^ N`. -/
theorem ordCDF_cross (N k : ℕ) {q q' : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1) :
    ordCDF N k q' * q ^ N ≤ ordCDF N k q * q' ^ N := by
  unfold ordCDF
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_Icc] at hi
  have e1 : q ^ N = q ^ i * q ^ (N - i) := by rw [← pow_add, Nat.add_sub_cancel' hi.2]
  have e2 : q' ^ N = q' ^ i * q' ^ (N - i) := by rw [← pow_add, Nat.add_sub_cancel' hi.2]
  rw [e1, e2]
  have h0 : 0 ≤ q * (1 - q') := mul_nonneg hq (by linarith)
  have key : (q * (1 - q')) ^ (N - i) ≤ (q' * (1 - q)) ^ (N - i) :=
    pow_le_pow_left₀ h0 (by nlinarith) _
  have hc : 0 ≤ (N.choose i : ℝ) * (q' ^ i * q ^ i) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg (hq.trans hqq) _) (pow_nonneg hq _))
  calc (N.choose i : ℝ) * q' ^ i * (1 - q') ^ (N - i) * (q ^ i * q ^ (N - i))
      = (N.choose i : ℝ) * (q' ^ i * q ^ i) * (q * (1 - q')) ^ (N - i) := by
        rw [mul_pow]; ring
    _ ≤ (N.choose i : ℝ) * (q' ^ i * q ^ i) * (q' * (1 - q)) ^ (N - i) :=
        mul_le_mul_of_nonneg_left key hc
    _ = (N.choose i : ℝ) * q ^ i * (1 - q) ^ (N - i) * (q' ^ i * q' ^ (N - i)) := by
        rw [mul_pow]; ring

theorem continuousOn_expReward_eq (M : AbilityModel) (budget : ℝ) (m : ℕ)
    (hm1 : 1 ≤ m) (hmn : m ≤ M.n) :
    ContinuousOn (expReward M (equalSplit budget m)) (Icc (0 : ℝ) 1) := by
  have h : ContinuousOn (fun a => budget / m * ordCDF (M.n - 1) (M.n - m) (M.F a))
      (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ((continuous_ordCDF _ _).comp_continuousOn (continuousOn_F M))
  exact h.congr (fun a _ => expReward_equalSplit M budget m hm1 hmn a)

/-- The entry threshold is attained when the expected reward is continuous. -/
theorem amin_attained (M : AbilityModel) (r : ℕ → ℝ) (cp : ℝ)
    (hc : ContinuousOn (expReward M r) (Icc (0 : ℝ) 1))
    (hne : ∃ a ∈ Icc (0 : ℝ) 1, cp ≤ expReward M r a) :
    cp ≤ expReward M r (amin M r cp) := by
  classical
  have hS : {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ cp ≤ expReward M r a}.Nonempty := by
    obtain ⟨a, ha, h⟩ := hne; exact ⟨a, ha, h⟩
  have hcl : IsClosed {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ cp ≤ expReward M r a} := by
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := cp))
    exact this
  have hmem := hcl.csInf_mem hS ⟨0, fun y hy => hy.1.1⟩
  have : amin M r cp = sInf {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ cp ≤ expReward M r a} := by
    unfold amin; rw [if_pos hS]
  rw [this]
  exact hmem.2

/-- A continuous function exceeding `cp` at `b ∈ (0,1]` exceeds it slightly to the left. -/
theorem exists_left_of_gt {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1)) {b cp : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hgb : cp < g b) :
    ∃ x ∈ Icc (0 : ℝ) 1, x < b ∧ cp < g x := by
  have hcw := hg b ⟨hb0.le, hb1⟩
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨ε, hε, hball⟩ := hcw (g b - cp) (by linarith)
  set x : ℝ := max 0 (b - ε / 2) with hx
  have hx0 : 0 ≤ x := le_max_left _ _
  have hxb : x < b := max_lt hb0 (by linarith)
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, hxb.le.trans hb1⟩
  have hdist : dist x b < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : b - ε / 2 ≤ x := le_max_right _ _
      linarith
    · linarith
  have hgx := hball hxI hdist
  rw [Real.dist_eq, abs_lt] at hgx
  exact ⟨x, hxI, hxb, by linarith⟩

/-- Winner-take-all is weakly participation-maximal among equal splits. -/
def WtaBest (M : AbilityModel) (budget cp : ℝ) : Prop :=
  ∀ m ∈ Finset.Icc 1 M.n,
    amin M (equalSplit budget 1) cp ≤ amin M (equalSplit budget m) cp

theorem wtaBest_small (M : AbilityModel) (budget cp : ℝ) (hcp : 0 < cp)
    (hb : budget < 2 * cp) : WtaBest M budget cp := by
  intro m hm
  rw [Finset.mem_Icc] at hm
  rcases eq_or_lt_of_le hm.1 with h | h
  · rw [← h]
  · have hlt1 : ∀ a ∈ Icc (0 : ℝ) 1, expReward M (equalSplit budget m) a < cp := by
      intro a ha
      rw [expReward_equalSplit M budget m hm.1 hm.2]
      have h1 := ordCDF_le_one (M.n - 1) (M.n - m) (F_mem_Icc M ha)
      have h0 := ordCDF_nonneg (M.n - 1) (M.n - m) (F_mem_Icc M ha)
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast h
      by_cases hbn : budget ≤ 0
      · have : budget / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hbn (by linarith)
        nlinarith
      push_neg at hbn
      have : budget / m ≤ budget / 2 := div_le_div_of_nonneg_left hbn.le (by norm_num) hm2
      nlinarith
    rw [amin_eq_one_of_lt M (equalSplit budget m) cp hlt1]
    exact (amin_mem_Icc M _ cp).2

theorem amin_wta_pos (M : AbilityModel) (budget cp : ℝ) (hcp : 0 < cp) (hb : cp < budget) :
    0 < amin M (equalSplit budget 1) cp := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  have hatt := amin_attained M _ cp (continuousOn_expReward_eq M budget 1 le_rfl hn1)
    ⟨1, ⟨zero_le_one, le_rfl⟩, by
      rw [expReward_equalSplit M budget 1 le_rfl hn1, ordCDF_top, M.hF1]; simp; linarith⟩
  rcases eq_or_lt_of_le (amin_mem_Icc M (equalSplit budget 1) cp).1 with h | h
  · exfalso
    rw [← h, expReward_equalSplit M budget 1 le_rfl hn1, ordCDF_top] at hatt
    have hF0 : M.F 0 = 0 := by
      rw [M.hF 0 ⟨le_rfl, zero_le_one⟩, intervalIntegral.integral_same]
    rw [hF0, zero_pow (by have := M.hn; omega)] at hatt
    linarith
  · exact h

/-- Downward closure in the budget. -/
theorem wtaBest_mono (M : AbilityModel) (cp B B' : ℝ) (hcp : 0 < cp) (hB' : cp < B')
    (hBB : B' < B) (hP : WtaBest M B cp) : WtaBest M B' cp := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  by_contra hlt
  push_neg at hlt
  set a := amin M (equalSplit B' m) cp with ha
  have haI : a ∈ Icc (0 : ℝ) 1 := amin_mem_Icc M _ cp
  -- `a` lies in the entry set of the `m`-split at budget `B'`
  have hSne : ∃ x ∈ Icc (0 : ℝ) 1, cp ≤ expReward M (equalSplit B' m) x := by
    by_contra hno
    push_neg at hno
    have h0 := amin_eq_one_of_lt M _ cp hno
    have h1 := (amin_mem_Icc M (equalSplit B' 1) cp).2
    have : a = 1 := ha.trans h0
    linarith
  have haS := amin_attained M _ cp (continuousOn_expReward_eq M B' m hm'.1 hm'.2) hSne
  rw [← ha, expReward_equalSplit M B' m hm'.1 hm'.2] at haS
  -- but not in that of winner-take-all at `B'`
  have ha1 : B' * M.F a ^ (M.n - 1) < cp := by
    by_contra hge
    push_neg at hge
    have := amin_le_of_mem M (equalSplit B' 1) cp a haI (by
      rw [expReward_equalSplit M B' 1 le_rfl hn1, ordCDF_top]; simpa using hge)
    linarith
  set b := amin M (equalSplit B 1) cp with hb
  have hbI : b ∈ Icc (0 : ℝ) 1 := amin_mem_Icc M _ cp
  have hb0 : 0 < b := amin_wta_pos M B cp hcp (hB'.trans hBB)
  have hbS : cp ≤ B * M.F b ^ (M.n - 1) := by
    have := amin_attained M _ cp (continuousOn_expReward_eq M B 1 le_rfl hn1)
      ⟨1, ⟨zero_le_one, le_rfl⟩, by
        rw [expReward_equalSplit M B 1 le_rfl hn1, ordCDF_top, M.hF1]; simp; linarith⟩
    rw [← hb, expReward_equalSplit M B 1 le_rfl hn1, ordCDF_top] at this
    simpa using this
  set h := fun q => ordCDF (M.n - 1) (M.n - m) q with hh
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hB'0 : 0 < B' := by linarith
  have hB0 : 0 < B := by linarith
  -- `m F(a)^{n-1} < h(F a)`
  have hi : (m : ℝ) * M.F a ^ (M.n - 1) < h (M.F a) := by
    have : B' * M.F a ^ (M.n - 1) < B' / m * h (M.F a) := lt_of_lt_of_le ha1 haS
    rw [div_mul_eq_mul_div, lt_div_iff₀ hm0] at this
    nlinarith
  have hFb : 0 < M.F b := by
    have := F_strictMono M ⟨le_rfl, zero_le_one⟩ hbI hb0
    have hF0 : M.F 0 = 0 := by
      rw [M.hF 0 ⟨le_rfl, zero_le_one⟩, intervalIntegral.integral_same]
    linarith
  by_cases hba : a < b
  · -- `a` already beats winner-take-all at budget `B`
    have : amin M (equalSplit B m) cp ≤ a := by
      apply amin_le_of_mem M _ cp a haI
      rw [expReward_equalSplit M B m hm'.1 hm'.2]
      have h0 := ordCDF_nonneg (M.n - 1) (M.n - m) (F_mem_Icc M haI)
      have : B' / m ≤ B / m := div_le_div_of_nonneg_right hBB.le hm0.le
      nlinarith
    have := hP m hm
    linarith
  push_neg at hba
  have hFab : M.F b ≤ M.F a := F_mono M hbI haI hba
  have hFa : 0 < M.F a := lt_of_lt_of_le hFb hFab
  have hcross := ordCDF_cross (M.n - 1) (M.n - m) (F_nonneg M hbI) hFab (F_le_one M haI)
  have hpa : 0 < M.F a ^ (M.n - 1) := pow_pos hFa _
  have hpb : 0 < M.F b ^ (M.n - 1) := pow_pos hFb _
  -- hence `m F(b)^{n-1} < h(F b)`
  have hj : (m : ℝ) * M.F b ^ (M.n - 1) < h (M.F b) := by
    have h1 : (m : ℝ) * M.F a ^ (M.n - 1) * M.F b ^ (M.n - 1) <
        h (M.F a) * M.F b ^ (M.n - 1) := mul_lt_mul_of_pos_right hi hpb
    have h2 : M.F a ^ (M.n - 1) * ((m : ℝ) * M.F b ^ (M.n - 1)) <
        M.F a ^ (M.n - 1) * h (M.F b) := by
      calc M.F a ^ (M.n - 1) * ((m : ℝ) * M.F b ^ (M.n - 1))
          = (m : ℝ) * M.F a ^ (M.n - 1) * M.F b ^ (M.n - 1) := by ring
        _ < h (M.F a) * M.F b ^ (M.n - 1) := h1
        _ ≤ h (M.F b) * M.F a ^ (M.n - 1) := hcross
        _ = M.F a ^ (M.n - 1) * h (M.F b) := by ring
    exact lt_of_mul_lt_mul_left h2 hpa.le
  have hgb : cp < expReward M (equalSplit B m) b := by
    rw [expReward_equalSplit M B m hm'.1 hm'.2]
    have : B * M.F b ^ (M.n - 1) < B / m * h (M.F b) := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hm0]
      nlinarith
    linarith
  obtain ⟨x, hxI, hxb, hx⟩ := exists_left_of_gt
    (continuousOn_expReward_eq M B m hm'.1 hm'.2) hb0 hbI.2 hgb
  have h1 := amin_le_of_mem M _ cp x hxI hx.le
  have h2 := hP m hm
  linarith

end InnovContest.Rewards



open MeasureTheory Set

namespace InnovContest.Rewards

/-- The marginal-performance density `y ↦ y · R'(y)` on `[0,1]` (ranks `1,…,n-1`). -/
noncomputable def rho (M : AbilityModel) (r : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (M.n - 1), (r j - r (j + 1)) * (y * ordPDF (M.n - 1) (M.n - j) M.F M.f y)

theorem continuousOn_ordPDF (M : AbilityModel) (N k : ℕ) :
    ContinuousOn (fun y => ordPDF N k M.F M.f y) (Icc (0 : ℝ) 1) := by
  unfold ordPDF
  have hF := continuousOn_F M
  exact ((((continuousOn_const.mul continuousOn_const).mul (hF.pow _)).mul
    ((continuousOn_const.sub hF).pow _)).mul M.hf)

theorem continuousOn_rho (M : AbilityModel) (r : ℕ → ℝ) :
    ContinuousOn (rho M r) (Icc (0 : ℝ) 1) := by
  unfold rho
  apply continuousOn_finset_sum
  intro j _
  exact continuousOn_const.mul (continuousOn_id.mul (continuousOn_ordPDF M _ _))

theorem ordPDF_nonneg (M : AbilityModel) (N k : ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ ordPDF N k M.F M.f y := by
  unfold ordPDF
  have h0 := F_nonneg M hy
  have h1 : 0 ≤ 1 - M.F y := by linarith [F_le_one M hy]
  have h2 := (M.hpos y hy).le
  positivity

theorem rho_nonneg (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ) (hr : Feasible M.n budget r)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : 0 ≤ rho M r y := by
  unfold rho
  apply Finset.sum_nonneg
  intro j hj
  rw [Finset.mem_Icc] at hj
  have := hr.2.1 j hj.1 (by omega)
  exact mul_nonneg (by linarith) (mul_nonneg hy.1 (ordPDF_nonneg M _ _ hy))

theorem intervalIntegrable_of_Icc {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1)) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) : IntervalIntegrable g volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hg.mono
  intro x hx
  rw [mem_uIcc] at hx
  rcases hx with hx | hx
  · exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  · exact ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩

theorem xstar_eq_integral (M : AbilityModel) (r : ℕ → ℝ) (cp a : ℝ)
    (ha : amin M r cp ≤ a) (ha1 : a ≤ 1) :
    xstar M r cp a = ∫ y in (amin M r cp)..a, rho M r y := by
  have hα := amin_mem_Icc M r cp
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨hα.1.trans ha, ha1⟩
  unfold xstar
  rw [if_neg (not_lt.mpr ha)]
  unfold rho
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
  · intro j _
    apply IntervalIntegrable.const_mul
    exact intervalIntegrable_of_Icc (continuousOn_id.mul (continuousOn_ordPDF M _ _)) hα haI

/-- The equilibrium payoff as a function of the top ability. -/
noncomputable def psi (M : AbilityModel) (r : ℕ → ℝ) (cp a : ℝ) : ℝ :=
  if amin M r cp ≤ a then xstar M r cp a else 0

theorem psi_eq_setIntegral (M : AbilityModel) (r : ℕ → ℝ) (cp a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    psi M r cp a = ∫ y in Ioc (amin M r cp) 1, (Iic a).indicator (rho M r) y := by
  rw [setIntegral_indicator measurableSet_Iic]
  unfold psi
  split_ifs with h
  · rw [xstar_eq_integral M r cp a h ha.2, intervalIntegral.integral_of_le h]
    have hset : Ioc (amin M r cp) 1 ∩ Iic a = Ioc (amin M r cp) a := by
      ext y; simp only [mem_Ioc, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans ha.2⟩, h2⟩
    rw [hset]
  · push_neg at h
    have : Ioc (amin M r cp) 1 ∩ Iic a = ∅ := by
      ext y; simp only [mem_Ioc, mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h1, _⟩, h2⟩; linarith
    rw [this, Measure.restrict_empty, integral_zero_measure]

theorem integral_rho_nonneg (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a ≤ b) : 0 ≤ ∫ y in a..b, rho M r y := by
  apply intervalIntegral.integral_nonneg hab
  intro y hy
  exact rho_nonneg M budget r hr ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩

theorem psi_nonneg (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ) (hr : Feasible M.n budget r)
    (cp : ℝ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : 0 ≤ psi M r cp a := by
  unfold psi
  split_ifs with h
  · rw [xstar_eq_integral M r cp a h ha.2]
    exact integral_rho_nonneg M budget r hr (amin_mem_Icc M r cp) ha h
  · exact le_rfl

theorem psi_mono (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ) (hr : Feasible M.n budget r)
    (cp : ℝ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
    psi M r cp a ≤ psi M r cp b := by
  have hα := amin_mem_Icc M r cp
  by_cases h : amin M r cp ≤ a
  · have hb' : amin M r cp ≤ b := h.trans hab
    unfold psi
    rw [if_pos h, if_pos hb', xstar_eq_integral M r cp a h ha.2,
      xstar_eq_integral M r cp b hb' hb.2,
      ← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_Icc (continuousOn_rho M r) hα ha)
        (intervalIntegrable_of_Icc (continuousOn_rho M r) ha hb)]
    linarith [integral_rho_nonneg M budget r hr ha hb hab]
  · have : psi M r cp a = 0 := by unfold psi; rw [if_neg h]
    rw [this]
    exact psi_nonneg M budget r hr cp hb

end InnovContest.Rewards


open MeasureTheory Set

namespace InnovContest.Rewards

theorem univ_nonempty_fin (M : AbilityModel) : (Finset.univ : Finset (Fin M.n)).Nonempty :=
  ⟨⟨0, by have := M.hn; omega⟩, Finset.mem_univ _⟩

/-- The highest ability in a profile. -/
noncomputable def amax (M : AbilityModel) (A : Fin M.n → ℝ) : ℝ :=
  Finset.univ.sup' (univ_nonempty_fin M) A

theorem measurable_amax (M : AbilityModel) : Measurable (amax M) := by
  have := Finset.measurable_sup' (univ_nonempty_fin M)
    (f := fun i (A : Fin M.n → ℝ) => A i) (fun i _ => measurable_pi_apply i)
  convert this using 1
  ext A
  simp [amax, Finset.sup'_apply]

theorem bestSubmission_eq_psi (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) (cp : ℝ) (A : Fin M.n → ℝ) (hA : ∀ i, A i ∈ Icc (0 : ℝ) 1) :
    bestSubmission M r cp A = psi M r cp (amax M A) := by
  have hdef : bestSubmission M r cp A =
      Finset.univ.sup' (univ_nonempty_fin M) (fun i => psi M r cp (A i)) := rfl
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' (univ_nonempty_fin M) A
  have hmax : amax M A = A i0 := hi0
  rw [hdef]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    apply psi_mono M budget r hr cp (hA i) (by rw [hmax]; exact hA i0)
    exact Finset.le_sup' A (Finset.mem_univ i)
  · rw [hmax]
    exact Finset.le_sup' (fun i => psi M r cp (A i)) (Finset.mem_univ i0)

theorem ae_profile_mem (M : AbilityModel) :
    ∀ᵐ A ∂(profileLaw M), ∀ i, A i ∈ Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have h1 : ∀ᵐ y ∂(abilityLaw M), y ∈ Icc (0 : ℝ) 1 := by
    unfold abilityLaw
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)
  exact (Measure.tendsto_eval_ae_ae (i := i)).eventually h1

theorem profile_amax_lt (M : AbilityModel) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    (profileLaw M).real {A | amax M A < y} = M.F y ^ M.n := by
  have hs : {A : Fin M.n → ℝ | amax M A < y} = Set.pi univ (fun _ => Iio y) := by
    ext A
    simp only [mem_setOf_eq, amax, Finset.sup'_lt_iff, Finset.mem_univ, true_implies,
      Set.mem_pi, mem_univ, mem_Iio]
  rw [hs, measureReal_def]
  unfold profileLaw
  rw [Measure.pi_pi]
  simp only [abilityLaw_Iio M hy, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (F_nonneg M hy)]

theorem profile_le_amax (M : AbilityModel) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    (profileLaw M).real {A | y ≤ amax M A} = 1 - M.F y ^ M.n := by
  have hs : {A : Fin M.n → ℝ | y ≤ amax M A} = {A | amax M A < y}ᶜ := by
    ext A; simp
  rw [hs, measureReal_compl (measurableSet_lt (measurable_amax M) measurable_const),
    profile_amax_lt M hy, probReal_univ]

/-- One-dimensional formula for the expected best submission. -/
theorem bestExpected_eq (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) (cp : ℝ) :
    bestExpected M r cp =
      ∫ y in Ioc (amin M r cp) 1, rho M r y * (1 - M.F y ^ M.n) := by
  have hα := amin_mem_Icc M r cp
  set α := amin M r cp with hαdef
  set ν : Measure ℝ := volume.restrict (Ioc α 1) with hν
  set ρt : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (rho M r) with hρt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_rho M r)
  have hbound : ∀ y, ‖ρt y‖ ≤ max C 0 := by
    intro y
    rw [hρt]
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hy]; exact (hC y hy).trans (le_max_left _ _)
    · rw [indicator_of_notMem hy, norm_zero]; exact le_max_right _ _
  have hρtm : AEStronglyMeasurable ρt ν := by
    have : AEStronglyMeasurable ρt volume :=
      (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
        ((continuousOn_rho M r).aestronglyMeasurable measurableSet_Icc)
    exact this.mono_measure Measure.restrict_le_self
  have hsub : Ioc α 1 ⊆ Icc (0 : ℝ) 1 := fun y hy => ⟨hα.1.trans hy.1.le, hy.2⟩
  -- the kernel
  set K : (Fin M.n → ℝ) → ℝ → ℝ := fun A y => (Iic (amax M A)).indicator ρt y with hK
  have hpsi : ∀ A : Fin M.n → ℝ, (∀ i, A i ∈ Icc (0 : ℝ) 1) →
      bestSubmission M r cp A = ∫ y, K A y ∂ν := by
    intro A hA
    obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' (univ_nonempty_fin M) A
    have hmI : amax M A ∈ Icc (0 : ℝ) 1 := by
      have : amax M A = A i0 := hi0
      rw [this]; exact hA i0
    rw [bestSubmission_eq_psi M budget r hr cp A hA, psi_eq_setIntegral M r cp _ hmI]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    simp only [hK, hρt]
    by_cases hya : y ∈ Iic (amax M A)
    · rw [indicator_of_mem hya, indicator_of_mem hya, indicator_of_mem (hsub hy)]
    · rw [indicator_of_notMem hya, indicator_of_notMem hya]
  have hS : MeasurableSet {p : (Fin M.n → ℝ) × ℝ | p.2 ≤ amax M p.1} :=
    measurableSet_le measurable_snd ((measurable_amax M).comp measurable_fst)
  have hKp : Function.uncurry K =
      {p : (Fin M.n → ℝ) × ℝ | p.2 ≤ amax M p.1}.indicator (fun p => ρt p.2) := by
    ext ⟨A, y⟩
    simp only [Function.uncurry_apply_pair, hK, indicator, mem_Iic, mem_setOf_eq]
  have hint : Integrable (Function.uncurry K) ((profileLaw M).prod ν) := by
    have hfin : IsFiniteMeasure ν := by
      rw [hν]; exact isFiniteMeasure_restrict.mpr (by simp)
    rw [hKp]
    apply Integrable.of_bound _ (max C 0)
    · exact Filter.Eventually.of_forall (fun p => (norm_indicator_le_norm_self _ _).trans
        (hbound p.2))
    · exact (hρtm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).indicator hS
  unfold bestExpected
  rw [integral_congr_ae ((ae_profile_mem M).mono (fun A hA => hpsi A hA))]
  rw [integral_integral_swap hint]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  have hyI := hsub hy
  have hKy : (fun A => K A y) =
      {A : Fin M.n → ℝ | y ≤ amax M A}.indicator (fun _ => ρt y) := by
    ext A; simp only [hK, indicator, mem_Iic, mem_setOf_eq]
  simp only
  rw [hKy, integral_indicator_const _ (measurableSet_le measurable_const (measurable_amax M)),
    profile_le_amax M hyI, smul_eq_mul, hρt, indicator_of_mem hyI]
  ring

end InnovContest.Rewards


open MeasureTheory Set

namespace InnovContest.Rewards

theorem ordCDF_succ (N k : ℕ) (hk : k ≤ N) (q : ℝ) :
    ordCDF N k q = ordCDF N (k + 1) q + (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) := by
  unfold ordCDF
  have : Finset.Icc k N = insert k (Finset.Icc (k + 1) N) := by
    ext i; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  rw [this, Finset.sum_insert (by simp)]
  ring

theorem choose_id1 (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (N.choose k : ℝ) * k = N * ((N - 1).choose (k - 1) : ℝ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h := Nat.add_one_mul_choose_eq M k'
  simp only [Nat.add_sub_cancel]
  have h' : ((M + 1 : ℕ) : ℝ) * (M.choose k' : ℝ) =
      ((M + 1).choose (k' + 1) : ℝ) * ((k' + 1 : ℕ) : ℝ) := by exact_mod_cast h
  linarith

theorem choose_id2 (N k : ℕ) (hk1 : 1 ≤ N) (hkN : k ≤ N) :
    (N.choose k : ℝ) * ((N - k : ℕ) : ℝ) = N * ((N - 1).choose k : ℝ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := Nat.choose_mul_succ_eq M k
  simp only [Nat.add_sub_cancel]
  have h' : (M.choose k : ℝ) * ((M + 1 : ℕ) : ℝ) =
      ((M + 1).choose k : ℝ) * ((M + 1 - k : ℕ) : ℝ) := by exact_mod_cast h
  linarith

/-- The derivative of the binomial tail is the order-statistic density. -/
theorem hasDerivAt_ordCDF (N : ℕ) : ∀ d k : ℕ, k + d = N → 1 ≤ k → ∀ q : ℝ,
    HasDerivAt (fun q => ordCDF N k q)
      ((N : ℝ) * ((N - 1).choose (k - 1) : ℝ) * q ^ (k - 1) * (1 - q) ^ (N - k)) q := by
  intro d
  induction d with
  | zero =>
    intro k hk hk1 q
    have hkN : k = N := by omega
    subst hkN
    have hf : (fun q => ordCDF k k q) = fun q => q ^ k := funext (ordCDF_top k)
    rw [hf]
    refine (hasDerivAt_pow k q).congr_deriv ?_
    simp
  | succ d ih =>
    intro k hk hk1 q
    have hkN : k ≤ N := by omega
    have hf : (fun q => ordCDF N k q) = fun q =>
        ordCDF N (k + 1) q + (N.choose k : ℝ) * q ^ k * (1 - q) ^ (N - k) :=
      funext (ordCDF_succ N k hkN)
    rw [hf]
    have h1 := ih (k + 1) (by omega) (by omega) q
    have ha := (hasDerivAt_pow k q).const_mul (N.choose k : ℝ)
    have hb := ((hasDerivAt_id' q).const_sub 1).pow (N - k)
    refine (h1.add (ha.mul hb)).congr_deriv ?_
    have e1 := choose_id1 N k hk1 hkN
    have e2 := choose_id2 N k (by omega) hkN
    have hpow : N - (k + 1) = N - k - 1 := by omega
    simp only [Nat.add_sub_cancel, hpow, Pi.pow_apply]
    linear_combination (q ^ (k - 1) * (1 - q) ^ (N - k)) * e1 -
      (q ^ k * (1 - q) ^ (N - k - 1)) * e2

theorem hasDerivAt_F (M : AbilityModel) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt M.F (M.f y) y := by
  have hint : IntervalIntegrable M.f volume 0 y :=
    intervalIntegrable_f M ⟨le_rfl, zero_le_one⟩ ⟨hy.1.le, hy.2.le⟩
  have hcont : ContinuousOn M.f (Ioo (0 : ℝ) 1) := M.hf.mono Ioo_subset_Icc_self
  have hmeas := hcont.stronglyMeasurableAtFilter isOpen_Ioo y hy (μ := volume)
  have hca : ContinuousAt M.f y := hcont.continuousAt (isOpen_Ioo.mem_nhds hy)
  have h := intervalIntegral.integral_hasDerivAt_right hint hmeas hca
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hy] with x hx
  exact M.hF x ⟨hx.1.le, hx.2.le⟩

theorem ordCDF_at_one (N k : ℕ) (hkN : k ≤ N) : ordCDF N k 1 = 1 := by
  unfold ordCDF
  rw [Finset.sum_eq_single N]
  · simp
  · intro i hi hiN
    rw [Finset.mem_Icc] at hi
    have : 0 < N - i := by omega
    simp [zero_pow this.ne']
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hkN, le_rfl⟩) h

theorem ordCDF_at_zero (N k : ℕ) (hk : 1 ≤ k) : ordCDF N k 0 = 0 := by
  unfold ordCDF
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Icc] at hi
  simp [zero_pow (show i ≠ 0 by omega)]

theorem F_zero (M : AbilityModel) : M.F 0 = 0 := by
  rw [M.hF 0 ⟨le_rfl, zero_le_one⟩, intervalIntegral.integral_same]

/-- Each order-statistic density integrates to one over `[0,1]`. -/
theorem integral_ordPDF (M : AbilityModel) (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∫ y in (0 : ℝ)..1, ordPDF N k M.F M.f y = 1 := by
  have hcont : ContinuousOn (fun y => ordCDF N k (M.F y)) (Icc (0 : ℝ) 1) :=
    (continuous_ordCDF N k).comp_continuousOn (continuousOn_F M)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont]
  · simp only [M.hF1, F_zero M, ordCDF_at_one N k hkN, ordCDF_at_zero N k hk1, sub_zero]
  · intro y hy
    have h := (hasDerivAt_ordCDF N (N - k) k (by omega) hk1 (M.F y)).comp y (hasDerivAt_F M hy)
    refine h.congr_deriv ?_
    unfold ordPDF; ring
  · exact intervalIntegrable_of_Icc' (continuousOn_ordPDF' M N k)
  where
    intervalIntegrable_of_Icc' {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
        IntervalIntegrable g volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rwa [uIcc_of_le zero_le_one]
    continuousOn_ordPDF' (M : AbilityModel) (N k : ℕ) :
        ContinuousOn (fun y => ordPDF N k M.F M.f y) (Icc (0 : ℝ) 1) := by
      unfold ordPDF
      have hF := continuousOn_F M
      exact ((((continuousOn_const.mul continuousOn_const).mul (hF.pow _)).mul
        ((continuousOn_const.sub hF).pow _)).mul M.hf)

end InnovContest.Rewards


open MeasureTheory Set

namespace InnovContest.Rewards

/-- The marginal value of the `j`-th reward differential with costless entry. -/
noncomputable def cval (M : AbilityModel) (j : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1, y * ordPDF (M.n - 1) (M.n - j) M.F M.f y * (1 - M.F y ^ M.n)

theorem continuousOn_w (M : AbilityModel) :
    ContinuousOn (fun y => 1 - M.F y ^ M.n) (Icc (0 : ℝ) 1) :=
  continuousOn_const.sub ((continuousOn_F M).pow _)

theorem iI01 {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    IntervalIntegrable g volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rwa [uIcc_of_le zero_le_one]

theorem bestExpected_zero (M : AbilityModel) (budget : ℝ) (r : ℕ → ℝ)
    (hr : Feasible M.n budget r) :
    bestExpected M r 0 = ∑ j ∈ Finset.Icc 1 (M.n - 1), (r j - r (j + 1)) * cval M j := by
  rw [bestExpected_eq M budget r hr 0, amin_zero M budget r hr,
    ← intervalIntegral.integral_of_le zero_le_one]
  unfold rho
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    unfold cval
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext y; ring
  · intro j _
    apply iI01
    exact (continuousOn_const.mul (continuousOn_id.mul (continuousOn_ordPDF M _ _))).mul
      (continuousOn_w M)

theorem w_mem (M : AbilityModel) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ 1 - M.F y ^ M.n ∧ 1 - M.F y ^ M.n ≤ 1 := by
  have h0 := F_nonneg M hy
  have h1 := F_le_one M hy
  constructor
  · have : M.F y ^ M.n ≤ 1 := pow_le_one₀ h0 h1
    linarith
  · have : 0 ≤ M.F y ^ M.n := pow_nonneg h0 _
    linarith

/-- `∫ (1 - F^n) g_1 = n / (2n-1)`. -/
theorem integral_w_g1 (M : AbilityModel) :
    ∫ y in (0 : ℝ)..1, ordPDF (M.n - 1) (M.n - 1) M.F M.f y * (1 - M.F y ^ M.n) =
      1 - ((M.n - 1 : ℕ) : ℝ) / ((M.n - 1 + M.n : ℕ) : ℝ) := by
  have hn2 := M.hn
  set N := M.n - 1 with hN
  have hn : M.n = N + 1 := by omega
  set G : ℝ → ℝ := fun y => M.F y ^ N - (N : ℝ) / ((N + M.n : ℕ) : ℝ) * M.F y ^ (N + M.n)
    with hG
  have hcont : ContinuousOn G (Icc (0 : ℝ) 1) := by
    have hF := continuousOn_F M
    exact (hF.pow _).sub (continuousOn_const.mul (hF.pow _))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont]
  · simp only [hG, M.hF1, F_zero M, one_pow]
    rw [zero_pow (by omega), zero_pow (by omega)]
    ring
  · intro y hy
    have hd := hasDerivAt_F M hy
    have h1 := hd.pow N
    have h2 := (hd.pow (N + M.n)).const_mul ((N : ℝ) / ((N + M.n : ℕ) : ℝ))
    refine (h1.sub h2).congr_deriv ?_
    unfold ordPDF
    have hNn : ((N + M.n : ℕ) : ℝ) ≠ 0 := by
      have : 0 < N + M.n := by omega
      exact_mod_cast this.ne'
    have e : ((N + M.n : ℕ) : ℝ) = N + M.n := by push_cast; ring
    rw [show N + M.n - 1 = (N - 1) + M.n by omega, pow_add]
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
    field_simp
  · apply iI01
    exact (continuousOn_ordPDF M _ _).mul (continuousOn_w M)

theorem kappa_mono {j : ℕ} {C q q' : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hqq : q ≤ q')
    (hq' : q' ≤ 1) :
    (j : ℝ) * q ^ (j - 1) - C * (1 - q) ^ (j - 1) ≤
      (j : ℝ) * q' ^ (j - 1) - C * (1 - q') ^ (j - 1) := by
  have h1 : q ^ (j - 1) ≤ q' ^ (j - 1) := pow_le_pow_left₀ hq hqq _
  have h2 : (1 - q') ^ (j - 1) ≤ (1 - q) ^ (j - 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  nlinarith [mul_le_mul_of_nonneg_left h1 hj, mul_le_mul_of_nonneg_left h2 hC]

/-- Single-crossing comparison. -/
theorem single_crossing {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) {y0 : ℝ}
    (hneg : ∀ y ∈ Icc (0 : ℝ) 1, y ≤ y0 → φ y ≤ 0)
    (hpos : ∀ y ∈ Icc (0 : ℝ) 1, y0 ≤ y → 0 ≤ φ y) :
    y0 * ∫ y in (0 : ℝ)..1, φ y ≤ ∫ y in (0 : ℝ)..1, y * φ y := by
  have hi1 : IntervalIntegrable φ volume 0 1 := iI01 hφ
  have hi2 : IntervalIntegrable (fun y => y * φ y) volume 0 1 := iI01 (continuousOn_id.mul hφ)
  rw [← intervalIntegral.integral_const_mul, ← sub_nonneg,
    ← intervalIntegral.integral_sub hi2 (hi1.const_mul y0)]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro y hy
  by_cases h : y ≤ y0
  · have := hneg y hy h; nlinarith
  · push_neg at h
    have := hpos y hy h.le; nlinarith

theorem cval_lt (M : AbilityModel) (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ M.n - 1) :
    cval M j < j * cval M 1 := by
  set N := M.n - 1 with hN
  set k := M.n - j with hk
  have hk1 : 1 ≤ k := by omega
  have hkN : k ≤ N := by omega
  set C : ℝ := ((N - 1).choose (k - 1) : ℝ) with hC
  have hCpos : 1 ≤ C := by
    have := Nat.choose_pos (show k - 1 ≤ N - 1 by omega)
    rw [hC]; exact_mod_cast this
  set g1 : ℝ → ℝ := fun y => ordPDF N N M.F M.f y with hg1
  set gj : ℝ → ℝ := fun y => ordPDF N k M.F M.f y with hgj
  set w : ℝ → ℝ := fun y => 1 - M.F y ^ M.n with hw
  set φ : ℝ → ℝ := fun y => w y * ((j : ℝ) * g1 y - gj y) with hφ
  have hφc : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    (continuousOn_w M).mul ((continuousOn_const.mul (continuousOn_ordPDF M _ _)).sub
      (continuousOn_ordPDF M _ _))
  -- factorization of `φ`
  set κ : ℝ → ℝ := fun q => (j : ℝ) * q ^ (j - 1) - C * (1 - q) ^ (j - 1) with hκ
  have hfac : ∀ y, φ y = w y * (M.f y * (N * M.F y ^ (k - 1))) * κ (M.F y) := by
    intro y
    have e2 : N - k = j - 1 := by omega
    have hsplit : M.F y ^ (N - 1) = M.F y ^ (k - 1) * M.F y ^ (j - 1) := by
      rw [← pow_add]; congr 1; omega
    simp only [hφ, hg1, hgj, hκ, ordPDF, Nat.sub_self, Nat.choose_self, pow_zero, Nat.cast_one,
      mul_one]
    rw [e2, hsplit, hC]
    ring
  have hκc : ContinuousOn (fun y => κ (M.F y)) (Icc (0 : ℝ) 1) := by
    simp only [hκ]
    have hF := continuousOn_F M
    exact (continuousOn_const.mul (hF.pow _)).sub
      (continuousOn_const.mul ((continuousOn_const.sub hF).pow _))
  have hκ0 : κ (M.F 0) = -C := by
    simp only [hκ, F_zero M]
    rw [zero_pow (by omega)]; simp
  have hκ1 : κ (M.F 1) = j := by
    simp only [hκ, M.hF1]
    rw [sub_self, zero_pow (by omega)]; simp
  obtain ⟨y0, hy0I, hy0⟩ : ∃ y0 ∈ Icc (0 : ℝ) 1, κ (M.F y0) = 0 := by
    have := intermediate_value_Icc (zero_le_one' ℝ) hκc
    have hmem : (0 : ℝ) ∈ Icc (κ (M.F 0)) (κ (M.F 1)) := by
      rw [hκ0, hκ1]; constructor <;> [linarith; positivity]
    exact this hmem
  have hy0pos : 0 < y0 := by
    rcases eq_or_lt_of_le hy0I.1 with h | h
    · rw [← h, hκ0] at hy0; linarith
    · exact h
  have hpre : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ w y * (M.f y * (N * M.F y ^ (k - 1))) := by
    intro y hy
    have := (w_mem M hy).1
    have := (M.hpos y hy).le
    have := pow_nonneg (F_nonneg M hy) (k - 1)
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    positivity
  have hneg : ∀ y ∈ Icc (0 : ℝ) 1, y ≤ y0 → φ y ≤ 0 := by
    intro y hy hyy
    rw [hfac]
    have : κ (M.F y) ≤ 0 := by
      rw [← hy0]
      exact kappa_mono (by linarith) (F_nonneg M hy) (F_mono M hy hy0I hyy) (F_le_one M hy0I)
    exact mul_nonpos_of_nonneg_of_nonpos (hpre y hy) this
  have hpos : ∀ y ∈ Icc (0 : ℝ) 1, y0 ≤ y → 0 ≤ φ y := by
    intro y hy hyy
    rw [hfac]
    have : 0 ≤ κ (M.F y) := by
      rw [← hy0]
      exact kappa_mono (by linarith) (F_nonneg M hy0I) (F_mono M hy0I hy hyy) (F_le_one M hy)
    exact mul_nonneg (hpre y hy) this
  have hsc := single_crossing hφc hneg hpos
  -- `∫ φ > 0`
  have hig1 : IntervalIntegrable (fun y => g1 y * w y) volume 0 1 :=
    iI01 ((continuousOn_ordPDF M _ _).mul (continuousOn_w M))
  have higj : IntervalIntegrable (fun y => gj y * w y) volume 0 1 :=
    iI01 ((continuousOn_ordPDF M _ _).mul (continuousOn_w M))
  have hint_phi : ∫ y in (0 : ℝ)..1, φ y =
      j * (∫ y in (0 : ℝ)..1, g1 y * w y) - ∫ y in (0 : ℝ)..1, gj y * w y := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hig1.const_mul _) higj]
    congr 1; ext y; simp only [hφ]; ring
  have hg1w : ∫ y in (0 : ℝ)..1, g1 y * w y = 1 - (N : ℝ) / ((N + M.n : ℕ) : ℝ) := by
    simp only [hg1, hw]; exact integral_w_g1 M
  have hgjw : ∫ y in (0 : ℝ)..1, gj y * w y ≤ 1 := by
    refine le_trans ?_ (integral_ordPDF M N k hk1 hkN).le
    apply intervalIntegral.integral_mono_on zero_le_one higj
      (iI01 (continuousOn_ordPDF M N k))
    intro y hy
    have h0 := ordPDF_nonneg M N k hy
    have := (w_mem M hy).2
    simp only [hgj, hw]
    nlinarith
  have hfrac : (N : ℝ) / ((N + M.n : ℕ) : ℝ) < 1 / 2 := by
    have hpos' : (0 : ℝ) < ((N + M.n : ℕ) : ℝ) := by
      have : 0 < N + M.n := by omega
      exact_mod_cast this
    rw [div_lt_iff₀ hpos']
    have : ((N + M.n : ℕ) : ℝ) = N + M.n := by push_cast; ring
    rw [this]
    have : (M.n : ℝ) = N + 1 := by
      have : M.n = N + 1 := by omega
      rw [this]; push_cast; ring
    rw [this]; linarith
  have hj2' : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hphipos : 0 < ∫ y in (0 : ℝ)..1, φ y := by
    rw [hint_phi, hg1w]
    nlinarith
  -- conclude
  have hlin : ∫ y in (0 : ℝ)..1, y * φ y = j * cval M 1 - cval M j := by
    unfold cval
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · congr 1; ext y; simp only [hφ, hg1, hgj, hw]
      rw [show M.n - 1 = N from rfl, show M.n - j = k from rfl]; ring
    · exact (iI01 ((continuousOn_id.mul (continuousOn_ordPDF M _ _)).mul
        (continuousOn_w M))).const_mul _
    · exact iI01 ((continuousOn_id.mul (continuousOn_ordPDF M _ _)).mul (continuousOn_w M))
  have := mul_pos hy0pos hphipos
  linarith

theorem cval_one_pos (M : AbilityModel) : 0 < cval M 1 := by
  unfold cval
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ zero_lt_one
  · exact iI01 ((continuousOn_id.mul (continuousOn_ordPDF M _ _)).mul (continuousOn_w M))
  · intro y hy
    have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hFy : 0 < M.F y := by
      have := F_strictMono M ⟨le_rfl, zero_le_one⟩ hyI hy.1
      rwa [F_zero M] at this
    have hFy1 : M.F y < 1 := by
      have := F_strictMono M hyI ⟨zero_le_one, le_rfl⟩ hy.2
      rwa [M.hF1] at this
    have hw : 0 < 1 - M.F y ^ M.n := by
      have : M.F y ^ M.n < 1 := pow_lt_one₀ hFy.le hFy1 (by have := M.hn; omega)
      linarith
    have hg : 0 < ordPDF (M.n - 1) (M.n - 1) M.F M.f y := by
      unfold ordPDF
      have hN : (0 : ℝ) < ((M.n - 1 : ℕ) : ℝ) := by
        have : 0 < M.n - 1 := by have := M.hn; omega
        exact_mod_cast this
      have := M.hpos y hyI
      have := Nat.choose_pos (le_refl (M.n - 1 - 1))
      have hc : (0 : ℝ) < ((M.n - 1 - 1).choose (M.n - 1 - 1) : ℝ) := by exact_mod_cast this
      have : 0 < 1 - M.F y := by linarith
      positivity
    have := hy.1
    positivity

end InnovContest.Rewards


open MeasureTheory Set

namespace InnovContest.Rewards

theorem bestExpected_zero_wta (M : AbilityModel) (budget : ℝ) (hb : 0 ≤ budget) :
    bestExpected M (equalSplit budget 1) 0 = budget * cval M 1 := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  rw [bestExpected_zero M budget _ (equalSplit_feasible M.n budget hb 1 le_rfl hn1)]
  rw [Finset.sum_eq_single 1]
  · simp [equalSplit]
  · intro j hj hj1
    rw [Finset.mem_Icc] at hj
    have : equalSplit budget 1 j - equalSplit budget 1 (j + 1) = 0 := by
      unfold equalSplit; rw [if_neg (by omega), if_neg (by omega)]; ring
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by have := M.hn; omega⟩) h

/-- Feasible allocations with no differentials at ranks `2,…,n` and full budget are WTA. -/
theorem eq_wta_of (n : ℕ) (hn : 2 ≤ n) (budget : ℝ) (r : ℕ → ℝ) (hr : Feasible n budget r)
    (hδ : ∀ j, 2 ≤ j → j ≤ n → r j - r (j + 1) = 0)
    (hT : ∑ j ∈ Finset.Icc 1 n, r j = budget) : r = equalSplit budget 1 := by
  have hz : ∀ d, d ≤ n - 1 → r (n + 1 - d) = 0 := by
    intro d
    induction d with
    | zero => intro _; exact hr.2.2.1 (n + 1) (by omega)
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hδ (n + 1 - (d + 1)) (by omega) (by omega)
      have : n + 1 - (d + 1) + 1 = n + 1 - d := by omega
      rw [this, h1] at h2
      linarith
  have hz2 : ∀ j, 2 ≤ j → r j = 0 := by
    intro j hj
    by_cases hjn : n < j
    · exact hr.2.2.1 j hjn
    · have := hz (n + 1 - j) (by omega)
      rwa [show n + 1 - (n + 1 - j) = j by omega] at this
  have hr1 : r 1 = budget := by
    rw [← hT]
    rw [Finset.sum_eq_single 1]
    · intro j hj hj1
      rw [Finset.mem_Icc] at hj
      exact hz2 j (by omega)
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) h
  funext j
  unfold equalSplit
  rcases Nat.lt_or_ge j 2 with h | h
  · interval_cases j
    · rw [if_neg (by omega)]; exact hr.1
    · rw [if_pos ⟨le_rfl, le_rfl⟩, hr1]; simp
  · rw [if_neg (by omega)]; exact hz2 j h

end InnovContest.Rewards

open InnovContest.Rewards in
theorem solution (M : AbilityModel) (budget : ℝ) (hbudget : 0 < budget)
    (r : ℕ → ℝ) (hr : Feasible M.n budget r) (hne : r ≠ equalSplit budget 1) :
    bestExpected M r 0 < bestExpected M (equalSplit budget 1) 0 := by
  have hn2 := M.hn
  set n := M.n with hndef
  rw [bestExpected_zero_wta M budget hbudget.le, bestExpected_zero M budget r hr]
  set δ : ℕ → ℝ := fun j => r j - r (j + 1) with hδdef
  have hδ0 : ∀ j ∈ Finset.Icc 1 n, 0 ≤ δ j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have := feasible_antitone n budget r hr hj.1 (Nat.le_succ j) (by omega)
    simp only [hδdef]; linarith
  set c1 := cval M 1 with hc1
  have hc1pos : 0 < c1 := cval_one_pos M
  set T := ∑ j ∈ Finset.Icc 1 n, r j with hTdef
  have hTB : T ≤ budget := hr.2.2.2.2
  have habel : ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * δ j = T := by
    rw [abel_sum, hr.2.2.1 (n + 1) (by omega)]; ring
  have hsplit : ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * δ j =
      ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) * δ j + n * δ n := by
    have : n = n - 1 + 1 := by omega
    conv_lhs => rw [this]
    rw [Finset.sum_Icc_succ_top (by omega), ← this]
  -- the gap decomposition
  have hgap : budget * c1 - ∑ j ∈ Finset.Icc 1 (n - 1), δ j * cval M j =
      ∑ j ∈ Finset.Icc 1 (n - 1), δ j * ((j : ℝ) * c1 - cval M j) +
        c1 * (n * δ n) + c1 * (budget - T) := by
    have : ∑ j ∈ Finset.Icc 1 (n - 1), δ j * ((j : ℝ) * c1 - cval M j) =
        c1 * ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) * δ j -
          ∑ j ∈ Finset.Icc 1 (n - 1), δ j * cval M j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this]
    have h2 : ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℝ) * δ j = T - n * δ n := by
      linarith [hsplit, habel]
    rw [h2]; ring
  have hterm : ∀ j ∈ Finset.Icc 1 (n - 1), 0 ≤ δ j * ((j : ℝ) * c1 - cval M j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply mul_nonneg (hδ0 j (Finset.mem_Icc.mpr ⟨hj.1, by omega⟩))
    rcases eq_or_lt_of_le hj.1 with h | h
    · rw [← h, hc1]; simp
    · linarith [cval_lt M j (by omega) hj.2]
  have hδn : 0 ≤ δ n := hδ0 n (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hS := Finset.sum_nonneg hterm
  by_contra hcon
  push_neg at hcon
  have hzero : ∑ j ∈ Finset.Icc 1 (n - 1), δ j * ((j : ℝ) * c1 - cval M j) +
      c1 * (n * δ n) + c1 * (budget - T) = 0 := by
    have h1 : 0 ≤ c1 * (n * δ n) := by positivity
    have h2 : 0 ≤ c1 * (budget - T) := mul_nonneg hc1pos.le (by linarith)
    linarith
  have hS0 : ∑ j ∈ Finset.Icc 1 (n - 1), δ j * ((j : ℝ) * c1 - cval M j) = 0 := by
    have h1 : 0 ≤ c1 * (n * δ n) := by positivity
    have h2 : 0 ≤ c1 * (budget - T) := mul_nonneg hc1pos.le (by linarith)
    linarith
  have hn0 : c1 * (n * δ n) = 0 := by
    have h1 : 0 ≤ c1 * (n * δ n) := by positivity
    have h2 : 0 ≤ c1 * (budget - T) := mul_nonneg hc1pos.le (by linarith)
    linarith
  have hT0 : c1 * (budget - T) = 0 := by linarith
  have hδn0 : δ n = 0 := by
    have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rcases mul_eq_zero.mp hn0 with h | h
    · linarith
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hn0'
      · exact h'
  have hTeq : T = budget := by
    rcases mul_eq_zero.mp hT0 with h | h
    · linarith
    · linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hS0
  apply hne
  apply eq_wta_of n hn2 budget r hr _ hTeq
  intro j hj2 hjn
  rcases eq_or_lt_of_le hjn with h | h
  · rw [h]; exact hδn0
  · have hj := hall j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hlt := cval_lt M j hj2 (by omega)
    rcases mul_eq_zero.mp hj with h' | h'
    · exact h'
    · linarith
