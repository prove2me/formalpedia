-- Prove2me | solution 1 for InnovContest.Rewards.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:59:13.014505+00:00
-- url     : https://prove2.me/submissions/e108f074-c5b9-4dd4-8964-da06f4630aae

import Mathlib
import Definitions.Def_InnovContest_Rewards_Model
import Theorems.Thm_InnovContest_Rewards_existence
import Theorems.Thm_InnovContest_Rewards_first_term_wta
import Theorems.Thm_InnovContest_Rewards_theorem_1
import Theorems.Thm_InnovContest_Rewards_first_term_wta_zero
import Theorems.Thm_InnovContest_Rewards_wta_optimal_small_cf
import Theorems.Thm_InnovContest_Rewards_numRewards_le_mstarP
import Theorems.Thm_InnovContest_Rewards_participation_threshold

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

/-- Part (i) of Theorem 2. -/
theorem part_one (M : AbilityModel) (budget cf : ℝ) (hb : 0 < budget) (hcf : 0 ≤ cf) :
    (∃ r : ℕ → ℝ, IsOptimal M budget 0 cf r) ∧
      (∀ r : ℕ → ℝ, IsOptimal M budget 0 cf r → numRewards M.n r = 1) := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  refine ⟨existence M budget 0 cf hb le_rfl hcf, ?_⟩
  intro r hopt
  have hW := equalSplit_feasible M.n budget hb.le 1 le_rfl hn1
  by_cases hrW : r = equalSplit budget 1
  · rw [hrW]; exact numRewards_wta M.n hn1 budget hb
  exfalso
  have h1 := hopt.2 _ hW
  have h2 := first_term_wta_zero M budget hb r hopt.1 hrW
  unfold firmObjective at h1
  rw [failProb_zero M budget r hopt.1, failProb_zero M budget _ hW] at h1
  linarith

/-- Part (ii) of Theorem 2 for a fixed budget. -/
theorem part_two_budget (M : AbilityModel) (cp cpHat budget : ℝ) (hcp : 0 < cp)
    (hbudget : cp < budget) (hupper : budget < (M.n : ℝ) * cp)
    (hthr : (budget < cpHat → ∀ m ∈ Finset.Icc 1 M.n,
          amin M (equalSplit budget 1) cp ≤ amin M (equalSplit budget m) cp) ∧
        (cpHat < budget →
          amin M (equalSplit budget (mstarP M budget cp)) cp <
            amin M (equalSplit budget 1) cp)) :
    ∃ cfHat : ℝ, 0 < cfHat ∧
      ∀ cf : ℝ, 0 ≤ cf →
        (∃ r : ℕ → ℝ, IsOptimal M budget cp cf r) ∧
        ((budget < cpHat ∨ cf < cfHat) →
          ∀ r : ℕ → ℝ, IsOptimal M budget cp cf r → numRewards M.n r = 1) ∧
        ((cpHat < budget ∧ cfHat < cf) →
          ∀ r : ℕ → ℝ, IsOptimal M budget cp cf r →
            2 ≤ numRewards M.n r ∧ numRewards M.n r ≤ mstarP M budget cp) := by
  have hn1 : 1 ≤ M.n := le_trans (by norm_num) M.hn
  have hb0 : 0 < budget := by linarith
  set W := equalSplit budget 1 with hWdef
  have hW : Feasible M.n budget W := equalSplit_feasible M.n budget hb0.le 1 le_rfl hn1
  have hnumW : numRewards M.n W = 1 := numRewards_wta M.n hn1 budget hb0
  have hG : ∀ r, Feasible M.n budget r → r ≠ W →
      bestExpected M r cp < bestExpected M W cp :=
    fun r hr hne => first_term_wta M budget cp hcp hbudget hupper r hr hne
  have hex : ∀ cf, 0 ≤ cf → ∃ r : ℕ → ℝ, IsOptimal M budget cp cf r :=
    fun cf hcf => existence M budget cp cf hb0 hcp.le hcf
  obtain ⟨h1ms, _, hfeasms, hminms⟩ := theorem_1 M budget cp hcp hbudget hupper
  -- uniqueness of the optimum when winner-take-all strictly beats every other allocation
  have huniq : ∀ cf, (∀ r, Feasible M.n budget r → r ≠ W →
      firmObjective M r cp cf < firmObjective M W cp cf) →
      ∀ r, IsOptimal M budget cp cf r → numRewards M.n r = 1 := by
    intro cf hlt r hopt
    by_cases hrW : r = W
    · rw [hrW]; exact hnumW
    · exact absurd (hopt.2 W hW) (not_le.mpr (hlt r hopt.1 hrW))
  by_cases hcase : ∀ m ∈ Finset.Icc 1 M.n,
      amin M (equalSplit budget 1) cp ≤ amin M (equalSplit budget m) cp
  · -- winner-take-all maximizes participation, hence is the unique optimum for every `cf`
    have hpart : ∀ r, Feasible M.n budget r →
        failProb M W cp ≤ failProb M r cp := by
      intro r hr
      apply failProb_mono
      exact (hcase _ (mstarP_spec M budget cp).1).trans (hminms r hr)
    refine ⟨1, one_pos, fun cf hcf => ⟨hex cf hcf, fun _ => ?_, fun h => ?_⟩⟩
    · exact huniq cf (fun r hr hne => objective_lt_wta M budget cp cf hcf r
        (hG r hr hne) (hpart r hr))
    · exact absurd (hcase _ (mstarP_spec M budget cp).1) (not_le.mpr (hthr.2 h.1))
  have hnotlt : ¬ budget < cpHat := fun h => hcase (hthr.1 h)
  have hstrict : amin M (equalSplit budget (mstarP M budget cp)) cp <
      amin M (equalSplit budget 1) cp := by
    push_neg at hcase
    obtain ⟨m, hm, hlt⟩ := hcase
    exact lt_of_le_of_lt ((mstarP_spec M budget cp).2 m hm) hlt
  obtain ⟨c, hc0, hcopt⟩ := wta_optimal_small_cf M budget cp hcp hbudget hupper
  set N : Set ℝ := {cf : ℝ | 0 ≤ cf ∧ ¬ IsOptimal M budget cp cf W} with hN
  set s := equalSplit budget (mstarP M budget cp) with hs
  have hDs : failProb M s cp < failProb M W cp :=
    failProb_strictMono M s W cp hstrict
  have hNne : N.Nonempty := by
    set D := failProb M W cp - failProb M s cp with hD
    set G := bestExpected M W cp - bestExpected M s cp with hGdef
    have hDpos : 0 < D := by rw [hD]; linarith
    refine ⟨|G| / D + 1, by positivity, ?_⟩
    intro hopt
    have h1 := hopt.2 s hfeasms
    unfold firmObjective at h1
    have h2 : (|G| / D + 1) * D = |G| + D := by field_simp
    have h3 : G ≤ |G| := le_abs_self G
    nlinarith
  have hNlb : ∀ x ∈ N, c < x := by
    intro x hx
    by_contra hle
    push_neg at hle
    exact hx.2 (hcopt x hx.1 hle)
  have hbdd : BddBelow N := ⟨0, fun x hx => hx.1⟩
  have hcfHat : c ≤ sInf N := le_csInf hNne (fun x hx => (hNlb x hx).le)
  refine ⟨sInf N, lt_of_lt_of_le hc0 hcfHat, fun cf hcf => ⟨hex cf hcf, ?_, ?_⟩⟩
  · rintro (hlt | hlt)
    · exact absurd hlt hnotlt
    -- below the threshold: winner-take-all is optimal at a slightly larger cost
    set cf' := (cf + sInf N) / 2 with hcf'
    have hcf'lt : cf' < sInf N := by rw [hcf']; linarith
    have hopt' : IsOptimal M budget cp cf' W := by
      by_contra hno
      have hmem : cf' ∈ N := ⟨by rw [hcf']; linarith, hno⟩
      exact absurd (csInf_le hbdd hmem) (not_le.mpr hcf'lt)
    apply huniq cf
    intro r hr hne
    have h1 := hopt'.2 r hr
    have h2 := hG r hr hne
    unfold firmObjective at h1 ⊢
    by_cases hDr : failProb M r cp ≤ failProb M W cp
    · have hcc : cf ≤ cf' := by rw [hcf']; linarith
      nlinarith [mul_le_mul_of_nonneg_right hcc (sub_nonneg.mpr hDr)]
    · push_neg at hDr
      nlinarith [mul_le_mul_of_nonneg_left hDr.le hcf]
  · rintro ⟨_, hlt⟩ r hopt
    obtain ⟨cf0, hcf0N, hcf0lt⟩ := exists_lt_of_csInf_lt hNne hlt
    have hnot := hcf0N.2
    unfold IsOptimal at hnot
    push_neg at hnot
    obtain ⟨s', hs', hbetter⟩ := hnot hW
    -- winner-take-all is beaten at `cf0`, hence also at `cf`
    have hbeat : firmObjective M W cp cf < firmObjective M s' cp cf := by
      have hs'W : s' ≠ W := by
        intro h; rw [h] at hbetter; exact lt_irrefl _ hbetter
      have hG' := hG s' hs' hs'W
      unfold firmObjective at hbetter ⊢
      have hDpos : failProb M s' cp < failProb M W cp := by
        by_contra hle
        push_neg at hle
        nlinarith [mul_le_mul_of_nonneg_left hle hcf0N.1]
      nlinarith [mul_lt_mul_of_pos_right hcf0lt (sub_pos.mpr hDpos)]
    refine ⟨?_, numRewards_le_mstarP M budget cp cf hcp hbudget hupper hcf r hopt⟩
    by_contra hlt2
    push_neg at hlt2
    have hle1 : numRewards M.n r ≤ 1 := by omega
    have hDr := failProb_mono M W r cp (amin_wta_le_single M budget cp r hopt.1 hle1)
    by_cases hrW : r = W
    · rw [hrW] at hopt
      exact absurd (hopt.2 s' hs') (not_le.mpr hbeat)
    · have := objective_lt_wta M budget cp cf hcf r (hG r hopt.1 hrW) hDr
      exact absurd (hopt.2 W hW) (not_le.mpr this)

end InnovContest.Rewards

open InnovContest.Rewards in
theorem solution (M : AbilityModel) :
    (∀ (budget cf : ℝ), 0 < budget → 0 ≤ cf →
      (∃ r : ℕ → ℝ, IsOptimal M budget 0 cf r) ∧
      (∀ r : ℕ → ℝ, IsOptimal M budget 0 cf r → numRewards M.n r = 1)) ∧
    (∀ cp : ℝ, 0 < cp →
      ∃ cpHat : ℝ, cp < cpHat ∧
        ∀ budget : ℝ, cp < budget → budget < (M.n : ℝ) * cp →
          ∃ cfHat : ℝ, 0 < cfHat ∧
            ∀ cf : ℝ, 0 ≤ cf →
              (∃ r : ℕ → ℝ, IsOptimal M budget cp cf r) ∧
              ((budget < cpHat ∨ cf < cfHat) →
                ∀ r : ℕ → ℝ, IsOptimal M budget cp cf r → numRewards M.n r = 1) ∧
              ((cpHat < budget ∧ cfHat < cf) →
                ∀ r : ℕ → ℝ, IsOptimal M budget cp cf r →
                  2 ≤ numRewards M.n r ∧ numRewards M.n r ≤ mstarP M budget cp)) := by
  refine ⟨fun budget cf hb hcf => part_one M budget cf hb hcf, fun cp hcp => ?_⟩
  obtain ⟨cpHat, hcpHat, hthr⟩ := participation_threshold M cp hcp
  exact ⟨cpHat, hcpHat, fun budget hb hu =>
    part_two_budget M cp cpHat budget hcp hb hu (hthr budget hb hu)⟩
