-- Prove2me | solution 1 for LargeBSP.Homog.eq_A4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:21:32.795072+00:00
-- url     : https://prove2.me/submissions/4733beea-9131-43ea-b5d4-e27841bfc273

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false


namespace BSPAux
open LargeBSP.Homog

/-- `ahead x j i`: item `j` is ranked ahead of item `i`. -/
abbrev ahead (x : ℕ → ℝ) (j i : ℕ) : Prop := x i < x j ∨ (x j = x i ∧ j < i)

lemma ahead_trans {x : ℕ → ℝ} {i j k : ℕ} (h1 : ahead x k j) (h2 : ahead x j i) : ahead x k i := by
  unfold ahead at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, by omega⟩

lemma not_ahead_self (x : ℕ → ℝ) (i : ℕ) : ¬ ahead x i i := by
  unfold ahead; rintro (h | ⟨_, h⟩) <;> [exact lt_irrefl _ h; exact lt_irrefl _ h]

lemma ahead_total (x : ℕ → ℝ) {i j : ℕ} (h : i ≠ j) : ahead x i j ∨ ahead x j i := by
  unfold ahead
  rcases lt_trichotomy (x i) (x j) with h1 | h1 | h1
  · right; left; exact h1
  · rcases lt_or_gt_of_ne h with h2 | h2
    · left; right; exact ⟨h1, h2⟩
    · right; right; exact ⟨h1.symm, h2⟩
  · left; left; exact h1

lemma rank_eq (x : ℕ → ℝ) (N i : ℕ) :
    rank x N i = ((Finset.range N).filter (fun j => ahead x j i)).card := rfl

lemma rank_lt_rank {x : ℕ → ℝ} {N i j : ℕ} (hj : j < N) (h : ahead x j i) :
    rank x N j < rank x N i := by
  classical
  rw [rank_eq, rank_eq]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, ?_, ?_⟩
    · simp [hj, h]
    · simp [not_ahead_self]
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, ahead_trans hk.2 h⟩

lemma rank_lt_N {x : ℕ → ℝ} {N i : ℕ} (hi : i < N) : rank x N i < N := by
  classical
  rw [rank_eq]
  calc ((Finset.range N).filter (fun j => ahead x j i)).card < (Finset.range N).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨i, by simp [hi], by simp [not_ahead_self]⟩
    _ = N := Finset.card_range N

lemma rank_injOn (x : ℕ → ℝ) (N : ℕ) : Set.InjOn (rank x N) (Finset.range N : Set ℕ) := by
  intro i hi j hj hij
  by_contra hne
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases ahead_total x hne with h | h
  · have := rank_lt_rank (N := N) hi h; omega
  · have := rank_lt_rank (N := N) hj h; omega

lemma image_rank (x : ℕ → ℝ) (N : ℕ) : (Finset.range N).image (rank x N) = Finset.range N := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    simp only [Finset.mem_image, Finset.mem_range] at hr ⊢
    obtain ⟨i, hi, rfl⟩ := hr
    exact rank_lt_N hi
  · rw [Finset.card_image_of_injOn (rank_injOn x N)]

lemma card_topSet (x : ℕ → ℝ) (N n : ℕ) : (topSet x N n).card = min n N := by
  classical
  have h1 : (topSet x N n).card = ((topSet x N n).image (rank x N)).card := by
    rw [Finset.card_image_of_injOn]
    intro i hi j hj hij
    exact rank_injOn x N (by simpa [topSet] using (Finset.mem_filter.1 hi).1)
      (by simpa [topSet] using (Finset.mem_filter.1 hj).1) hij
  have h2 : (topSet x N n).image (rank x N) = (Finset.range N).filter (· < n) := by
    have := Finset.filter_image (f := rank x N) (s := Finset.range N) (p := (· < n))
    rw [image_rank] at this
    rw [this]; rfl
  rw [h1, h2]
  have h3 : (Finset.range N).filter (· < n) = Finset.range (min n N) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h3, Finset.card_range]

lemma mem_topSet {x : ℕ → ℝ} {N n i : ℕ} : i ∈ topSet x N n ↔ i < N ∧ rank x N i < n := by
  simp [topSet]

/-- Items in the top set have valuation at least that of items outside it. -/
lemma le_of_top_nontop {x : ℕ → ℝ} {N n i j : ℕ} (hi : i ∈ topSet x N n) (hj : j < N)
    (hj' : j ∉ topSet x N n) : x j ≤ x i := by
  rw [mem_topSet] at hi hj'
  by_contra h
  push Not at h
  have := rank_lt_rank (N := N) hj (Or.inl h)
  have : ¬ rank x N j < n := fun h' => hj' ⟨hj, h'⟩
  omega

lemma topSet_subset_range (x : ℕ → ℝ) (N n : ℕ) : topSet x N n ⊆ Finset.range N :=
  Finset.filter_subset _ _

lemma topSet_zero (x : ℕ → ℝ) (N : ℕ) : topSet x N 0 = ∅ := by
  ext i; simp [topSet]

lemma topSet_of_le (x : ℕ → ℝ) {N n : ℕ} (h : N ≤ n) : topSet x N n = Finset.range N := by
  ext i; simp only [topSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h' => h'.1
  · intro hi; exact ⟨hi, lt_of_lt_of_le (rank_lt_N hi) h⟩

lemma V_zero (x : ℕ → ℝ) (N : ℕ) : V x N 0 = 0 := by
  simp [V, topSet_zero]

lemma cost_const (c : ℝ) (x : ℕ → ℝ) (N n : ℕ) : cost (fun _ => c) x N n = (min n N : ℕ) * c := by
  simp [cost, card_topSet]

/-- Pathwise upper bound: `V_N(m) ≤ m y + Σ (x_i - y)^+`. -/
lemma V_le (x : ℕ → ℝ) (N m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    V x N m ≤ m * y + ∑ i ∈ Finset.range N, max (x i - y) 0 := by
  unfold V
  have h1 : ∑ i ∈ topSet x N m, x i ≤ ∑ i ∈ topSet x N m, (y + max (x i - y) 0) := by
    apply Finset.sum_le_sum; intro i _; have := le_max_left (x i - y) 0; linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, card_topSet, nsmul_eq_mul] at h1
  have h2 : ∑ i ∈ topSet x N m, max (x i - y) 0 ≤ ∑ i ∈ Finset.range N, max (x i - y) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (topSet_subset_range x N m)
      (fun i _ _ => le_max_right _ _)
  have h3 : ((min m N : ℕ) : ℝ) * y ≤ m * y := by
    apply mul_le_mul_of_nonneg_right _ hy
    exact_mod_cast min_le_left m N
  linarith

/-- If at most `m` items exceed `M`, every item outside the top-`m` set is `≤ M`. -/
lemma nontop_le {x : ℕ → ℝ} {N m : ℕ} (hm : m ≤ N) {M : ℝ}
    (hK : ((Finset.range N).filter (fun i => M < x i)).card ≤ m) {j : ℕ} (hj : j < N)
    (hj' : j ∉ topSet x N m) : x j ≤ M := by
  classical
  by_contra h
  push Not at h
  have hsub : insert j (topSet x N m) ⊆ (Finset.range N).filter (fun i => M < x i) := by
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · simp [hj, h]
    · have := le_of_top_nontop hi hj hj'
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨(mem_topSet.1 hi).1, by linarith⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hj', card_topSet, min_eq_left hm] at this
  omega

/-- Pathwise exact representation: `V_N(m) = m y + Σ (x_i - y)^+` for some `y ∈ [0, M]`. -/
lemma V_eq_exists {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) {N m : ℕ} (hm : m ≤ N) {M : ℝ} (hM : 0 ≤ M)
    (hK : ((Finset.range N).filter (fun i => M < x i)).card ≤ m) :
    ∃ y ∈ Set.Icc (0 : ℝ) M, V x N m = m * y + ∑ i ∈ Finset.range N, max (x i - y) 0 := by
  classical
  set T := topSet x N m with hT
  -- choose y
  obtain ⟨y, hy0, hyM, hyT, hyN⟩ : ∃ y : ℝ, 0 ≤ y ∧ y ≤ M ∧ (∀ i ∈ T, y ≤ x i) ∧
      (∀ j, j < N → j ∉ T → x j ≤ y) := by
    by_cases hne : T.Nonempty
    · refine ⟨min M (T.inf' hne x), le_min hM ?_, min_le_left _ _, ?_, ?_⟩
      · rw [Finset.le_inf'_iff]; intro i _; exact hx i
      · intro i hi; exact le_trans (min_le_right _ _) (Finset.inf'_le _ hi)
      · intro j hj hj'
        apply le_min (nontop_le hm hK hj hj')
        rw [Finset.le_inf'_iff]; intro i hi; exact le_of_top_nontop hi hj hj'
    · refine ⟨M, hM, le_rfl, ?_, ?_⟩
      · intro i hi; exact absurd ⟨i, hi⟩ hne
      · intro j hj hj'; exact nontop_le hm hK hj hj'
  refine ⟨y, ⟨hy0, hyM⟩, ?_⟩
  have hsplit : ∑ i ∈ Finset.range N, max (x i - y) 0 = ∑ i ∈ T, (x i - y) := by
    rw [← Finset.sum_subset (topSet_subset_range x N m)]
    · apply Finset.sum_congr rfl; intro i hi; exact max_eq_left (by linarith [hyT i hi])
    · intro j hj hj'
      exact max_eq_right (by linarith [hyN j (Finset.mem_range.1 hj) hj'])
  rw [hsplit, Finset.sum_sub_distrib, Finset.sum_const, hT, card_topSet, min_eq_left hm,
    nsmul_eq_mul]
  simp [V, hT]

end BSPAux




namespace BSPAux
open LargeBSP.Homog

section Quantile
variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma cdf_eq_zero_of_neg (hν0 : ν (Set.Iio 0) = 0) {y : ℝ} (hy : y < 0) : cdf ν y = 0 := by
  have h1 := ofReal_cdf ν y
  have : ν (Set.Iic y) = 0 := measure_mono_null (Set.Iic_subset_Iio.2 hy) hν0
  rw [this] at h1
  have := cdf_nonneg ν y
  have := ENNReal.ofReal_eq_zero.1 h1
  linarith

lemma qset_nonempty {u : ℝ} (hu : u < 1) : {y : ℝ | 0 ≤ y ∧ u ≤ cdf ν y}.Nonempty := by
  have h := (tendsto_cdf_atTop ν).eventually_const_lt hu
  obtain ⟨y, hy⟩ := (h.and (eventually_ge_atTop 0)).exists
  exact ⟨y, hy.2, hy.1.le⟩

lemma qset_bdd (u : ℝ) : BddBelow {y : ℝ | 0 ≤ y ∧ u ≤ cdf ν y} := ⟨0, fun y hy => hy.1⟩

lemma quantile_nonneg (F : ℝ → ℝ) (u : ℝ) : 0 ≤ quantile F u :=
  Real.sInf_nonneg (fun y hy => hy.1)

lemma le_cdf_quantile {u : ℝ} (hu1 : u < 1) : u ≤ cdf ν (quantile (cdf ν) u) := by
  set q := quantile (cdf ν) u with hq
  by_contra hlt
  push Not at hlt
  have hcont := (cdf ν).right_continuous q
  have hev : ∀ᶠ z in 𝓝[Set.Ici q] q, cdf ν z < u := hcont.tendsto.eventually (eventually_lt_nhds hlt)
  obtain ⟨b, hb, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
  obtain ⟨z, hz, hzb⟩ := exists_lt_of_csInf_lt (qset_nonempty hu1) (show q < b from hb)
  have hqz : q ≤ z := csInf_le (qset_bdd u) hz
  have := hsub ⟨hqz, hzb⟩
  exact absurd hz.2 (not_le.2 this)

lemma quantile_le_iff (hν0 : ν (Set.Iio 0) = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (y : ℝ) :
    quantile (cdf ν) u ≤ y ↔ u ≤ cdf ν y := by
  constructor
  · intro h; exact le_trans (le_cdf_quantile hu1) (monotone_cdf ν h)
  · intro h
    have hy : 0 ≤ y := by
      by_contra hy; push Not at hy
      rw [cdf_eq_zero_of_neg hν0 hy] at h; linarith
    exact csInf_le (qset_bdd u) ⟨hy, h⟩

lemma lt_quantile_iff (hν0 : ν (Set.Iio 0) = 0) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (y : ℝ) :
    y < quantile (cdf ν) u ↔ cdf ν y < u := by
  rw [← not_le, quantile_le_iff hν0 hu0 hu1, not_le]

lemma quantile_monotoneOn (hν0 : ν (Set.Iio 0) = 0) :
    MonotoneOn (quantile (cdf ν)) (Set.Ioo 0 1) := by
  intro u hu v hv huv
  rw [quantile_le_iff hν0 hu.1 hu.2]
  exact le_trans huv (le_cdf_quantile hv.2)

lemma quantile_aemeasurable (hν0 : ν (Set.Iio 0) = 0) :
    AEMeasurable (quantile (cdf ν)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (quantile_monotoneOn hν0)

lemma volume_Ioo_inter_Iic {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic a) = ENNReal.ofReal a := by
  apply le_antisymm
  · calc volume (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic a) ≤ volume (Set.Icc 0 a) := by
          apply measure_mono; intro u hu; exact ⟨hu.1.1.le, hu.2⟩
      _ = ENNReal.ofReal a := by rw [Real.volume_Icc, sub_zero]
  · calc ENNReal.ofReal a = volume (Set.Ioo 0 a) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ _ := by
          apply measure_mono; intro u hu
          exact ⟨⟨hu.1, lt_of_lt_of_le hu.2 ha1⟩, hu.2.le⟩

/-- The quantile transform: the law of `F⁻¹(U)`, `U` uniform on `(0,1)`, is `ν`. -/
lemma map_quantile (hν0 : ν (Set.Iio 0) = 0) :
    Measure.map (quantile (cdf ν)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) = ν := by
  symm
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply_of_aemeasurable (quantile_aemeasurable hν0) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo]
  have hset : quantile (cdf ν) ⁻¹' Set.Iic y ∩ Set.Ioo 0 1 = Set.Ioo 0 1 ∩ Set.Iic (cdf ν y) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (quantile_le_iff hν0 h2.1 h2.2 y).1 h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨(quantile_le_iff hν0 h2.1 h2.2 y).2 h1, h2⟩
  rw [hset, volume_Ioo_inter_Iic (cdf_nonneg ν y) (cdf_le_one ν y), ofReal_cdf]

lemma integral_eq_quantile (hν0 : ν (Set.Iio 0) = 0) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂ν = ∫ u in Set.Ioo (0 : ℝ) 1, f (quantile (cdf ν) u) := by
  conv_lhs => rw [← map_quantile hν0]
  exact integral_map (quantile_aemeasurable hν0) hf.aestronglyMeasurable

lemma integrable_quantile_iff (hν0 : ν (Set.Iio 0) = 0) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f ν ↔ IntegrableOn (fun u => f (quantile (cdf ν) u)) (Set.Ioo (0 : ℝ) 1) := by
  conv_lhs => rw [← map_quantile hν0]
  exact integrable_map_measure hf.aestronglyMeasurable (quantile_aemeasurable hν0)

lemma quantile_intervalIntegrable (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) :
    IntervalIntegrable (quantile (cdf ν)) volume 0 1 := by
  have h := (integrable_quantile_iff hν0 continuous_id).1 hν1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    integrableOn_Ioc_iff_integrableOn_Ioo]
  exact h

lemma quantile_intervalIntegrable' (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (quantile (cdf ν)) volume a b := by
  apply (quantile_intervalIntegrable hν0 hν1).mono_set
  rw [Set.uIcc_of_le zero_le_one]
  intro u hu
  rcases le_total a b with h | h
  · rw [Set.uIcc_of_le h] at hu; exact ⟨le_trans ha.1 hu.1, le_trans hu.2 hb.2⟩
  · rw [Set.uIcc_of_ge h] at hu; exact ⟨le_trans hb.1 hu.1, le_trans hu.2 ha.2⟩

/-- `∫ g dν` as an interval integral of `g ∘ F⁻¹` over `[0,1]`. -/
lemma integral_eq_quantile' (hν0 : ν (Set.Iio 0) = 0) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂ν = ∫ u in (0 : ℝ)..1, f (quantile (cdf ν) u) := by
  rw [integral_eq_quantile hν0 hf, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

lemma Vlim_eq (t : ℝ) : Vlim ν t = ∫ u in (1 - t)..1, quantile (cdf ν) u := by
  unfold Vlim
  rw [intervalIntegral.integral_comp_sub_left (fun u => quantile (cdf ν) u) 1, sub_zero]

/-- `G(y) = E (X - y)^+`. -/
noncomputable def G (ν : Measure ℝ) (y : ℝ) : ℝ := ∫ x, max (x - y) 0 ∂ν

lemma G_eq (hν0 : ν (Set.Iio 0) = 0) (y : ℝ) :
    G ν y = ∫ u in (0 : ℝ)..1, max (quantile (cdf ν) u - y) 0 :=
  integral_eq_quantile' hν0 (f := fun x => max (x - y) 0) (by fun_prop)

lemma posPart_intervalIntegrable (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (y : ℝ)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun u => max (quantile (cdf ν) u - y) 0) volume a b := by
  have h := quantile_intervalIntegrable' hν0 hν1 ha hb
  have h2 := h.sub (intervalIntegrable_const (c := y))
  exact ⟨Integrable.pos_part h2.1, Integrable.pos_part h2.2⟩

/-- `V̄(t) ≤ t y + G(y)` for every `t ∈ [0,1]` and every `y`. -/
lemma Vlim_le (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) : Vlim ν t ≤ t * y + G ν y := by
  have ha : 1 - t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [G_eq hν0, Vlim_eq,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1 - t)
      (posPart_intervalIntegrable hν0 hν1 y h0 ha) (posPart_intervalIntegrable hν0 hν1 y ha h1)]
  have hA : 0 ≤ ∫ u in (0 : ℝ)..(1 - t), max (quantile (cdf ν) u - y) 0 :=
    intervalIntegral.integral_nonneg ha.1 (fun u _ => le_max_right _ _)
  have hB : ∫ u in (1 - t)..1, (quantile (cdf ν) u - y) ≤
      ∫ u in (1 - t)..1, max (quantile (cdf ν) u - y) 0 :=
    intervalIntegral.integral_mono_on (by linarith [ht.1])
      ((quantile_intervalIntegrable' hν0 hν1 ha h1).sub intervalIntegrable_const)
      (posPart_intervalIntegrable hν0 hν1 y ha h1) (fun u _ => le_max_left _ _)
  rw [intervalIntegral.integral_sub (quantile_intervalIntegrable' hν0 hν1 ha h1)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at hB
  have : (1 - (1 - t)) * y = t * y := by ring
  linarith

/-- Splitting lemma: if `F⁻¹ ≤ y` below `a` and `F⁻¹ ≥ y` above `a`, then
`G(y) = V̄(1 - a) - (1 - a) y`. -/
lemma G_eq_split (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {a y : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ u ∈ Set.Ioo (0 : ℝ) 1, u < a → quantile (cdf ν) u ≤ y)
    (hhi : ∀ u ∈ Set.Ioo (0 : ℝ) 1, a < u → y ≤ quantile (cdf ν) u) :
    G ν y = Vlim ν (1 - a) - (1 - a) * y := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [G_eq hν0, Vlim_eq, sub_sub_cancel,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (posPart_intervalIntegrable hν0 hν1 y h0 ha) (posPart_intervalIntegrable hν0 hν1 y ha h1)]
  have hA : ∫ u in (0 : ℝ)..a, max (quantile (cdf ν) u - y) 0 = 0 := by
    rw [intervalIntegral.integral_of_le ha.1, integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu.1, lt_of_lt_of_le hu.2 ha.2⟩
      simp only
      exact max_eq_right (by linarith [hlo u hu' hu.2])
  have hB : ∫ u in a..1, max (quantile (cdf ν) u - y) 0 =
      ∫ u in a..1, (quantile (cdf ν) u - y) := by
    rw [intervalIntegral.integral_of_le ha.2, intervalIntegral.integral_of_le ha.2,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt ha.1 hu.1, hu.2⟩
    exact max_eq_left (by linarith [hhi u hu' hu.1])
  rw [hA, hB, zero_add, intervalIntegral.integral_sub (quantile_intervalIntegrable' hν0 hν1 ha h1)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]

/-- For `t ∈ (0,1]` there is `y ≥ 0` with `V̄(t) = t y + G(y)`. -/
lemma Vlim_eq_exists (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) : ∃ y, 0 ≤ y ∧ Vlim ν t = t * y + G ν y := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h
    refine ⟨0, le_rfl, ?_⟩
    have := G_eq_split hν0 hν1 (a := 0) (y := 0) ⟨le_rfl, zero_le_one⟩
      (fun u hu hu0 => absurd hu.1 (not_lt.2 hu0.le))
      (fun u hu _ => quantile_nonneg _ u)
    rw [this]; simp
  · refine ⟨quantile (cdf ν) (1 - t), quantile_nonneg _ _, ?_⟩
    have hm : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.1]⟩
    have := G_eq_split hν0 hν1 (a := 1 - t) (y := quantile (cdf ν) (1 - t))
      ⟨hm.1.le, hm.2.le⟩
      (fun u hu hlt => quantile_monotoneOn hν0 hu hm hlt.le)
      (fun u hu hlt => quantile_monotoneOn hν0 hm hu hlt.le)
    rw [this, sub_sub_cancel]; ring

end Quantile
end BSPAux




namespace BSPAux
open LargeBSP.Homog

section Tstar
variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma tstar_mem (c : ℝ) : tstar ν c ∈ Set.Icc (0 : ℝ) 1 := by
  unfold tstar
  constructor
  · exact Real.sSup_nonneg (fun s hs => hs.1.1.le)
  · exact Real.sSup_le (fun s hs => hs.1.2.le) zero_le_one

lemma tstar_hi (hν0 : ν (Set.Iio 0) = 0) (c : ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (h : 1 - tstar ν c < u) : c ≤ quantile (cdf ν) u := by
  have hs : 1 - u < tstar ν c := by linarith
  unfold tstar at hs
  have hne : {s : ℝ | s ∈ Set.Ioo 0 1 ∧ c ≤ quantile (cdf ν) (1 - s)}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty] at hs
    linarith [hu.2]
  obtain ⟨s', hs', hlt⟩ := exists_lt_of_lt_csSup hne hs
  have hm : 1 - s' ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs'.1.2], by linarith [hs'.1.1]⟩
  exact le_trans hs'.2 (quantile_monotoneOn hν0 hm hu (by linarith))

lemma tstar_lo (c : ℝ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (h : u < 1 - tstar ν c) : quantile (cdf ν) u < c := by
  by_contra hc
  push Not at hc
  have hmem : 1 - u ∈ {s : ℝ | s ∈ Set.Ioo 0 1 ∧ c ≤ quantile (cdf ν) (1 - s)} := by
    refine ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
    simpa using hc
  have := le_csSup (⟨1, fun s hs => hs.1.2.le⟩ : BddAbove {s : ℝ | s ∈ Set.Ioo 0 1 ∧
    c ≤ quantile (cdf ν) (1 - s)}) hmem
  unfold tstar at h
  linarith

/-- `G(c) = V̄(t⋆) - t⋆ c`. -/
lemma G_eq_tstar (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (c : ℝ) :
    G ν c = Vlim ν (tstar ν c) - tstar ν c * c := by
  have ht := tstar_mem (ν := ν) c
  have := G_eq_split hν0 hν1 (a := 1 - tstar ν c) (y := c)
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
    (fun u hu hlt => (tstar_lo c hu hlt).le) (fun u hu hlt => tstar_hi hν0 c hu hlt)
  rw [this, sub_sub_cancel]

lemma tstar_max (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (c : ℝ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Vlim ν t - t * c ≤ Vlim ν (tstar ν c) - tstar ν c * c := by
  intro t ht
  have := Vlim_le hν0 hν1 ht c
  rw [G_eq_tstar hν0 hν1] at this
  linarith

lemma tstar_cont (hν0 : ν (Set.Iio 0) = 0) (c : ℝ) (hcont : ContinuousAt (cdf ν) c) :
    tstar ν c = 1 - cdf ν c := by
  set S := {s : ℝ | s ∈ Set.Ioo 0 1 ∧ c ≤ quantile (cdf ν) (1 - s)} with hS
  have hin : ∀ s ∈ Set.Ioo (0 : ℝ) 1, s < 1 - cdf ν c → s ∈ S := by
    intro s hs hlt
    refine ⟨hs, ?_⟩
    by_contra hq
    push Not at hq
    have hu : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := (quantile_le_iff hν0 hu.1 hu.2 c).1 hq.le
    linarith
  have hout : ∀ s ∈ S, s ≤ 1 - cdf ν c := by
    intro s hs
    by_contra hlt
    push Not at hlt
    have hu : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1.2], by linarith [hs.1.1]⟩
    have hlt' : 1 - s < cdf ν c := by linarith
    have hev : ∀ᶠ y in 𝓝[<] c, 1 - s < cdf ν y :=
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually (eventually_gt_nhds hlt')
    obtain ⟨y, hy1, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
    have := (quantile_le_iff hν0 hu.1 hu.2 y).2 hy1.le
    have := hs.2
    have hy2 : y < c := hy2
    linarith
  unfold tstar
  rw [← hS]
  have hF1 := cdf_le_one ν c
  have hF0 := cdf_nonneg ν c
  rcases eq_or_lt_of_le (show 0 ≤ 1 - cdf ν c by linarith) with ha | ha
  · have : S = ∅ := by
      ext s; simp only [Set.mem_empty_iff_false, iff_false]
      intro hs; have := hout s hs; linarith [hs.1.1]
    rw [this, Real.sSup_empty, ← ha]
  · apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨(1 - cdf ν c) / 2, hin _ ⟨by linarith, by linarith⟩ (by linarith)⟩
    · exact hout
    · intro w hw
      refine ⟨(max w 0 + (1 - cdf ν c)) / 2, hin _ ⟨?_, ?_⟩ ?_, ?_⟩
      · have := le_max_right w 0; linarith
      · have := max_lt hw ha; linarith
      · have := max_lt hw ha; linarith
      · have := le_max_left w 0; have := max_lt hw ha; linarith

/-- The milestone `integral_pos_part_eq`. -/
lemma integral_pos_part_eq_aux (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (c : ℝ) :
    ∫ s in (0 : ℝ)..1, max (quantile (cdf ν) (1 - s) - c) 0 =
        ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) ∧
      ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) =
        Vlim ν (tstar ν c) - tstar ν c * c := by
  have ht := tstar_mem (ν := ν) c
  have h2 : ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) =
      Vlim ν (tstar ν c) - tstar ν c * c := by
    have hii : IntervalIntegrable (fun s => quantile (cdf ν) (1 - s)) volume 0 (tstar ν c) := by
      have := (quantile_intervalIntegrable' hν0 hν1 (a := 1 - tstar ν c) (b := 1)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ ⟨zero_le_one, le_rfl⟩)
      have h' := this.comp_sub_left 1
      simpa using h'.symm
    rw [intervalIntegral.integral_sub hii intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, sub_zero]
    rfl
  refine ⟨?_, h2⟩
  rw [h2, ← G_eq_tstar hν0 hν1, G_eq hν0,
    intervalIntegral.integral_comp_sub_left (fun u => max (quantile (cdf ν) u - c) 0) 1]
  simp

end Tstar
end BSPAux




namespace BSPAux
open LargeBSP.Homog

section Meas
variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_rank {X : ℕ → Ω → ℝ} (hXm : ∀ n, Measurable (X n)) (N i : ℕ) :
    Measurable (fun ω => rank (fun n => X n ω) N i) := by
  classical
  simp_rw [rank_eq, Finset.card_filter]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_lt (hXm i) (hXm j)).union
    ((measurableSet_eq_fun (hXm j) (hXm i)).inter (MeasurableSet.const _))

lemma V_eq_sum_ite (x : ℕ → ℝ) (N m : ℕ) :
    V x N m = ∑ i ∈ Finset.range N, if rank x N i < m then x i else 0 := by
  rw [V, topSet, Finset.sum_filter]

lemma measurable_V {X : ℕ → Ω → ℝ} (hXm : ∀ n, Measurable (X n)) (N m : ℕ) :
    Measurable (fun ω => V (fun n => X n ω) N m) := by
  simp_rw [V_eq_sum_ite]
  apply Finset.measurable_sum; intro i _
  exact Measurable.ite (measurable_rank hXm N i measurableSet_Iio) (hXm i) measurable_const

end Meas

section Prob
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma tim_iff {f : ℕ → Ω → ℝ} {a : ℝ} : TendstoInMeasure P f atTop (fun _ => a) ↔
    ∀ ε, 0 < ε → Tendsto (fun N => P {ω | ε ≤ |f N ω - a|}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_norm]; simp only [Real.norm_eq_abs]

lemma tz_mono {A B : ℕ → Set Ω} (hB : Tendsto (fun N => P (B N)) atTop (𝓝 0))
    (h : ∀ᶠ N in atTop, A N ⊆ B N) : Tendsto (fun N => P (A N)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
    (Eventually.of_forall fun N => zero_le) (h.mono fun N hN => measure_mono hN)

lemma tz_union {A B C : ℕ → Set Ω} (hB : Tendsto (fun N => P (B N)) atTop (𝓝 0))
    (hC : Tendsto (fun N => P (C N)) atTop (𝓝 0))
    (h : ∀ᶠ N in atTop, A N ⊆ B N ∪ C N) : Tendsto (fun N => P (A N)) atTop (𝓝 0) := by
  apply tz_mono (B := fun N => B N ∪ C N) _ h
  have := hB.add hC
  rw [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
    (fun N => zero_le) (fun N => measure_union_le _ _)

lemma tz_biUnion {ι : Type*} (s : Finset ι) {B : ι → ℕ → Set Ω}
    (hB : ∀ k ∈ s, Tendsto (fun N => P (B k N)) atTop (𝓝 0)) :
    Tendsto (fun N => P (⋃ k ∈ s, B k N)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum s hB
  simp only [Finset.sum_const_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun N => zero_le) (fun N => measure_biUnion_finset_le s _)

lemma tz_empty {A : ℕ → Set Ω} (h : ∀ᶠ N in atTop, A N = ∅) :
    Tendsto (fun N => P (A N)) atTop (𝓝 0) :=
  tz_mono (B := fun _ => ∅) (by simp) (h.mono fun N hN => by simp [hN])

end Prob

/-- Pathwise bracketing of `min x y` by a step function. -/
lemma min_bracket {x y Δ : ℝ} (hx : 0 ≤ x) (hΔ : 0 ≤ Δ) {k : ℕ} (hk : (k : ℝ) * Δ = y) :
    Δ * (∑ j ∈ Finset.range k, if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0) ≤ min x y ∧
    min x y ≤ Δ * (∑ j ∈ Finset.range k, if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0) + Δ := by
  set g : ℕ → ℝ := fun j => min x ((j : ℝ) * Δ) with hg
  have ha : ∀ j : ℕ, Δ * (if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0) ≤ g (j + 1) - g j := by
    intro j
    simp only [hg]; push_cast
    split_ifs with h
    · rw [min_eq_right h.le, min_eq_right (by nlinarith)]; ring_nf; rfl
    · rw [mul_zero]; apply sub_nonneg.2; apply min_le_min le_rfl; nlinarith
  have hb : ∀ j : ℕ, g (j + 2) - g (j + 1) ≤ Δ * (if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0) := by
    intro j
    simp only [hg]; push_cast
    split_ifs with h
    · rw [min_eq_right h.le]; have := min_le_right x (((j : ℝ) + 2) * Δ); nlinarith
    · push Not at h
      rw [min_eq_left h, min_eq_left (by nlinarith)]; simp
  have s1 : ∑ j ∈ Finset.range k, (g (j + 1) - g j) = g k - g 0 := Finset.sum_range_sub g k
  have s2 : ∑ j ∈ Finset.range k, (g (j + 1 + 1) - g (j + 1)) = g (k + 1) - g (0 + 1) :=
    Finset.sum_range_sub (fun j => g (j + 1)) k
  have hg0 : g 0 = 0 := by simp [hg, hx]
  have hgk : g k = min x y := by simp [hg, hk]
  have hgk1 : g k ≤ g (k + 1) := by
    simp only [hg]; apply min_le_min le_rfl; push_cast; nlinarith
  have hg1 : g (0 + 1) ≤ Δ := by simp [hg]
  rw [Finset.mul_sum]
  constructor
  · calc ∑ j ∈ Finset.range k, Δ * (if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0)
          ≤ ∑ j ∈ Finset.range k, (g (j + 1) - g j) := Finset.sum_le_sum (fun j _ => ha j)
      _ = min x y := by rw [s1, hg0, hgk, sub_zero]
  · have : ∑ j ∈ Finset.range k, (g (j + 1 + 1) - g (j + 1)) ≤
        ∑ j ∈ Finset.range k, Δ * (if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun j _ => hb j)
    rw [s2] at this
    linarith

end BSPAux




namespace BSPAux
open LargeBSP.Homog

section TIM
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma tim_sub {f g : ℕ → Ω → ℝ} {a b : ℝ} (hf : TendstoInMeasure P f atTop (fun _ => a))
    (hg : TendstoInMeasure P g atTop (fun _ => b)) :
    TendstoInMeasure P (fun N ω => f N ω - g N ω) atTop (fun _ => a - b) := by
  rw [tim_iff] at *
  intro ε hε
  apply tz_union (hf (ε / 2) (by linarith)) (hg (ε / 2) (by linarith))
  refine Eventually.of_forall fun N ω hω => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra h
  push Not at h
  have : |f N ω - g N ω - (a - b)| ≤ |f N ω - a| + |g N ω - b| := by
    rw [show f N ω - g N ω - (a - b) = (f N ω - a) - (g N ω - b) by ring]
    exact abs_sub _ _
  linarith [h.1, h.2]

lemma tim_add {f g : ℕ → Ω → ℝ} {a b : ℝ} (hf : TendstoInMeasure P f atTop (fun _ => a))
    (hg : TendstoInMeasure P g atTop (fun _ => b)) :
    TendstoInMeasure P (fun N ω => f N ω + g N ω) atTop (fun _ => a + b) := by
  rw [tim_iff] at *
  intro ε hε
  apply tz_union (hf (ε / 2) (by linarith)) (hg (ε / 2) (by linarith))
  refine Eventually.of_forall fun N ω hω => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra h
  push Not at h
  have : |f N ω + g N ω - (a + b)| ≤ |f N ω - a| + |g N ω - b| := by
    rw [show f N ω + g N ω - (a + b) = (f N ω - a) + (g N ω - b) by ring]
    exact abs_add_le _ _
  linarith [h.1, h.2]

lemma tim_congr {f g : ℕ → Ω → ℝ} {a : ℝ} (hf : TendstoInMeasure P f atTop (fun _ => a))
    (h : ∀ᶠ N in atTop, ∀ ω, f N ω = g N ω) : TendstoInMeasure P g atTop (fun _ => a) := by
  rw [tim_iff] at *
  intro ε hε
  apply tz_mono (hf ε hε)
  filter_upwards [h] with N hN ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rwa [hN ω]

lemma tim_const_of {f : ℕ → Ω → ℝ} {a : ℝ}
    (h : ∀ ε > 0, ∀ᶠ N in atTop, ∀ ω, |f N ω - a| < ε) :
    TendstoInMeasure P f atTop (fun _ => a) := by
  rw [tim_iff]
  intro ε hε
  apply tz_empty
  filter_upwards [h ε hε] with N hN
  ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]; exact hN ω

end TIM

lemma sum_ite_lt_eq (x : ℕ → ℝ) {N : ℕ} (hN : N ≠ 0) (z : ℝ) :
    (∑ i ∈ Finset.range N, if z < x i then (1 : ℝ) else 0) = N * (1 - empCdf x N z) := by
  rw [Finset.sum_boole]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range N) (fun i => x i ≤ z)
  have h2 : (Finset.range N).filter (fun i => ¬ x i ≤ z) =
      (Finset.range N).filter (fun i => z < x i) := by
    apply Finset.filter_congr; intro i _; exact not_le
  rw [h2, Finset.card_range] at h
  unfold empCdf
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h3 : (((Finset.range N).filter (fun i => z < x i)).card : ℝ) =
      N - ((Finset.range N).filter (fun i => x i ≤ z)).card := by
    have h' : ((((Finset.range N).filter (fun i => x i ≤ z)).card +
        ((Finset.range N).filter (fun i => z < x i)).card : ℕ) : ℝ) = N := by exact_mod_cast h
    push_cast at h'; linarith
  rw [h3]; field_simp

/-- `Δ Σ_{j<k} (1 - F((j+1)Δ))`. -/
noncomputable def stepSum (F : ℝ → ℝ) (Δ : ℝ) (k : ℕ) : ℝ :=
  Δ * ∑ j ∈ Finset.range k, (1 - F (((j : ℝ) + 1) * Δ))

lemma avg_min_bracket (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) {N : ℕ} (hN : N ≠ 0) {y Δ : ℝ}
    (hΔ : 0 ≤ Δ) {k : ℕ} (hk : (k : ℝ) * Δ = y) :
    stepSum (empCdf x N) Δ k ≤ (∑ i ∈ Finset.range N, min (x i) y) / N ∧
    (∑ i ∈ Finset.range N, min (x i) y) / N ≤ stepSum (empCdf x N) Δ k + Δ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hsum : ∑ i ∈ Finset.range N, Δ * (∑ j ∈ Finset.range k,
      if ((j : ℝ) + 1) * Δ < x i then (1 : ℝ) else 0) = N * stepSum (empCdf x N) Δ k := by
    rw [← Finset.mul_sum, Finset.sum_comm, stepSum]
    simp_rw [sum_ite_lt_eq x hN]
    rw [← Finset.mul_sum]; ring
  have hlo : N * stepSum (empCdf x N) Δ k ≤ ∑ i ∈ Finset.range N, min (x i) y := by
    rw [← hsum]; exact Finset.sum_le_sum (fun i _ => (min_bracket (hx i) hΔ hk).1)
  have hhi : ∑ i ∈ Finset.range N, min (x i) y ≤ N * stepSum (empCdf x N) Δ k + N * Δ := by
    rw [← hsum]
    have := Finset.sum_le_sum (s := Finset.range N) (fun i _ => (min_bracket (hx i) hΔ hk).2)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  constructor
  · rw [le_div_iff₀ hN']; linarith
  · rw [div_le_iff₀ hN']; linarith

section Nu
variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma ae_nonneg (hν0 : ν (Set.Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  convert hν0 using 2
  ext x; simp

lemma integral_ite_lt (z : ℝ) :
    ∫ x, (if z < x then (1 : ℝ) else 0) ∂ν = 1 - cdf ν z := by
  have : (fun x => if z < x then (1 : ℝ) else 0) = (Set.Ioi z).indicator (fun _ => (1 : ℝ)) := by
    funext x; simp [Set.indicator_apply]
  rw [this, integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul, mul_one,
    cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

lemma integrable_ite_lt (z : ℝ) : Integrable (fun x => if z < x then (1 : ℝ) else 0) ν := by
  have : (fun x => if z < x then (1 : ℝ) else 0) = (Set.Ioi z).indicator (fun _ => (1 : ℝ)) := by
    funext x; simp [Set.indicator_apply]
  rw [this]; exact (integrable_const _).indicator measurableSet_Ioi

lemma integrable_min (hν1 : Integrable id ν) (y : ℝ) : Integrable (fun x => min x y) ν :=
  Integrable.inf hν1 (integrable_const y)

lemma int_min_bracket (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) {y Δ : ℝ}
    (hΔ : 0 ≤ Δ) {k : ℕ} (hk : (k : ℝ) * Δ = y) :
    stepSum (cdf ν) Δ k ≤ ∫ x, min x y ∂ν ∧ ∫ x, min x y ∂ν ≤ stepSum (cdf ν) Δ k + Δ := by
  have hint : Integrable (fun x => Δ * (∑ j ∈ Finset.range k,
      if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0)) ν :=
    (integrable_finsetSum _ (fun j _ => integrable_ite_lt _)).const_mul Δ
  have heq : ∫ x, Δ * (∑ j ∈ Finset.range k,
      if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0) ∂ν = stepSum (cdf ν) Δ k := by
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_ite_lt _), stepSum]
    simp_rw [integral_ite_lt]
  constructor
  · rw [← heq]
    exact integral_mono_ae hint (integrable_min hν1 y)
      ((ae_nonneg hν0).mono fun x hx => (min_bracket hx hΔ hk).1)
  · have h2 : ∫ x, (Δ * (∑ j ∈ Finset.range k,
        if ((j : ℝ) + 1) * Δ < x then (1 : ℝ) else 0) + Δ) ∂ν = stepSum (cdf ν) Δ k + Δ := by
      rw [integral_add hint (integrable_const Δ), heq, integral_const]; simp
    rw [← h2]
    exact integral_mono_ae (integrable_min hν1 y) (hint.add (integrable_const Δ))
      ((ae_nonneg hν0).mono fun x hx => (min_bracket hx hΔ hk).2)

end Nu
end BSPAux




namespace BSPAux
open LargeBSP.Homog

lemma tim_avg_min {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    {y : ℝ} (hy : 0 ≤ y) :
    TendstoInMeasure P (fun (N : ℕ) ω => (∑ i ∈ Finset.range N, min (X i ω) y) / N) atTop
      (fun _ => ∫ x, min x y ∂ν) := by
  rw [tim_iff]
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * y / ε < k := exists_nat_gt _
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  set Δ := y / k with hΔdef
  have hΔ0 : 0 ≤ Δ := by positivity
  have hkΔ : (k : ℝ) * Δ = y := by rw [hΔdef]; field_simp
  have hΔε : Δ < ε / 2 := by
    rw [hΔdef, div_lt_iff₀ hkpos]; rw [div_lt_iff₀ hε] at hk; linarith
  set η := ε / (2 * (y + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hyη : y * η < ε / 2 := by
    rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  apply tz_mono (tz_biUnion (Finset.range k)
    (B := fun j N => {ω | η ≤ |empCdf (fun n => X n ω) N (((j : ℝ) + 1) * Δ) -
      cdf ν (((j : ℝ) + 1) * Δ)|})
    (fun j _ => (tim_iff.1 (hA1 _ (by positivity))) η hη0))
  filter_upwards [eventually_ne_atTop 0] with N hN ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨a1, a2⟩ := avg_min_bracket (fun n => X n ω) (fun i => hX0 i ω) hN hΔ0 hkΔ
  obtain ⟨b1, b2⟩ := int_min_bracket hν0 hν1 hΔ0 hkΔ
  have hdiff : |stepSum (empCdf (fun n => X n ω) N) Δ k - stepSum (cdf ν) Δ k| ≤ y * η := by
    rw [stepSum, stepSum, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hΔ0]
    calc Δ * |∑ j ∈ Finset.range k, ((1 - empCdf (fun n => X n ω) N (((j : ℝ) + 1) * Δ)) -
          (1 - cdf ν (((j : ℝ) + 1) * Δ)))|
        ≤ Δ * ∑ j ∈ Finset.range k, |(1 - empCdf (fun n => X n ω) N (((j : ℝ) + 1) * Δ)) -
          (1 - cdf ν (((j : ℝ) + 1) * Δ))| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hΔ0
      _ ≤ Δ * ∑ j ∈ Finset.range k, η := by
          apply mul_le_mul_of_nonneg_left _ hΔ0
          apply Finset.sum_le_sum
          intro j hj
          rw [show ∀ a b : ℝ, (1 - a) - (1 - b) = -(a - b) from fun a b => by ring, abs_neg]
          exact (hcon j hj).le
      _ = y * η := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, mul_comm Δ, hkΔ]
  rw [abs_le] at hdiff
  have : |(∑ i ∈ Finset.range N, min (X i ω) y) / N - ∫ x, min x y ∂ν| < ε := by
    rw [abs_sub_lt_iff]; constructor <;> linarith [hdiff.1, hdiff.2]
  linarith

lemma tim_avg_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν))
    {y : ℝ} (hy : 0 ≤ y) :
    TendstoInMeasure P (fun (N : ℕ) ω => (∑ i ∈ Finset.range N, max (X i ω - y) 0) / N) atTop
      (fun _ => G ν y) := by
  have h := tim_sub hWLLN (tim_avg_min P X hX0 ν hν0 hν1 hA1 hy)
  have hpt : ∀ x : ℝ, x - min x y = max (x - y) 0 := by
    intro x; rw [min_def, max_def]; split_ifs <;> linarith
  have hG : G ν y = (∫ x, x ∂ν) - ∫ x, min x y ∂ν := by
    have hν1' : Integrable (fun x : ℝ => x) ν := hν1
    rw [G, ← integral_sub hν1' (integrable_min hν1 y)]
    congr 1; funext x; rw [hpt]
  rw [hG]
  apply tim_congr h (Eventually.of_forall fun N ω => ?_)
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hpt _)

end BSPAux




namespace BSPAux
open LargeBSP.Homog

lemma GN_lip (x : ℕ → ℝ) (N : ℕ) (y y' : ℝ) :
    |(∑ i ∈ Finset.range N, max (x i - y) 0) / N - (∑ i ∈ Finset.range N, max (x i - y') 0) / N|
      ≤ |y - y'| := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hN', div_le_iff₀ hN']
  calc |∑ i ∈ Finset.range N, (max (x i - y) 0 - max (x i - y') 0)|
      ≤ ∑ i ∈ Finset.range N, |max (x i - y) 0 - max (x i - y') 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, |y - y'| := Finset.sum_le_sum fun i _ => by
          have := abs_max_sub_max_le_abs (x i - y) (x i - y') 0
          rwa [show x i - y - (x i - y') = -(y - y') by ring, abs_neg] at this
    _ = |y - y'| * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

lemma card_gt_eq (x : ℕ → ℝ) {N : ℕ} (hN : N ≠ 0) (z : ℝ) :
    ((((Finset.range N).filter (fun i => z < x i)).card : ℕ) : ℝ) = N * (1 - empCdf x N z) := by
  rw [← sum_ite_lt_eq x hN z, Finset.sum_boole]

/-- Part (i) of Theorem 2: `V̄_N(t) ⇒ V̄(t)`. -/
lemma tim_Vbar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    TendstoInMeasure P (fun (N : ℕ) ω => Vbar (fun n => X n ω) N t) atTop
      (fun _ => Vlim ν t) := by
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · subst h0
    apply tim_const_of
    intro ε hε
    refine Eventually.of_forall fun N ω => ?_
    simp [Vbar, Vlim, V_zero, hε]
  have hGN := fun y (hy : 0 ≤ y) => tim_iff.1 (tim_avg_pos P X hX0 ν hν0 hν1 hA1 hWLLN hy)
  rw [tim_iff]
  intro ε hε
  obtain ⟨y0, hy0, hVy0⟩ := Vlim_eq_exists hν0 hν1 ⟨htpos, ht.2⟩
  obtain ⟨M, hM1, hMF⟩ : ∃ M : ℝ, 1 ≤ M ∧ 1 - t / 2 < cdf ν M := by
    have h := (tendsto_cdf_atTop ν).eventually_const_lt (show 1 - t / 2 < 1 by linarith)
    obtain ⟨M, hM⟩ := (h.and (eventually_ge_atTop 1)).exists
    exact ⟨M, hM.2, hM.1⟩
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 6 * M / ε < k := exists_nat_gt _
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  set δ := M / k with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ < ε / 6 := by
    rw [hδ, div_lt_iff₀ hkpos]; rw [div_lt_iff₀ hε] at hk; linarith
  have hkδ : (k : ℝ) * δ = M := by rw [hδ]; field_simp
  apply tz_union (hGN y0 hy0 ε hε) (tz_union ((tim_iff.1 (hA1 M hM0)) (t / 4) (by linarith))
    (tz_biUnion (Finset.range (k + 1))
      (B := fun j N => {ω | ε / 3 ≤ |(∑ i ∈ Finset.range N, max (X i ω - j * δ) 0) / N -
        G ν (j * δ)|})
      (fun j _ => hGN _ (by positivity) (ε / 3) (by linarith)))
    (Eventually.of_forall fun N => subset_refl _))
  have hN1 := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually
    (gt_mem_nhds (show (0 : ℝ) < t / 4 by linarith))
  have hN2 := (tendsto_const_div_atTop_nhds_zero_nat M).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 6 by linarith))
  filter_upwards [eventually_ne_atTop 0, hN1, hN2] with N hN hN1 hN2 ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨hc0, hc1, hc2⟩ := hcon
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hN1' : 4 < N * t := by
    rw [div_lt_iff₀ hNpos] at hN1; linarith
  have hN2' : M / N < ε / 6 := hN2
  set m := ⌊(N : ℝ) * t⌋₊ with hm
  have hm1 : (m : ℝ) ≤ N * t := Nat.floor_le (by positivity)
  have hm2 : (N : ℝ) * t < m + 1 := Nat.lt_floor_add_one _
  have hmN : m ≤ N := by
    have : (m : ℝ) ≤ N := le_trans hm1 (by nlinarith [ht.2])
    exact_mod_cast this
  have hVbar : Vbar (fun n => X n ω) N t = V (fun n => X n ω) N m / N := rfl
  set r : ℝ := (m : ℝ) / N with hr
  have hr0 : 0 ≤ r := by positivity
  have hrt : r ≤ t := by rw [hr, div_le_iff₀ hNpos]; linarith
  have hrt' : t - 1 / N < r := by
    rw [hr, lt_div_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ hNpos.ne']; linarith
  -- upper bound
  have hup : Vbar (fun n => X n ω) N t - Vlim ν t < ε := by
    have h1 := V_le (fun n => X n ω) N m hy0
    have e : (∑ i ∈ Finset.range N, max (X i ω - y0) 0) / N * N =
        ∑ i ∈ Finset.range N, max (X i ω - y0) 0 := div_mul_cancel₀ _ hNpos.ne'
    have h2 : V (fun n => X n ω) N m / N ≤
        t * y0 + (∑ i ∈ Finset.range N, max (X i ω - y0) 0) / N := by
      rw [div_le_iff₀ hNpos]
      have : (m : ℝ) * y0 ≤ N * t * y0 := mul_le_mul_of_nonneg_right hm1 hy0
      nlinarith
    have h3 := (abs_lt.1 hc0).2
    rw [hVbar, hVy0]; linarith
  -- lower bound
  have hK : ((Finset.range N).filter (fun i => M < X i ω)).card ≤ m := by
    have hc := card_gt_eq (fun n => X n ω) hN M
    have h1 := (abs_lt.1 hc1)
    have : ((((Finset.range N).filter (fun i => M < X i ω)).card : ℕ) : ℝ) < m := by
      rw [hc]
      have : 1 - empCdf (fun n => X n ω) N M < 3 * t / 4 := by linarith [h1.1]
      nlinarith
    exact_mod_cast this.le
  obtain ⟨y, ⟨hy0', hyM⟩, hVy⟩ := V_eq_exists (fun i => hX0 i ω) hmN hM0 hK
  set j := ⌊y / δ⌋₊ with hj
  have hj1 : (j : ℝ) * δ ≤ y := by
    have := Nat.floor_le (show 0 ≤ y / δ by positivity)
    rw [← hj, le_div_iff₀ hδ0] at this; exact this
  have hj2 : y < j * δ + δ := by
    have := Nat.lt_floor_add_one (y / δ)
    rw [← hj, div_lt_iff₀ hδ0] at this; linarith
  have hjk : j ∈ Finset.range (k + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hδ0, hkδ]; exact hyM
  have hcj := (abs_lt.1 (hc2 j hjk))
  have hlip := GN_lip (fun n => X n ω) N y (j * δ)
  have hlip' := (abs_le.1 hlip)
  have hyj : |y - j * δ| ≤ δ := by rw [abs_le]; constructor <;> linarith
  have hlow : Vlim ν t - Vbar (fun n => X n ω) N t < ε := by
    have hVl := Vlim_le hν0 hν1 ht (j * δ)
    have hjδ0 : 0 ≤ (j : ℝ) * δ := by positivity
    have hjδM : (j : ℝ) * δ ≤ M := le_trans hj1 hyM
    have hVb : Vbar (fun n => X n ω) N t =
        r * y + (∑ i ∈ Finset.range N, max (X i ω - y) 0) / N := by
      rw [hVbar, hVy, add_div, hr, mul_div_right_comm]
    have e1 : r * y ≥ r * (j * δ) := mul_le_mul_of_nonneg_left hj1 hr0
    have e2 : r * (j * δ) ≥ (t - 1 / N) * (j * δ) := mul_le_mul_of_nonneg_right hrt'.le hjδ0
    have e3 : 1 / (N : ℝ) * (j * δ) ≤ M / N := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hjδM hNpos.le
    have e4 : (t - 1 / N) * (j * δ) = t * (j * δ) - 1 / N * (j * δ) := by ring
    rw [hVb]
    linarith [hcj.1, hlip'.1]
  exact absurd hω (not_le.2 (abs_lt.2 ⟨by linarith, hup⟩))

end BSPAux




namespace BSPAux
open LargeBSP.Homog

lemma unifIntegrable_avg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω) (hUI : UniformIntegrable X 1 P)
    (c : ℝ) (hc : 0 ≤ c) :
    UnifIntegrable (fun (N : ℕ) ω => (∑ i ∈ Finset.range N, max (X i ω - c) 0) / N) 1 P := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hUI.unifIntegrable hε
  refine ⟨δ, hδ, fun N s hs hPs => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hpt : ∀ ω, ‖s.indicator (fun ω => (∑ i ∈ Finset.range N, max (X i ω - c) 0) / N) ω‖ ≤
      ((1 / N : ℝ) • ∑ i ∈ Finset.range N, s.indicator (X i)) ω := by
    intro ω
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    by_cases hω : ω ∈ s
    · simp only [Set.indicator_of_mem hω]
      have h0 : 0 ≤ (∑ i ∈ Finset.range N, max (X i ω - c) 0) / N := by
        apply div_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _) (Nat.cast_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0, div_eq_inv_mul, one_div]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum; intro i _
      exact max_le (by linarith) (hX0 i ω)
    · simp [Set.indicator_of_notMem hω]
  have hN' : (N : ENNReal) ≠ 0 := by simp [hN.ne']
  calc eLpNorm (s.indicator (fun ω => (∑ i ∈ Finset.range N, max (X i ω - c) 0) / N)) 1 P
      ≤ eLpNorm ((1 / N : ℝ) • ∑ i ∈ Finset.range N, s.indicator (X i)) 1 P :=
        eLpNorm_mono_real hpt
    _ = ‖(1 / N : ℝ)‖ₑ * eLpNorm (∑ i ∈ Finset.range N, s.indicator (X i)) 1 P :=
        eLpNorm_const_smul _ _ _ _
    _ ≤ ‖(1 / N : ℝ)‖ₑ * ∑ i ∈ Finset.range N, eLpNorm (s.indicator (X i)) 1 P := by
        gcongr
        exact eLpNorm_sum_le (fun i _ => ((hXm i).indicator hs).aestronglyMeasurable) le_rfl
    _ ≤ ‖(1 / N : ℝ)‖ₑ * ∑ i ∈ Finset.range N, ENNReal.ofReal ε := by
        gcongr with i hi; exact h i s hs hPs
    _ = ENNReal.ofReal ε := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
        have : ‖(1 / N : ℝ)‖ₑ * (N : ENNReal) = 1 := by
          rw [one_div, enorm_inv (by exact_mod_cast hN.ne'), Real.enorm_natCast]
          exact ENNReal.inv_mul_cancel hN' (by simp)
        rw [this, one_mul]

lemma integrable_pos_X {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℕ → Ω → ℝ}
    (hUI : UniformIntegrable X 1 P) (c : ℝ) (i : ℕ) :
    Integrable (fun ω => max (X i ω - c) 0) P := by
  have hi : Integrable (X i) P := memLp_one_iff_integrable.1 (hUI.memLp i)
  exact Integrable.pos_part (hi.sub (integrable_const c))

/-- `PPD / N → G(c)`. -/
lemma PPD_div_tendsto_G {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    (hUI : UniformIntegrable X 1 P)
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν))
    (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ => PPD P X (fun _ => c) N / N) atTop (𝓝 (G ν c)) := by
  have heq : ∀ N : ℕ, PPD P X (fun _ => c) N / N =
      ∫ ω, (∑ i ∈ Finset.range N, max (X i ω - c) 0) / N ∂P := by
    intro N
    rw [PPD, integral_div, integral_finsetSum _ (fun i _ => integrable_pos_X hUI c i)]
  simp_rw [heq]
  have h1 : ∀ᶠ N in atTop, Integrable
      (fun ω => (∑ i ∈ Finset.range N, max (X i ω - c) 0) / (N : ℝ)) P :=
    Eventually.of_forall fun N =>
      (integrable_finsetSum _ (fun i _ => integrable_pos_X hUI c i)).div_const _
  have key := tendsto_integral_of_L1' (μ := P) (fun _ : Ω => G ν c) aestronglyMeasurable_const h1 ?_
  · convert key using 2; simp
  · have hmeas : ∀ N : ℕ, AEStronglyMeasurable
        (fun ω => (∑ i ∈ Finset.range N, max (X i ω - c) 0) / N) P := fun N =>
      ((integrable_finsetSum _ (fun i _ => integrable_pos_X hUI c i)).div_const _).aestronglyMeasurable
    exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas (memLp_const _)
      (unifIntegrable_avg hXm hX0 hUI c hc) (tim_avg_pos P X hX0 ν hν0 hν1 hA1 hWLLN hc)

end BSPAux




namespace BSPAux
open LargeBSP.Homog

lemma choice_spec (x : ℕ → ℝ) (N : ℕ) (p : Menu) :
    choice x N p ∈ offered N p ∧
      ∀ k ∈ offered N p, surplus x N p k ≤ surplus x N p (choice x N p) := by
  have hne : (offered N p).Nonempty := ⟨0, by simp [offered]⟩
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image (offered N p) (surplus x N p) hne
  exact Nat.sInf_mem (s := {n : ℕ | n ∈ offered N p ∧
    ∀ k ∈ offered N p, surplus x N p k ≤ surplus x N p n}) ⟨n, hn, hmax⟩

lemma surplus_zero (x : ℕ → ℝ) (N : ℕ) (p : Menu) : surplus x N p 0 = 0 := by
  simp [surplus, price, V_zero]

/-- Pathwise: the profit of any menu is at most `Σ (x_i - c_i)^+`. -/
lemma profit_le_pos (c x : ℕ → ℝ) (N : ℕ) (p : Menu) :
    profit c x N p ≤ ∑ i ∈ Finset.range N, max (x i - c i) 0 := by
  have hnn : 0 ≤ ∑ i ∈ Finset.range N, max (x i - c i) 0 :=
    Finset.sum_nonneg fun i _ => le_max_right _ _
  unfold profit
  split_ifs with h0
  · exact hnn
  obtain ⟨hmem, hmax⟩ := choice_spec x N p
  have h1 := hmax 0 (by simp [offered])
  rw [surplus_zero, surplus] at h1
  set n := choice x N p
  have h2 : V x N n - cost c x N n = ∑ i ∈ topSet x N n, (x i - c i) := by
    rw [V, cost, Finset.sum_sub_distrib]
  have h3 : ∑ i ∈ topSet x N n, (x i - c i) ≤ ∑ i ∈ topSet x N n, max (x i - c i) 0 :=
    Finset.sum_le_sum fun i _ => le_max_left _ _
  have h4 : ∑ i ∈ topSet x N n, max (x i - c i) 0 ≤ ∑ i ∈ Finset.range N, max (x i - c i) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (topSet_subset_range x N n)
      (fun i _ _ => le_max_right _ _)
  linarith

lemma isBSPMenu_top : IsBSPMenu (fun _ => ⊤) := by
  intro n r h; exact absurd h (WithTop.top_ne_coe)

section Profit
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X : ℕ → Ω → ℝ)

lemma PPD_nonneg (c : ℕ → ℝ) (N : ℕ) : 0 ≤ PPD P X c N :=
  Finset.sum_nonneg fun i _ => integral_nonneg fun ω => le_max_right _ _

lemma expProfit_le_PPD (c : ℕ → ℝ) (hint : ∀ i, Integrable (fun ω => max (X i ω - c i) 0) P)
    (N : ℕ) (p : Menu) : expProfit P X c N p ≤ PPD P X c N := by
  unfold expProfit
  by_cases hI : Integrable (fun ω => profit c (fun n => X n ω) N p) P
  · rw [PPD, ← integral_finsetSum _ (fun i _ => hint i)]
    exact integral_mono hI (integrable_finsetSum _ (fun i _ => hint i))
      (fun ω => profit_le_pos c (fun n => X n ω) N p)
  · rw [integral_undef hI]; exact PPD_nonneg P X c N

lemma optProfit_le_PPD (c : ℕ → ℝ) (hint : ∀ i, Integrable (fun ω => max (X i ω - c i) 0) P)
    (N : ℕ) : optProfit P X c N ≤ PPD P X c N := by
  have : Nonempty {p : Menu // IsBSPMenu p} := ⟨⟨fun _ => ⊤, isBSPMenu_top⟩⟩
  exact ciSup_le fun p => expProfit_le_PPD P X c hint N p.1

lemma le_optProfit (c : ℕ → ℝ) (hint : ∀ i, Integrable (fun ω => max (X i ω - c i) 0) P)
    (N : ℕ) (p : Menu) (hp : IsBSPMenu p) : expProfit P X c N p ≤ optProfit P X c N :=
  le_ciSup (f := fun p : {p : Menu // IsBSPMenu p} => expProfit P X c N p.1)
    ⟨PPD P X c N, by rintro _ ⟨q, rfl⟩; exact expProfit_le_PPD P X c hint N q.1⟩ ⟨p, hp⟩

end Profit

lemma offered_single {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) (q : ℝ) :
    offered N (singleSizeMenu m q) = {0, m} := by
  have h : (Finset.Icc 1 N).filter (fun n => singleSizeMenu m q n ≠ ⊤) = {m} := by
    ext n
    rw [Finset.mem_filter, Finset.mem_singleton, Finset.mem_Icc]
    unfold singleSizeMenu
    constructor
    · intro h; by_contra hn; rw [if_neg hn] at h; exact h.2 rfl
    · intro hn; subst hn; rw [if_pos rfl]; exact ⟨⟨hm1, hmN⟩, WithTop.coe_ne_top⟩
  unfold offered
  rw [h]

lemma profit_single (c : ℝ) (x : ℕ → ℝ) {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) (q : ℝ) :
    profit (fun _ => c) x N (singleSizeMenu m q) =
      if q < V x N m then q - m * c else 0 := by
  have hoff := offered_single hm1 hmN q
  have hm0 : m ≠ 0 := by omega
  have hpm : price (singleSizeMenu m q) m = q := by simp [price, singleSizeMenu, hm0]
  have hsm : surplus x N (singleSizeMenu m q) m = V x N m - q := by rw [surplus, hpm]
  have hs0 := surplus_zero x N (singleSizeMenu m q)
  have hcost : cost (fun _ => c) x N m = m * c := by rw [cost_const, min_eq_left hmN]
  unfold profit
  by_cases hq : q < V x N m
  · have hch : choice x N (singleSizeMenu m q) = m := by
      have hset : {n : ℕ | n ∈ offered N (singleSizeMenu m q) ∧
          ∀ k ∈ offered N (singleSizeMenu m q),
            surplus x N (singleSizeMenu m q) k ≤ surplus x N (singleSizeMenu m q) n} = {m} := by
        ext n
        simp only [hoff, Finset.mem_insert, Finset.mem_singleton, Set.mem_ofPred_eq,
          Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
        constructor
        · rintro ⟨h | h, h1, h2⟩
          · subst h; rw [hs0, hsm] at h2; linarith
          · exact h
        · rintro rfl; refine ⟨Or.inr rfl, ?_, le_rfl⟩; rw [hs0, hsm]; linarith
      unfold choice; rw [hset, csInf_singleton]
    rw [hch, if_neg hm0, if_pos hq, hpm, hcost]
  · have hch : choice x N (singleSizeMenu m q) = 0 := by
      apply Nat.eq_zero_of_le_zero
      apply Nat.sInf_le
      simp only [hoff, Finset.mem_insert, Finset.mem_singleton, Set.mem_ofPred_eq,
        forall_eq_or_imp, forall_eq, true_or, true_and]
      refine ⟨le_rfl, ?_⟩
      rw [hs0, hsm]; linarith
    rw [hch, if_pos rfl, if_neg hq]

end BSPAux




namespace BSPAux
open LargeBSP.Homog

lemma expProfit_single {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (c : ℝ) {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N)
    (q : ℝ) :
    expProfit P X (fun _ => c) N (singleSizeMenu m q) =
      (q - m * c) * P.real {ω | q < V (fun n => X n ω) N m} := by
  unfold expProfit
  simp_rw [profit_single c _ hm1 hmN q]
  have : (fun ω => if q < V (fun n => X n ω) N m then q - m * c else 0) =
      {ω | q < V (fun n => X n ω) N m}.indicator (fun _ => q - m * c) := by
    funext ω; simp [Set.indicator_apply]
  rw [this, integral_indicator_const _ (measurableSet_lt measurable_const (measurable_V hXm N m)),
    smul_eq_mul, mul_comm]

lemma isBSPMenu_single (m : ℕ) {q : ℝ} (hq : 0 ≤ q) : IsBSPMenu (singleSizeMenu m q) := by
  intro n r h
  unfold singleSizeMenu at h
  split_ifs at h with hn
  · rw [← WithTop.coe_eq_coe.1 h]; exact hq
  · exact absurd h WithTop.top_ne_coe

/-- Lower bound: the single size `⌊N t⌋` at price `N (v - δ)` gives, eventually,
`E[π]/N > v - t c - η`. -/
lemma optProfit_lower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (c : ℝ) (hc : 0 ≤ c)
    (hint : ∀ i, Integrable (fun ω => max (X i ω - c) 0) P)
    {t v : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (hV : TendstoInMeasure P (fun (N : ℕ) ω => Vbar (fun n => X n ω) N t) atTop (fun _ => v))
    (hLpos : 0 < v - t * c) :
    ∀ η > 0, ∀ᶠ N : ℕ in atTop, v - t * c - η < optProfit P X (fun _ => c) N / N := by
  intro η hη
  set L := v - t * c with hL
  set η' := min η L with hη'
  have hη'0 : 0 < η' := lt_min hη hLpos
  have hη'L : η' ≤ L := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  set δ := η' / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set θ := η' / (4 * L) with hθ
  have hθ0 : 0 < θ := by positivity
  have hLθ : L * θ = η' / 4 := by rw [hθ]; field_simp
  have hbad := tim_iff.1 hV δ hδ0
  have hbadR : Tendsto (fun N : ℕ => P.real {ω | δ ≤ |Vbar (fun n => X n ω) N t - v|}) atTop
      (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hbad
    exact this
  have hN1 := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually (gt_mem_nhds ht.1)
  filter_upwards [hbadR.eventually (gt_mem_nhds hθ0), hN1, eventually_ne_atTop 0]
    with N hNbad hN1 hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hNt : 1 < N * t := by rw [div_lt_iff₀ hNpos] at hN1; linarith
  set m := ⌊(N : ℝ) * t⌋₊ with hm
  have hm1' : (m : ℝ) ≤ N * t := Nat.floor_le (by nlinarith [ht.1])
  have hm1 : 1 ≤ m := by
    rw [hm]; apply Nat.le_floor; push_cast; linarith
  have hmN : m ≤ N := by
    have : (m : ℝ) ≤ N := le_trans hm1' (by nlinarith [ht.2])
    exact_mod_cast this
  have hvL : L ≤ v := by have := mul_nonneg ht.1.le hc; linarith
  set q := (N : ℝ) * (v - δ) with hq
  have hq0 : 0 ≤ q := by
    apply mul_nonneg hNpos.le
    have : δ < L := by linarith
    linarith
  have hexp := expProfit_single P X hXm c hm1 hmN q
  have hopt := le_optProfit P X (fun _ => c) hint N (singleSizeMenu m q) (isBSPMenu_single m hq0)
  -- probability of purchase
  set bad := {ω | δ ≤ |Vbar (fun n => X n ω) N t - v|} with hbad_def
  have hbadm : MeasurableSet bad := by
    apply measurableSet_le measurable_const
    exact (((measurable_V hXm N m).div_const _).sub_const _).abs
  have hsub : badᶜ ⊆ {ω | q < V (fun n => X n ω) N m} := by
    intro ω hω
    simp only [hbad_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    have h1 := (abs_lt.1 hω).1
    have hVb : Vbar (fun n => X n ω) N t = V (fun n => X n ω) N m / N := rfl
    rw [hVb] at h1
    have h2 : v - δ < V (fun n => X n ω) N m / N := by linarith
    rw [lt_div_iff₀ hNpos] at h2
    rw [hq]; linarith
  have hgood : 1 - P.real bad ≤ P.real {ω | q < V (fun n => X n ω) N m} := by
    rw [← probReal_compl_eq_one_sub hbadm]; exact measureReal_mono hsub
  have hgood' : 1 - θ ≤ P.real {ω | q < V (fun n => X n ω) N m} := by linarith
  have hfac : L - δ ≤ (q - m * c) / N := by
    rw [le_div_iff₀ hNpos, hq]
    have : (m : ℝ) * c ≤ N * t * c := mul_le_mul_of_nonneg_right hm1' hc
    nlinarith
  have hLδ : 0 ≤ L - δ := by linarith
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]; linarith
  have hprod : (L - δ) * (1 - θ) ≤ expProfit P X (fun _ => c) N (singleSizeMenu m q) / N := by
    rw [hexp, mul_div_right_comm]
    exact mul_le_mul hfac hgood' (by linarith) (le_trans hLδ hfac)
  have hopt' : expProfit P X (fun _ => c) N (singleSizeMenu m q) / N ≤
      optProfit P X (fun _ => c) N / N := div_le_div_of_nonneg_right hopt hNpos.le
  have : (L - δ) * (1 - θ) ≥ L - δ - L * θ := by nlinarith
  rw [hLθ] at this
  linarith

end BSPAux




namespace BSPAux
open LargeBSP.Homog

lemma tim_cbar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ)
    (hc : 0 ≤ c) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    TendstoInMeasure P (fun (N : ℕ) ω => cbar (fun _ => c) (fun n => X n ω) N t) atTop
      (fun _ => t * c) := by
  apply tim_const_of
  intro ε hε
  filter_upwards [eventually_ne_atTop 0,
    (tendsto_const_div_atTop_nhds_zero_nat c).eventually (gt_mem_nhds hε)] with N hN hN' ω
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set m := ⌊(N : ℝ) * t⌋₊ with hm
  have hm1 : (m : ℝ) ≤ N * t := Nat.floor_le (by nlinarith [ht.1])
  have hm2 : (N : ℝ) * t < m + 1 := Nat.lt_floor_add_one _
  have hmN : m ≤ N := by
    have : (m : ℝ) ≤ N := le_trans hm1 (by nlinarith [ht.2])
    exact_mod_cast this
  unfold cbar
  rw [cost_const, ← hm, min_eq_left hmN]
  have hup : (m : ℝ) * c / N ≤ t * c := by
    rw [div_le_iff₀ hNpos]; nlinarith
  have hlo : t * c - c / N ≤ (m : ℝ) * c / N := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hNpos]; nlinarith
  rw [abs_lt]; constructor <;> linarith

lemma G_pos {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν1 : Integrable id ν) {c : ℝ}
    (h : cdf ν c < 1) : 0 < G ν c := by
  unfold G
  have hint : Integrable (fun x => max (x - c) 0) ν :=
    Integrable.pos_part (hν1.sub (integrable_const c))
  rw [integral_pos_iff_support_of_nonneg (f := fun x => max (x - c) 0)
    (fun x => le_max_right _ _) hint]
  have hsupp : Function.support (fun x : ℝ => max (x - c) 0) = Set.Ioi c := by
    ext x
    simp only [Function.mem_support, Set.mem_Ioi]
    constructor
    · intro hx; by_contra h'; push Not at h'; exact hx (max_eq_right (by linarith))
    · intro hx; rw [max_eq_left (by linarith)]; linarith
  rw [hsupp, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf]
  rw [tsub_pos_iff_lt, ENNReal.ofReal_lt_one]
  exact h

theorem theorem_2_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    (hUI : UniformIntegrable X 1 P)
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν))
    (c : ℝ) (hc : 0 ≤ c) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure P
      (fun (N : ℕ) ω => Vbar (fun n => X n ω) N t) atTop (fun _ => Vlim ν t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure P
      (fun (N : ℕ) ω => cbar (fun _ => c) (fun n => X n ω) N t) atTop (fun _ => t * c)) ∧
    (tstar ν c ∈ Set.Icc (0 : ℝ) 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Vlim ν t - t * c ≤ Vlim ν (tstar ν c) - tstar ν c * c) ∧
      (ContinuousAt (cdf ν) c → tstar ν c = 1 - cdf ν c)) ∧
    (cdf ν c < 1 →
      Tendsto (fun N : ℕ => optProfit P X (fun _ => c) N / PPD P X (fun _ => c) N) atTop
        (𝓝 1)) := by
  refine ⟨fun t ht => tim_Vbar P X hX0 ν hν0 hν1 hA1 hWLLN ht,
    fun t ht => tim_cbar P X c hc ht,
    ⟨tstar_mem c, tstar_max hν0 hν1 c, tstar_cont hν0 c⟩, ?_⟩
  intro hF
  have hG := G_pos hν1 hF
  have hL : G ν c = Vlim ν (tstar ν c) - tstar ν c * c := G_eq_tstar hν0 hν1 c
  have hint : ∀ i, Integrable (fun ω => max (X i ω - c) 0) P := integrable_pos_X hUI c
  have hPPD := PPD_div_tendsto_G P X hXm hX0 ν hν0 hν1 hA1 hUI hWLLN c hc
  have htm := tstar_mem (ν := ν) c
  have ht0 : 0 < tstar ν c := by
    rcases eq_or_lt_of_le htm.1 with h | h
    · rw [← h] at hL; simp [Vlim] at hL; linarith
    · exact h
  have hlow := optProfit_lower P X hXm c hc hint ⟨ht0, htm.2⟩
    (tim_Vbar P X hX0 ν hν0 hν1 hA1 hWLLN htm) (by rw [← hL]; exact hG)
  have hopt : Tendsto (fun N : ℕ => optProfit P X (fun _ => c) N / N) atTop (𝓝 (G ν c)) := by
    rw [tendsto_order]; constructor
    · intro a ha
      have := hlow (G ν c - a) (by linarith)
      rw [← hL] at this
      filter_upwards [this] with N hN; linarith
    · intro b hb
      filter_upwards [hPPD.eventually (eventually_lt_nhds hb)] with N hN
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right
        (optProfit_le_PPD P X (fun _ => c) hint N) (Nat.cast_nonneg N)) hN
  have key := hopt.div hPPD hG.ne'
  rw [div_self hG.ne'] at key
  apply key.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (by exact_mod_cast hN)]

end BSPAux



open LargeBSP.Homog in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (Vl : ℝ → ℝ) (t₀ : ℝ)
    (g : ℕ → ℝ) (hg0 : ∀ᶠ N in atTop, 0 < g N)
    (hgω : Tendsto (fun N : ℕ =>
      (∫⁻ ω, ENNReal.ofReal ((V (fun n => X n ω) N ⌊(N : ℝ) * t₀⌋₊ - N * Vl t₀) ^ 2) ∂P) /
        ENNReal.ofReal (g N ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (P {ω | (N : ℝ) * Vl t₀ - g N < V (fun n => X n ω) N ⌊(N : ℝ) * t₀⌋₊}).toReal)
      atTop (𝓝 1) := by
  set A : ℕ → Set Ω := fun N => {ω | (N : ℝ) * Vl t₀ - g N < V (fun n => X n ω) N ⌊(N : ℝ) * t₀⌋₊}
    with hA
  have hAm : ∀ N, MeasurableSet (A N) := fun N =>
    measurableSet_lt measurable_const (BSPAux.measurable_V hXm N _)
  have hc : Tendsto (fun N => P (A N)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgω
      (Eventually.of_forall fun N => zero_le')
    filter_upwards [hg0] with N hN
    have hg2 : ENNReal.ofReal (g N ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    refine le_trans (measure_mono ?_) (meas_ge_le_lintegral_div
      (((BSPAux.measurable_V hXm N _).sub measurable_const).pow_const 2).ennreal_ofReal.aemeasurable
      hg2 ENNReal.ofReal_ne_top)
    intro ω hω
    simp only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω ⊢
    apply ENNReal.ofReal_le_ofReal
    simp only [Pi.sub_apply]
    nlinarith
  have h1 : ∀ N, (P (A N)).toReal = 1 - (P (A N)ᶜ).toReal := by
    intro N
    rw [prob_compl_eq_one_sub (hAm N), ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
    ring
  show Tendsto (fun N => (P (A N)).toReal) atTop (𝓝 1)
  simp_rw [h1]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
