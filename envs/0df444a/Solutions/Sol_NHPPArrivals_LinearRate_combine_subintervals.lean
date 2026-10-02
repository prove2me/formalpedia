-- Prove2me | solution 1 for NHPPArrivals.LinearRate.combine_subintervals
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:57:39.050881+00:00
-- url     : https://prove2.me/submissions/3dc8aa52-9b9e-4782-b505-397bcfb15eae

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf

set_option autoImplicit false

open MeasureTheory in
theorem pa3c_pos (lam : ℝ → ℝ) (T : ℝ)
    (hint : IntervalIntegrable lam volume 0 T) (hnn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ lam s)
    (hfin : {s ∈ Set.Icc (0:ℝ) T | lam s = 0}.Finite) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ T) : 0 < ∫ x in a..b, lam x := by
  have hsub : Set.uIcc a b ⊆ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hab.le, Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc ha hb
  have hi : IntervalIntegrable lam volume a b := hint.mono_set hsub
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' _ hi]
  · refine ⟨hab, ?_⟩
    have hZ : volume {s ∈ Set.Icc (0:ℝ) T | lam s = 0} = 0 := hfin.measure_zero volume
    have h1 : Set.Ioc a b \ {s ∈ Set.Icc (0:ℝ) T | lam s = 0} ⊆
        Function.support lam ∩ Set.Ioc a b := by
      intro x hx
      refine ⟨?_, hx.1⟩
      intro h0
      exact hx.2 ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, h0⟩
    calc (0:ENNReal) < volume (Set.Ioc a b) := by
          rw [Real.volume_Ioc]; exact ENNReal.ofReal_pos.mpr (by linarith)
      _ = volume (Set.Ioc a b \ {s ∈ Set.Icc (0:ℝ) T | lam s = 0}) :=
          (measure_sdiff_null hZ).symm
      _ ≤ _ := measure_mono h1
  · rw [Set.uIoc_of_le hab.le]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    exact hnn x ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem pa3c_reidx (g : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, g j = ∑ m ∈ Finset.range k, g (m + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

open MeasureTheory NHPPArrivals.LinearRate in
theorem pa3c_meas (lam : ℝ → ℝ) (T : ℝ) (hint : IntervalIntegrable lam volume 0 T)
    (hnn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ lam s) (hΛ : 0 < cumRate lam T) (hT : 0 ≤ T)
    (s : Set ℝ) (hs : MeasurableSet s) :
    arrivalLaw lam T s
      = ENNReal.ofReal ((∫ x in s ∩ Set.Icc 0 T, lam x) / cumRate lam T) := by
  unfold arrivalLaw
  rw [withDensity_apply _ hs, Measure.restrict_restrict hs]
  have hI : IntegrableOn lam (Set.Icc 0 T) volume := by
    exact (integrableOn_Icc_iff_integrableOn_Ioc (f := lam) (a := 0) (b := T)).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hint)
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div]
  · exact (hI.mono_set Set.inter_subset_right).div_const _
  · refine (ae_restrict_iff' (hs.inter measurableSet_Icc)).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    exact div_nonneg (hnn x hx.2) hΛ.le

open MeasureTheory NHPPArrivals.LinearRate in
theorem pa3c_diff (lam : ℝ → ℝ) (T : ℝ) (hint : IntervalIntegrable lam volume 0 T)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    cumRate lam b - cumRate lam a = ∫ x in a..b, lam x := by
  have hsub : ∀ c : ℝ, 0 ≤ c → c ≤ T → Set.uIcc 0 c ⊆ Set.uIcc 0 T := by
    intro c hc0 hcT
    rw [Set.uIcc_of_le hc0, Set.uIcc_of_le (hc0.trans hcT)]
    exact Set.Icc_subset_Icc le_rfl hcT
  unfold cumRate
  exact intervalIntegral.integral_interval_sub_left
    (hint.mono_set (hsub b (ha.trans hab) hb)) (hint.mono_set (hsub a ha (hab.trans hb)))

open MeasureTheory NHPPArrivals.LinearRate in
theorem pa3c_Ico (lam : ℝ → ℝ) (T : ℝ) (hint : IntervalIntegrable lam volume 0 T)
    (hnn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ lam s) (hΛ : 0 < cumRate lam T) (hT : 0 ≤ T)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (arrivalLaw lam T).real (Set.Ico a b) = (cumRate lam b - cumRate lam a) / cumRate lam T := by
  rw [measureReal_def, pa3c_meas lam T hint hnn hΛ hT _ measurableSet_Ico,
    Set.inter_eq_left.mpr (show Set.Ico a b ⊆ Set.Icc 0 T from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩),
    integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, ← pa3c_diff lam T hint a b ha hab hb]
  apply ENNReal.toReal_ofReal
  apply div_nonneg _ hΛ.le
  rw [pa3c_diff lam T hint a b ha hab hb]
  exact intervalIntegral.integral_nonneg hab
    (fun x hx => hnn x ⟨by linarith [hx.1], by linarith [hx.2]⟩)

open MeasureTheory NHPPArrivals.LinearRate in
theorem solution (lam : ℝ → ℝ) (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k)
    (hint : IntervalIntegrable lam volume 0 T) (hnn : ∀ s ∈ Set.Icc (0:ℝ) T, 0 ≤ lam s)
    (hfin : {s ∈ Set.Icc (0:ℝ) T | lam s = 0}.Finite) :
    IsProbabilityMeasure (arrivalLaw lam T) ∧
    (∀ j ∈ Finset.Icc 1 k, 0 ≤ weight lam T k j) ∧
    ∑ j ∈ Finset.Icc 1 k, weight lam T k j = 1 ∧
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      (arrivalLaw lam T).real {x | Int.fract ((k:ℝ) * x / T) ≤ t} = mixCdf lam T k t := by
  have hΛ0 : 0 < ∫ x in (0:ℝ)..T, lam x := pa3c_pos lam T hint hnn hfin 0 T le_rfl hT le_rfl
  have hΛ : 0 < cumRate lam T := hΛ0
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = T / k := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hT hkR
  have hkδ : (k:ℝ) * δ = T := by rw [hδ]; field_simp
  have hprob : IsProbabilityMeasure (arrivalLaw lam T) := by
    constructor
    rw [pa3c_meas lam T hint hnn hΛ hT.le _ MeasurableSet.univ, Set.univ_inter,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
    change ENNReal.ofReal (cumRate lam T / cumRate lam T) = 1
    rw [div_self hΛ.ne', ENNReal.ofReal_one]
  have hD : ∀ m : ℕ, m < k →
      0 < cumRate lam ((m:ℝ) * δ + δ) - cumRate lam ((m:ℝ) * δ) := by
    intro m hm
    have hm' : (m:ℝ) + 1 ≤ k := by exact_mod_cast hm
    have h1 : ((m:ℝ) + 1) * δ ≤ (k:ℝ) * δ := mul_le_mul_of_nonneg_right hm' hδpos.le
    rw [pa3c_diff lam T hint _ _ (by positivity) (by linarith) (by nlinarith)]
    exact pa3c_pos lam T hint hnn hfin _ _ (by positivity) (by linarith) (by nlinarith)
  have hw : ∀ m : ℕ, weight lam T k (m + 1)
      = (cumRate lam ((m:ℝ) * δ + δ) - cumRate lam ((m:ℝ) * δ)) / cumRate lam T := by
    intro m
    unfold weight
    rw [show ((m + 1 : ℕ) : ℝ) * T / k = (m:ℝ) * δ + δ by rw [hδ]; push_cast; ring,
      show (((m + 1 : ℕ) : ℝ) - 1) * T / k = (m:ℝ) * δ by rw [hδ]; push_cast; ring]
  refine ⟨hprob, ?_, ?_, ?_⟩
  · intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hj2 := (Finset.mem_Icc.mp hj).2
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [hw]
    exact div_nonneg (hD m (by omega)).le hΛ.le
  · rw [pa3c_reidx (fun j => weight lam T k j) k]
    simp only [hw]
    rw [← Finset.sum_div]
    have htel := Finset.sum_range_sub (fun m : ℕ => cumRate lam ((m:ℝ) * δ)) k
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Nat.cast_zero, zero_mul] at htel
    rw [htel, hkδ]
    have h0 : cumRate lam 0 = 0 := by unfold cumRate; simp
    rw [h0, sub_zero, div_self hΛ.ne']
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have := hprob
    let I : ℕ → Set ℝ := fun m => Set.Ico ((m:ℝ) * δ) ((m:ℝ) * δ + t * δ)
    let U : Set ℝ := ⋃ m ∈ Finset.range k, I m
    let E : Set ℝ :=
      insert T ((((Finset.range k).image (fun m : ℕ => (m:ℝ) * δ + t * δ)) : Finset ℝ) : Set ℝ)
    have hyx : ∀ x : ℝ, (k:ℝ) * x / T = x / δ := by
      intro x; rw [hδ]; field_simp
    have hUS : U ⊆ {x | Int.fract ((k:ℝ) * x / T) ≤ t} := by
      intro x hx
      simp only [U, I, Set.mem_iUnion, Finset.mem_range, Set.mem_Ico, exists_prop] at hx
      obtain ⟨m, _, h1, h2⟩ := hx
      simp only [Set.mem_ofPred_eq, hyx]
      have hy1 : (m:ℝ) ≤ x / δ := by rw [le_div_iff₀ hδpos]; linarith
      have hy2 : x / δ < m + t := by rw [div_lt_iff₀ hδpos]; linarith
      have hfl : ⌊x / δ⌋ = (m:ℤ) := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      rw [Int.fract, hfl]; push_cast; linarith
    have hSU : {x | Int.fract ((k:ℝ) * x / T) ≤ t} ⊆ U ∪ E ∪ (Set.Icc 0 T)ᶜ := by
      intro x hx
      simp only [Set.mem_ofPred_eq, hyx] at hx
      unfold Int.fract at hx
      by_cases hxI : x ∈ Set.Icc 0 T
      swap
      · exact Or.inr hxI
      by_cases hxT : x = T
      · left; right; rw [hxT]; exact Set.mem_insert T _
      obtain ⟨hx0, hxT'⟩ := hxI
      have hxlt : x < T := lt_of_le_of_ne hxT' hxT
      have hy0 : 0 ≤ x / δ := div_nonneg hx0 hδpos.le
      have hyk : x / δ < k := by rw [div_lt_iff₀ hδpos]; linarith
      have hn0 : 0 ≤ ⌊x / δ⌋ := Int.floor_nonneg.mpr hy0
      have hnle : ((⌊x / δ⌋ : ℤ) : ℝ) ≤ x / δ := Int.floor_le _
      have hnk : ⌊x / δ⌋ < (k:ℤ) := by
        have : ((⌊x / δ⌋ : ℤ) : ℝ) < ((k:ℤ):ℝ) := by push_cast; linarith
        exact_mod_cast this
      obtain ⟨m, hm⟩ : ∃ m : ℕ, ⌊x / δ⌋ = (m:ℤ) := ⟨(⌊x / δ⌋).toNat, (Int.toNat_of_nonneg hn0).symm⟩
      have hmk : m < k := by omega
      rw [hm] at hnle hx
      push_cast at hnle hx
      have hm1 : (m:ℝ) * δ ≤ x := (le_div_iff₀ hδpos).mp hnle
      have hm2 : x ≤ ((m:ℝ) + t) * δ := (div_le_iff₀ hδpos).mp (by linarith)
      rcases lt_or_eq_of_le hm2 with hlt | heq
      · left; left
        simp only [U, I, Set.mem_iUnion, Finset.mem_range, Set.mem_Ico, exists_prop]
        exact ⟨m, hmk, hm1, by linarith⟩
      · left; right
        apply Set.mem_insert_of_mem
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
        exact ⟨m, hmk, by rw [heq]; ring⟩
    have hacc : arrivalLaw lam T ≪ volume := by
      unfold arrivalLaw
      exact (withDensity_absolutelyContinuous _ _).trans
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    have hE0 : arrivalLaw lam T E = 0 :=
      hacc (((Finset.finite_toSet _).insert T).measure_zero volume)
    have hC0 : arrivalLaw lam T (Set.Icc 0 T)ᶜ = 0 := by
      rw [pa3c_meas lam T hint hnn hΛ hT.le _ measurableSet_Icc.compl]
      simp
    have hSeq : arrivalLaw lam T {x | Int.fract ((k:ℝ) * x / T) ≤ t} = arrivalLaw lam T U := by
      apply le_antisymm _ (measure_mono hUS)
      calc arrivalLaw lam T {x | Int.fract ((k:ℝ) * x / T) ≤ t}
          ≤ arrivalLaw lam T (U ∪ E ∪ (Set.Icc 0 T)ᶜ) := measure_mono hSU
        _ ≤ arrivalLaw lam T (U ∪ E) + arrivalLaw lam T (Set.Icc 0 T)ᶜ := measure_union_le _ _
        _ ≤ arrivalLaw lam T U + arrivalLaw lam T E + arrivalLaw lam T (Set.Icc 0 T)ᶜ := by
          gcongr; exact measure_union_le _ _
        _ = arrivalLaw lam T U := by rw [hE0, hC0, add_zero, add_zero]
    rw [measureReal_def, hSeq, ← measureReal_def]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range k)) I := by
      intro m _ m' _ hne
      show Disjoint (I m) (I m')
      rw [Set.disjoint_left]
      intro x hx hx'
      simp only [I, Set.mem_Ico] at hx hx'
      have htd : t * δ ≤ δ := by nlinarith
      rcases lt_or_gt_of_ne hne with h | h
      · have h' : (m:ℝ) + 1 ≤ m' := by exact_mod_cast h
        nlinarith [mul_le_mul_of_nonneg_right h' hδpos.le]
      · have h' : (m':ℝ) + 1 ≤ m := by exact_mod_cast h
        nlinarith [mul_le_mul_of_nonneg_right h' hδpos.le]
    rw [measureReal_biUnion_finset hdisj (fun m _ => measurableSet_Ico)]
    unfold mixCdf
    rw [pa3c_reidx (fun j => weight lam T k j * subCdf lam T k j t) k]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmk : m < k := Finset.mem_range.mp hm
    have hm' : (m:ℝ) + 1 ≤ k := by exact_mod_cast hmk
    have h1 : ((m:ℝ) + 1) * δ ≤ (k:ℝ) * δ := mul_le_mul_of_nonneg_right hm' hδpos.le
    have htd : t * δ ≤ δ := by nlinarith
    rw [pa3c_Ico lam T hint hnn hΛ hT.le _ _ (by positivity) (by nlinarith) (by nlinarith), hw]
    unfold subCdf subCum
    rw [show (((m + 1 : ℕ) : ℝ) - 1) * T / k = (m:ℝ) * δ by rw [hδ]; push_cast; ring,
      show t * T / k = t * δ by rw [hδ]; ring, show T / (k:ℝ) = δ by rw [hδ]]
    have hDm := (hD m hmk).ne'
    rw [div_mul_div_comm,
      mul_comm (cumRate lam ((m:ℝ) * δ + δ) - cumRate lam ((m:ℝ) * δ)) _,
      mul_div_mul_right _ _ hDm]
