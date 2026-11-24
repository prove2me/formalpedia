-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_positiveDiscount_zeroBarrier_BV
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:25:50.278948+00:00
-- url     : https://prove2.me/submissions/92010029-5d01-49dd-8b0e-6d52f26df852

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace Kyprianou.Ch03

section PositiveDiscountZeroBarrierBV

private lemma bv_min_one_abs_integrableOn
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) :
    IntegrableOn (fun y : ℝ => min (1 : ℝ) |y|) (Iio 0) L.ν := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => min (1 : ℝ) |y|) (L.ν.restrict (Iio 0)) :=
    (continuous_const.min continuous_abs).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral]
  have hsplit : Iio (0 : ℝ) = Iic (-1 : ℝ) ∪ Ioo (-1 : ℝ) 0 := by
    ext y
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro hy
      rcases le_or_gt y (-1) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, hy⟩
    · rintro (h1 | ⟨_, h2⟩)
      · linarith
      · exact h2
  rw [hsplit]
  have h1 : ∫⁻ y in Iic (-1 : ℝ), ‖min (1 : ℝ) |y|‖ₑ ∂L.ν < ⊤ := by
    refine lt_of_le_of_lt ?_ L.ν_integrable
    calc
      ∫⁻ y in Iic (-1 : ℝ), ‖min (1 : ℝ) |y|‖ₑ ∂L.ν
          ≤ ∫⁻ y in Iic (-1 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂L.ν := by
        refine setLIntegral_mono' measurableSet_Iic fun y hy => ?_
        have hy1 : (1 : ℝ) ≤ |y| := by
          rw [abs_of_nonpos (by linarith [mem_Iic.mp hy])]
          linarith [mem_Iic.mp hy]
        have hy2 : (1 : ℝ) ≤ y ^ 2 := by nlinarith [mem_Iic.mp hy]
        have hm1 : min (1 : ℝ) |y| = 1 := min_eq_left hy1
        have hm2 : min (1 : ℝ) (y ^ 2) = 1 := min_eq_left hy2
        rw [hm1, hm2, Real.enorm_eq_ofReal (by norm_num)]
      _ ≤ ∫⁻ y in Set.univ, ENNReal.ofReal (min 1 (y ^ 2)) ∂L.ν := lintegral_mono_set (subset_univ _)
      _ = ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂L.ν := by rw [Measure.restrict_univ]
  have h2 : ∫⁻ y in Ioo (-1 : ℝ) 0, ‖min (1 : ℝ) |y|‖ₑ ∂L.ν < ⊤ := by
    refine lt_of_le_of_lt ?_ hBV.2
    refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
    have hle : min (1 : ℝ) |y| ≤ |y| := min_le_right _ _
    have hnn : 0 ≤ min (1 : ℝ) |y| := le_min zero_le_one (abs_nonneg y)
    rw [Real.enorm_eq_ofReal hnn]
    exact ENNReal.ofReal_le_ofReal hle
  exact lt_of_le_of_lt (lintegral_union_le _ _ _) (ENNReal.add_lt_top.mpr ⟨h1, h2⟩)

private lemma bv_psi_eq_drift_add_integral
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) {θ : ℝ} (hθ : 0 ≤ θ) :
    L.ψ θ = L.drift * θ + ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂L.ν := by
  have hbound := bv_min_one_abs_integrableOn L hBV
  have hexp_int : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1) (Iio 0) L.ν := by
    refine (hbound.const_mul (max 1 θ)).mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub continuous_const).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have hθy : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ hy.le
    have hexp_le : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr hθy
    have h1 : 1 - Real.exp (θ * y) ≤ 1 := by linarith [Real.exp_pos (θ * y)]
    have h2 : 1 - Real.exp (θ * y) ≤ θ * |y| := by
      have hlin := Real.add_one_le_exp (θ * y)
      rw [abs_of_neg hy]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hexp_le), neg_sub]
    by_cases hy1 : |y| ≤ 1
    · rw [min_eq_right hy1]
      exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right 1 θ) (abs_nonneg y))
    · push_neg at hy1
      rw [min_eq_left hy1.le, mul_one]
      exact h1.trans (le_max_left 1 θ)
  have hlin_int : IntegrableOn (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) (Iio 0) L.ν := by
    refine (hbound.const_mul θ).mono' ?_ ?_
    · exact ((continuous_const.mul continuous_id).aestronglyMeasurable.mul
        ((aestronglyMeasurable_const).indicator measurableSet_Ioo))
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      by_cases hmem : y ∈ Ioo (-1 : ℝ) 1
      · simp only [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg hθ]
        have hy1 : |y| ≤ 1 := by
          rw [abs_of_neg hy]; linarith [hmem.1]
        rw [min_eq_right hy1]
      · simp only [Set.indicator_of_notMem hmem, mul_zero, norm_zero]
        exact mul_nonneg hθ (le_min zero_le_one (abs_nonneg y))
  have hind_eq : ∫ y in Iio (0 : ℝ), (θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν =
      θ * ∫ y in Ioo (-1 : ℝ) 0, y ∂L.ν := by
    have hpt : EqOn (fun y : ℝ => θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
        ((Ioo (-1 : ℝ) 0).indicator (fun y => θ * y)) (Iio 0) := by
      intro y hy
      by_cases h1 : -1 < y
      · have hm1 : y ∈ Ioo (-1 : ℝ) 1 := ⟨h1, hy.trans zero_lt_one⟩
        have hm2 : y ∈ Ioo (-1 : ℝ) 0 := ⟨h1, hy⟩
        simp [hm1, hm2]
      · have hm1 : y ∉ Ioo (-1 : ℝ) 1 := fun h => h1 h.1
        have hm2 : y ∉ Ioo (-1 : ℝ) 0 := fun h => h1 h.1
        simp [hm1, hm2]
    rw [setIntegral_congr_fun measurableSet_Iio hpt,
      integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr Ioo_subset_Iio_self,
      integral_const_mul]
  have hsub : ∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν =
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂L.ν) -
        ∫ y in Iio (0 : ℝ), (θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν :=
    integral_sub hexp_int hlin_int
  unfold SpectrallyNegativeLevy.ψ laplaceExponent SpectrallyNegativeLevy.drift
  rw [hBV.1, hsub, hind_eq]
  ring

private lemma bv_psi_le_drift_mul
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) {θ : ℝ} (hθ : 0 ≤ θ) :
    L.ψ θ ≤ L.drift * θ := by
  rw [bv_psi_eq_drift_add_integral L hBV hθ]
  have hnonpos : ∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂L.ν ≤ 0 := by
    refine integral_nonpos_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ hy.le))
  linarith

private lemma bv_X_le_drift_mul_ae
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (t : NNReal) :
    ∀ᵐ ω ∂P, L.X t ω ≤ L.drift * (t : ℝ) := by
  have hstep : ∀ k : ℕ, P {ω : Omega | L.drift * (t : ℝ) + 1 / ((k : ℝ) + 1) < L.X t ω} = 0 := by
    intro k
    let δ : ℝ := 1 / ((k : ℝ) + 1)
    have hδ_pos : 0 < δ := by positivity
    let A : Set Omega := {ω : Omega | L.drift * (t : ℝ) + δ < L.X t ω}
    have hA_meas : MeasurableSet A :=
      measurableSet_lt measurable_const ((L.adapted t).mono (F.le t) le_rfl)
    have hbd : ∀ θ : ℝ, 0 ≤ θ →
        Real.exp (θ * δ) * (P A).toReal ≤ 1 := by
      intro θ hθ
      have h1 : Real.exp (θ * δ) * (P A).toReal ≤
          ∫ ω, Real.exp (θ * (L.X t ω - L.drift * (t : ℝ))) ∂P := by
        have hint : Integrable (fun ω => Real.exp (θ * (L.X t ω - L.drift * (t : ℝ)))) P := by
          have heq : (fun ω => Real.exp (θ * (L.X t ω - L.drift * (t : ℝ)))) =
              fun ω => Real.exp (-(θ * L.drift * (t : ℝ))) * Real.exp (θ * L.X t ω) := by
            ext ω; rw [← Real.exp_add]; congr 1; ring
          rw [heq]
          exact (L.laplace t θ hθ).1.const_mul _
        have hconst : Real.exp (θ * δ) * (P A).toReal =
            ∫ ω in A, Real.exp (θ * δ) ∂P := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
        rw [hconst]
        calc
          ∫ ω in A, Real.exp (θ * δ) ∂P
              ≤ ∫ ω in A, Real.exp (θ * (L.X t ω - L.drift * (t : ℝ))) ∂P := by
            refine setIntegral_mono_on (integrableOn_const (hs := measure_ne_top P A))
              hint.integrableOn hA_meas fun ω hω => ?_
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [mem_setOf.mp hω]) hθ)
          _ ≤ ∫ ω, Real.exp (θ * (L.X t ω - L.drift * (t : ℝ))) ∂P :=
            setIntegral_le_integral hint (ae_of_all _ fun ω => (Real.exp_pos _).le)
      have h2 : ∫ ω, Real.exp (θ * (L.X t ω - L.drift * (t : ℝ))) ∂P ≤ 1 := by
        have heq : (fun ω => Real.exp (θ * (L.X t ω - L.drift * (t : ℝ)))) =
            fun ω => Real.exp (-(θ * L.drift * (t : ℝ))) * Real.exp (θ * L.X t ω) := by
          ext ω; rw [← Real.exp_add]; congr 1; ring
        rw [heq, integral_const_mul, (L.laplace t θ hθ).2, ← Real.exp_add]
        have hψ : L.ψ θ ≤ L.drift * θ := bv_psi_le_drift_mul L hBV hθ
        have hexp_le : -(θ * L.drift * (t : ℝ)) + (t : ℝ) * L.ψ θ ≤ 0 := by
          have : (t : ℝ) * L.ψ θ ≤ (t : ℝ) * (L.drift * θ) :=
            mul_le_mul_of_nonneg_left hψ (NNReal.coe_nonneg t)
          linarith
        exact Real.exp_le_one_iff.mpr hexp_le
      exact h1.trans h2
    have htoReal : (P A).toReal = 0 := by
      by_contra hne
      have hpos : 0 < (P A).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
      obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log (1 / (P A).toReal) + 1) / δ)
      have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hlt : 1 < Real.exp ((N : ℝ) * δ) * (P A).toReal := by
        have h1 : Real.log (1 / (P A).toReal) < (N : ℝ) * δ := by
          have := (div_lt_iff₀ hδ_pos).mp hN
          linarith
        have h2 : 1 / (P A).toReal < Real.exp ((N : ℝ) * δ) := by
          have := Real.exp_lt_exp.mpr h1
          rwa [Real.exp_log (div_pos one_pos hpos)] at this
        have h3 := (div_lt_iff₀ hpos).mp h2
        linarith
      linarith [hbd (N : ℝ) hN_nn]
    exact (ENNReal.toReal_eq_zero_iff (P A)).mp htoReal |>.resolve_right (measure_ne_top P A)
  have hunion : P (⋃ k : ℕ, {ω : Omega | L.drift * (t : ℝ) + 1 / ((k : ℝ) + 1) < L.X t ω}) = 0 :=
    measure_iUnion_null hstep
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hunion
  simp only [mem_ofPred_eq, not_le] at hω
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hω)
  refine mem_iUnion.mpr ⟨k, ?_⟩
  show L.drift * (t : ℝ) + 1 / ((k : ℝ) + 1) < L.X t ω
  linarith

private abbrev NonnegRat := {q : ℚ // 0 ≤ q}

private noncomputable def nonnegRatToNN (q : NonnegRat) : NNReal :=
  Real.toNNReal (q.1 : ℝ)

private lemma nonnegRatToNN_coe (q : NonnegRat) : (nonnegRatToNN q : ℝ) = (q.1 : ℝ) :=
  Real.coe_toNNReal _ (Rat.cast_nonneg.mpr q.2)

private lemma bv_drift_pos_of_not_antitone
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ ω : Omega ∂ P, Antitone (fun t : NNReal => L.X t ω)))
    (hBV : L.BoundedVariation) :
    0 < L.drift := by
  by_contra hle
  push_neg at hle
  have hpair_ae : ∀ p : {p : NonnegRat × NonnegRat // p.1.1 ≤ p.2.1},
      ∀ᵐ ω ∂P, L.X (nonnegRatToNN p.1.2) ω ≤ L.X (nonnegRatToNN p.1.1) ω := by
    intro p
    let s : NNReal := nonnegRatToNN p.1.1
    let t : NNReal := nonnegRatToNN p.1.2
    have hst : s ≤ t := by
      rw [← NNReal.coe_le_coe, nonnegRatToNN_coe, nonnegRatToNN_coe]
      exact Rat.cast_le.mpr p.2
    have hts_ae : ∀ᵐ ω ∂P, L.X (t - s) ω ≤ 0 := by
      filter_upwards [bv_X_le_drift_mul_ae L hBV (t - s)] with ω hω
      exact hω.trans (mul_nonpos_of_nonpos_of_nonneg hle (NNReal.coe_nonneg (t - s)))
    have hnull_ts : P ((L.X (t - s)) ⁻¹' Ioi (0 : ℝ)) = 0 := by
      rw [ae_iff] at hts_ae
      have heq : (L.X (t - s)) ⁻¹' Ioi (0 : ℝ) = {ω | ¬ L.X (t - s) ω ≤ 0} := by
        ext ω; simp [not_le]
      rw [heq]; exact hts_ae
    have hid := L.stationaryIncrements s t hst
    have hnull_inc : P ((fun ω => L.X t ω - L.X s ω) ⁻¹' Ioi (0 : ℝ)) = 0 := by
      rw [hid.measure_mem_eq measurableSet_Ioi, hnull_ts]
    rw [ae_iff]
    have heq : {ω | ¬ L.X t ω ≤ L.X s ω} = (fun ω => L.X t ω - L.X s ω) ⁻¹' Ioi (0 : ℝ) := by
      ext ω; simp [not_le, sub_pos]
    rw [heq]; exact hnull_inc
  have hall_rat : ∀ᵐ ω ∂P, ∀ p : {p : NonnegRat × NonnegRat // p.1.1 ≤ p.2.1},
      L.X (nonnegRatToNN p.1.2) ω ≤ L.X (nonnegRatToNN p.1.1) ω :=
    ae_all_iff.mpr hpair_ae
  refine hNotDecreasing ?_
  filter_upwards [hall_rat] with ω hω
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_rfl
  · have hlim_s : ∃ rs : ℕ → NonnegRat,
        (∀ n, s ≤ nonnegRatToNN (rs n) ∧ nonnegRatToNN (rs n) ≤ t) ∧
        Tendsto (fun n => nonnegRatToNN (rs n)) atTop (𝓝[≥] s) := by
      have hex : ∀ n : ℕ, ∃ q : NonnegRat,
          s ≤ nonnegRatToNN q ∧ nonnegRatToNN q ≤ t ∧
          (nonnegRatToNN q : ℝ) < (s : ℝ) + 1 / ((n : ℝ) + 1) := by
        intro n
        let hi : ℝ := min (t : ℝ) ((s : ℝ) + 1 / ((n : ℝ) + 1))
        have hlt_hi : (s : ℝ) < hi :=
          lt_min (NNReal.coe_lt_coe.mpr hlt) (lt_add_of_pos_right _ (by positivity))
        obtain ⟨q, hsq, hqhi⟩ := exists_rat_btwn hlt_hi
        have hq_nn : (0 : ℚ) ≤ q := by
          have : (0 : ℝ) ≤ (q : ℝ) := (NNReal.coe_nonneg s).trans hsq.le
          exact_mod_cast this
        refine ⟨⟨q, hq_nn⟩, ?_, ?_, ?_⟩
        · rw [← NNReal.coe_le_coe, nonnegRatToNN_coe]; exact hsq.le
        · rw [← NNReal.coe_le_coe, nonnegRatToNN_coe]
          exact hqhi.le.trans (min_le_left _ _)
        · rw [nonnegRatToNN_coe]
          exact hqhi.trans_le (min_le_right _ _)
      choose rs hrs_ge hrs_le hrs_lt using hex
      refine ⟨rs, fun n => ⟨hrs_ge n, hrs_le n⟩, ?_⟩
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hrs_ge⟩
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hrs_ge n)))]
      have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
      linarith [hrs_lt n, hN]
    have hlim_t : ∃ qs : ℕ → NonnegRat,
        (∀ n, t ≤ nonnegRatToNN (qs n)) ∧
        Tendsto (fun n => nonnegRatToNN (qs n)) atTop (𝓝[≥] t) := by
      have hex : ∀ n : ℕ, ∃ q : NonnegRat,
          t ≤ nonnegRatToNN q ∧ (nonnegRatToNN q : ℝ) < (t : ℝ) + 1 / ((n : ℝ) + 1) := by
        intro n
        obtain ⟨q, htq, hqhi⟩ := exists_rat_btwn (lt_add_of_pos_right (t : ℝ) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
        have hq_nn : (0 : ℚ) ≤ q := by
          have : (0 : ℝ) ≤ (q : ℝ) := (NNReal.coe_nonneg t).trans htq.le
          exact_mod_cast this
        refine ⟨⟨q, hq_nn⟩, ?_, ?_⟩
        · rw [← NNReal.coe_le_coe, nonnegRatToNN_coe]; exact htq.le
        · rw [nonnegRatToNN_coe]; exact hqhi
      choose qs hqs_ge hqs_lt using hex
      refine ⟨qs, hqs_ge, ?_⟩
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hqs_ge⟩
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hqs_ge n)))]
      have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        gcongr
      linarith [hqs_lt n, hN]
    rcases hlim_s with ⟨rs, hrs_bnd, hrs_tend⟩
    rcases hlim_t with ⟨qs, hqs_ge, hqs_tend⟩
    have hXs : Tendsto (fun n => L.X (nonnegRatToNN (rs n)) ω) atTop (𝓝 (L.X s ω)) :=
      (L.rightCont ω s).tendsto.comp hrs_tend
    have hXt : Tendsto (fun n => L.X (nonnegRatToNN (qs n)) ω) atTop (𝓝 (L.X t ω)) :=
      (L.rightCont ω t).tendsto.comp hqs_tend
    refine le_of_tendsto_of_tendsto hXt hXs (Eventually.of_forall fun n => ?_)
    have hle_q : (rs n).1 ≤ (qs n).1 := by
      have h1 : (nonnegRatToNN (rs n) : ℝ) ≤ (nonnegRatToNN (qs n) : ℝ) :=
        NNReal.coe_le_coe.mpr ((hrs_bnd n).2.trans (hqs_ge n))
      rw [nonnegRatToNN_coe, nonnegRatToNN_coe] at h1
      exact_mod_cast h1
    exact hω ⟨(rs n, qs n), hle_q⟩

private lemma bv_firstHitting_zero_ae_of_drift_pos
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hdrift_pos : 0 < L.drift) :
    ∀ᵐ ω ∂P, firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = 0 := by
  let tseq : ℕ → NNReal := fun n => ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have htseq_pos : ∀ n : ℕ, (0 : ℝ) < (tseq n : ℝ) := fun n => by
    change 0 < 1 / ((n : ℝ) + 1); positivity
  have hlim_int : Tendsto
      (fun n : ℕ => ∫ y in Iio (0 : ℝ), (tseq n : ℝ) * (Real.exp ((1 / (tseq n : ℝ)) * y) - 1) ∂L.ν)
      atTop (𝓝 0) := by
    have hbound := bv_min_one_abs_integrableOn L hBV
    have hlim : Tendsto
        (fun n : ℕ => ∫ y in Iio (0 : ℝ), (tseq n : ℝ) * (Real.exp ((1 / (tseq n : ℝ)) * y) - 1) ∂L.ν)
        atTop (𝓝 (∫ _y in Iio (0 : ℝ), (0 : ℝ) ∂L.ν)) := by
      refine tendsto_integral_filter_of_dominated_convergence (G := ℝ) (ι := ℕ) (l := atTop) (fun y : ℝ => min (1 : ℝ) |y|) ?_ ?_ hbound ?_
      · exact Eventually.of_forall fun n =>
          (continuous_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
            continuous_const)).aestronglyMeasurable
      · refine Eventually.of_forall fun n => ?_
        filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
        have ht_pos : 0 < (tseq n : ℝ) := htseq_pos n
        have ht_le1 : (tseq n : ℝ) ≤ 1 := by
          change 1 / ((n : ℝ) + 1) ≤ 1
          exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
        have hu_nonpos : (1 / (tseq n : ℝ)) * y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hy.le
        have hexp_le : Real.exp ((1 / (tseq n : ℝ)) * y) ≤ 1 := Real.exp_le_one_iff.mpr hu_nonpos
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht_pos, abs_of_nonpos (sub_nonpos.mpr hexp_le), neg_sub]
        refine le_min ?_ ?_
        · have h1 : 1 - Real.exp ((1 / (tseq n : ℝ)) * y) ≤ 1 := by linarith [Real.exp_pos ((1 / (tseq n : ℝ)) * y)]
          nlinarith
        · have hlin := Real.add_one_le_exp ((1 / (tseq n : ℝ)) * y)
          have h1 : 1 - Real.exp ((1 / (tseq n : ℝ)) * y) ≤ -((1 / (tseq n : ℝ)) * y) := by linarith
          have h2 : (tseq n : ℝ) * (1 - Real.exp ((1 / (tseq n : ℝ)) * y)) ≤
              (tseq n : ℝ) * (-((1 / (tseq n : ℝ)) * y)) :=
            mul_le_mul_of_nonneg_left h1 ht_pos.le
          have h3 : (tseq n : ℝ) * (-((1 / (tseq n : ℝ)) * y)) = |y| := by
            rw [abs_of_neg hy]; field_simp
          linarith
      · filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
        have hdom : Tendsto (fun n : ℕ => (tseq n : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        refine squeeze_zero_norm ?_ hdom
        intro n
        have ht_pos : 0 < (tseq n : ℝ) := htseq_pos n
        have hu_nonpos : (1 / (tseq n : ℝ)) * y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hy.le
        have hexp_le : Real.exp ((1 / (tseq n : ℝ)) * y) ≤ 1 := Real.exp_le_one_iff.mpr hu_nonpos
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos ht_pos, abs_of_nonpos (sub_nonpos.mpr hexp_le), neg_sub]
        have h1 : 1 - Real.exp ((1 / (tseq n : ℝ)) * y) ≤ 1 := by linarith [Real.exp_pos ((1 / (tseq n : ℝ)) * y)]
        nlinarith
    rwa [integral_zero] at hlim
  have hlim_prob : Tendsto (fun n : ℕ => (P {ω : Omega | L.X (tseq n) ω ≤ 0}).toReal) atTop (𝓝 0) := by
    let c0 : ℝ := 1 - Real.exp (-L.drift)
    have hc0_pos : 0 < c0 := by
      dsimp only [c0]
      linarith [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hdrift_pos)]
    have hupper : Tendsto
        (fun n : ℕ => (1 - Real.exp ((tseq n : ℝ) * L.ψ (1 / (tseq n : ℝ)) - L.drift)) / c0)
        atTop (𝓝 0) := by
      have hexp : Tendsto
          (fun n : ℕ => (tseq n : ℝ) * L.ψ (1 / (tseq n : ℝ)) - L.drift) atTop (𝓝 0) := by
        have heq : (fun n : ℕ => (tseq n : ℝ) * L.ψ (1 / (tseq n : ℝ)) - L.drift) =
            fun n => ∫ y in Iio (0 : ℝ), (tseq n : ℝ) * (Real.exp ((1 / (tseq n : ℝ)) * y) - 1) ∂L.ν := by
          ext n
          have ht_pos : 0 < (tseq n : ℝ) := htseq_pos n
          rw [bv_psi_eq_drift_add_integral L hBV (by positivity), mul_add,
            ← integral_const_mul]
          have hcancel : (tseq n : ℝ) * (L.drift * (1 / (tseq n : ℝ))) = L.drift := by field_simp
          linarith
        rw [heq]
        exact hlim_int
      have h1 : Tendsto
          (fun n : ℕ => 1 - Real.exp ((tseq n : ℝ) * L.ψ (1 / (tseq n : ℝ)) - L.drift))
          atTop (𝓝 (1 - Real.exp 0)) :=
        tendsto_const_nhds.sub (Real.continuous_exp.continuousAt.tendsto.comp hexp)
      rw [Real.exp_zero, sub_self] at h1
      simpa using h1.div_const c0
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) ?_ hupper
    intro n
    rw [le_div_iff₀ hc0_pos]
    let A : Set Omega := {ω : Omega | L.X (tseq n) ω ≤ 0}
    have hA_meas : MeasurableSet A :=
      measurableSet_le ((L.adapted (tseq n)).mono (F.le (tseq n)) le_rfl) measurable_const
    have ht_pos : 0 < (tseq n : ℝ) := htseq_pos n
    let θ : ℝ := 1 / (tseq n : ℝ)
    have hθ_nn : 0 ≤ θ := by positivity
    let f : Omega → ℝ := fun ω => 1 - Real.exp (θ * L.X (tseq n) ω - L.drift)
    have hf_int : Integrable f P :=
      (integrable_const (1 : ℝ)).sub (by
        have heq : (fun ω => Real.exp (θ * L.X (tseq n) ω - L.drift)) =
            fun ω => Real.exp (-L.drift) * Real.exp (θ * L.X (tseq n) ω) := by
          ext ω; rw [← Real.exp_add]; congr 1; ring
        rw [heq]
        exact (L.laplace (tseq n) θ hθ_nn).1.const_mul _)
    have hf_ae_nn : ∀ᵐ ω ∂P, 0 ≤ f ω := by
      filter_upwards [bv_X_le_drift_mul_ae L hBV (tseq n)] with ω hω
      dsimp only [f]
      have h1 : θ * L.X (tseq n) ω - L.drift ≤ 0 := by
        have hmul : θ * L.X (tseq n) ω ≤ θ * (L.drift * (tseq n : ℝ)) :=
          mul_le_mul_of_nonneg_left hω hθ_nn
        have hcancel : θ * (L.drift * (tseq n : ℝ)) = L.drift := by
          dsimp only [θ]; field_simp
        linarith
      linarith [Real.exp_le_one_iff.mpr h1]
    have hstep1 : (P A).toReal * c0 ≤ ∫ ω, f ω ∂P := by
      have hconst : (P A).toReal * c0 = ∫ ω in A, c0 ∂P := by
        rw [setIntegral_const, smul_eq_mul, Measure.real]
      rw [hconst]
      calc
        ∫ ω in A, c0 ∂P ≤ ∫ ω in A, f ω ∂P := by
          refine setIntegral_mono_on (integrableOn_const (hs := measure_ne_top P A))
            hf_int.integrableOn hA_meas fun ω hω => ?_
          dsimp only [c0, f]
          have hle : θ * L.X (tseq n) ω - L.drift ≤ -L.drift := by
            have := mul_nonpos_of_nonneg_of_nonpos hθ_nn (mem_setOf.mp hω)
            linarith
          linarith [Real.exp_le_exp.mpr hle]
        _ ≤ ∫ ω, f ω ∂P := setIntegral_le_integral hf_int hf_ae_nn
    have hstep2 : ∫ ω, f ω ∂P = 1 - Real.exp ((tseq n : ℝ) * L.ψ θ - L.drift) := by
      dsimp only [f]
      have hexp_eq : (fun ω => Real.exp (θ * L.X (tseq n) ω - L.drift)) =
          fun ω => Real.exp (-L.drift) * Real.exp (θ * L.X (tseq n) ω) := by
        ext ω; rw [← Real.exp_add]; congr 1; ring
      have hint2 : Integrable (fun ω => Real.exp (θ * L.X (tseq n) ω - L.drift)) P := by
        rw [hexp_eq]; exact (L.laplace (tseq n) θ hθ_nn).1.const_mul _
      rw [integral_sub (integrable_const (1 : ℝ)) hint2, integral_const, smul_eq_mul,
        Measure.real, measure_univ, ENNReal.toReal_one, one_mul,
        hexp_eq, integral_const_mul, (L.laplace (tseq n) θ hθ_nn).2, ← Real.exp_add]
      congr 2
      unfold SpectrallyNegativeLevy.ψ
      ring
    linarith
  have hge_zero : ∀ k : ℕ,
      P {ω : Omega | (tseq k : WithTop NNReal) ≤
        firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω} = 0 := by
    intro k
    let ε : NNReal := tseq k
    let B : Set Omega := {ω : Omega | (ε : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω}
    have hle : ∀ n : ℕ, k < n → (P B).toReal ≤ (P {ω : Omega | L.X (tseq n) ω ≤ 0}).toReal := by
      intro n hkn
      have hsub : B ⊆ {ω : Omega | L.X (tseq n) ω ≤ 0} := by
        intro ω hω
        by_contra hgt
        have hgt' : 0 < L.X (tseq n) ω := lt_of_not_ge hgt
        have hpos_t : (0 : NNReal) < tseq n := by
          rw [← NNReal.coe_lt_coe, NNReal.coe_zero]; exact htseq_pos n
        have hhit : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω ≤ (tseq n : WithTop NNReal) :=
          sInf_le ⟨tseq n, ⟨hpos_t, hgt'⟩, rfl⟩
        have hlt_t : (tseq n : WithTop NNReal) < (ε : WithTop NNReal) := by
          refine WithTop.coe_lt_coe.mpr ?_
          rw [← NNReal.coe_lt_coe]
          change (1 : ℝ) / ((n : ℝ) + 1) < 1 / ((k : ℝ) + 1)
          gcongr
        exact not_lt_of_ge (le_trans hω hhit) hlt_t
      exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
    have htoReal : (P B).toReal = 0 := by
      refine le_antisymm ?_ ENNReal.toReal_nonneg
      exact ge_of_tendsto hlim_prob (eventually_atTop.mpr ⟨k + 1, fun n hn => hle n (by omega)⟩)
    exact (ENNReal.toReal_eq_zero_iff (P B)).mp htoReal |>.resolve_right (measure_ne_top P B)
  have hunion : P (⋃ k : ℕ,
      {ω : Omega | (tseq k : WithTop NNReal) ≤
        firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω}) = 0 :=
    measure_iUnion_null hge_zero
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hunion
  simp only [mem_ofPred_eq] at hω
  cases hτ : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω with
  | top =>
    refine mem_iUnion.mpr ⟨0, ?_⟩
    show (tseq 0 : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω
    rw [hτ]
    exact le_top
  | coe t =>
    have ht_pos : (0 : NNReal) < t := by
      rw [hτ] at hω
      exact pos_iff_ne_zero.mpr fun h0 => hω (by simp [h0])
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (NNReal.coe_pos.mpr ht_pos)
    refine mem_iUnion.mpr ⟨k, ?_⟩
    show (tseq k : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω
    rw [hτ, WithTop.coe_le_coe, ← NNReal.coe_le_coe]
    exact hk.le

end PositiveDiscountZeroBarrierBV

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hBV : L.BoundedVariation) :
    forall (q : Real), 0 < q ->
          forall phi : Real,
      (0 <= phi ∧ L.ψ phi = q ∧ (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi)) ->
      (forall (x : Real), x = 0 ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) := by
  intro q _hq phi _hphi x hx finiteTime hfin
  subst hx
  have hdrift_pos : 0 < L.drift := bv_drift_pos_of_not_antitone L hNotDecreasing hBV
  have hhit0 : ∀ᵐ ω ∂P, firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = 0 :=
    bv_firstHitting_zero_ae_of_drift_pos L hBV hdrift_pos
  have hae : (fun ω : Omega =>
      if firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = ⊤
      then (0 : ℝ)
      else Real.exp (-q * (finiteTime ω : ℝ))) =ᵐ[P] fun _ => (1 : ℝ) := by
    filter_upwards [hhit0] with ω hω
    have hne : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω ≠ ⊤ := by
      rw [hω]; exact WithTop.coe_ne_top
    have hbne : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω != ⊤ := by
      simpa [bne_iff_ne] using hne
    have hft : firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω =
        (finiteTime ω : WithTop NNReal) := hfin ω hbne
    have hft0 : finiteTime ω = 0 := by
      have : (0 : WithTop NNReal) = (finiteTime ω : WithTop NNReal) := by rwa [hω] at hft
      exact WithTop.coe_injective this.symm
    simp [hne, hft0, Real.exp_zero]
  rw [integral_congr_ae hae, integral_const, smul_eq_mul, Measure.real, measure_univ,
    ENNReal.toReal_one, mul_one]
  simp [Real.exp_zero]
