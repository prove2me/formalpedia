-- Prove2me | solution 1 for Kyprianou.Ch03.upwardPassage_zeroRootIsSubordinator
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:01:55.535213+00:00
-- url     : https://prove2.me/submissions/bcb63571-2930-4cb6-bc63-5610ccd94354

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Theorems.Thm_Kyprianou_Ch03_upwardPassageProbabilityAndDrift
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_zero_ae_of_unboundedVariation
import Theorems.Thm_AvramDividend_Classical_levy_strongMarkov_shiftedPath_indep_stoppedEvent_rightCont

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace Kyprianou.Ch03

section UpwardPassageSubordinator

/-! ### 1. Rational hitting time, measurability, and right-continuous stopping times -/

private abbrev PosRat := {q : ℚ // 0 < q}

private noncomputable def posRatToNN (q : PosRat) : NNReal :=
  Real.toNNReal (q.1 : ℝ)

private lemma posRatToNN_coe (q : PosRat) : (posRatToNN q : ℝ) = (q.1 : ℝ) :=
  Real.coe_toNNReal _ (Rat.cast_nonneg.mpr q.2.le)

private lemma posRatToNN_pos (q : PosRat) : (0 : NNReal) < posRatToNN q := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_zero, posRatToNN_coe]
  exact Rat.cast_pos.mpr q.2

/-- Countable-grid rational upward hitting time on arbitrary paths `NNReal → ℝ`. -/
private noncomputable def ratHit (x : ℝ) (f : NNReal → ℝ) : WithTop NNReal :=
  sInf ((fun q : PosRat => (posRatToNN q : WithTop NNReal)) ''
    {q : PosRat | x < f (posRatToNN q)})

private lemma ratHit_le_coe_iff (x : ℝ) (f : NNReal → ℝ) (t : NNReal) :
    ratHit x f ≤ (t : WithTop NNReal) ↔
      ∀ m : ℕ, ∃ q : PosRat,
        (posRatToNN q : ℝ) ≤ (t : ℝ) + 1 / ((m : ℝ) + 1) ∧ x < f (posRatToNN q) := by
  constructor
  · intro h m
    let d : NNReal := ⟨1 / ((m : ℝ) + 1), by positivity⟩
    let u : NNReal := t + d
    have hd_pos : (0 : NNReal) < d := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_zero]
      change (0 : ℝ) < 1 / ((m : ℝ) + 1)
      positivity
    have hlt : ratHit x f < (u : WithTop NNReal) :=
      lt_of_le_of_lt h (WithTop.coe_lt_coe.mpr (lt_add_of_pos_right t hd_pos))
    rcases sInf_lt_iff.mp hlt with ⟨_, ⟨q, hq, rfl⟩, hqu⟩
    refine ⟨q, ?_, hq⟩
    have hqu' : posRatToNN q < u := WithTop.coe_lt_coe.mp hqu
    have hle : (posRatToNN q : ℝ) ≤ (u : ℝ) := NNReal.coe_le_coe.mpr hqu'.le
    have hu_coe : (u : ℝ) = (t : ℝ) + 1 / ((m : ℝ) + 1) := rfl
    linarith
  · intro h
    cases hval : ratHit x f with
    | top =>
      rcases h 0 with ⟨q, _, hq_gt⟩
      have hle : ratHit x f ≤ (posRatToNN q : WithTop NNReal) :=
        sInf_le ⟨q, hq_gt, rfl⟩
      rw [hval, top_le_iff] at hle
      exact absurd hle (WithTop.coe_ne_top)
    | coe r =>
      rw [WithTop.coe_le_coe, ← NNReal.coe_le_coe]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      rcases h m with ⟨q, hq_le, hq_gt⟩
      have h1 : ratHit x f ≤ (posRatToNN q : WithTop NNReal) :=
        sInf_le ⟨q, hq_gt, rfl⟩
      rw [hval, WithTop.coe_le_coe, ← NNReal.coe_le_coe] at h1
      linarith

private lemma ratHit_eq_firstHittingTime_of_rightCont
    {Omega : Type} (X : NNReal → Omega → ℝ) (ω : Omega)
    (hrc : ∀ t : NNReal, ContinuousWithinAt (fun s => X s ω) (Ici t) t) (x : ℝ) :
    ratHit x (fun s => X s ω) = firstHittingTime X (Set.Ioi x) ω := by
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro _ ⟨t, ⟨ht_pos, hxt⟩, rfl⟩
    rw [ratHit_le_coe_iff]
    intro m
    have hopen : IsOpen (Ioi x) := isOpen_Ioi
    have hnhds : (fun s => X s ω) ⁻¹' Ioi x ∈ 𝓝[≥] t :=
      hrc t (hopen.mem_nhds hxt)
    rw [Metric.mem_nhdsWithin_iff] at hnhds
    rcases hnhds with ⟨δ, hδ_pos, hδ⟩
    let r : ℝ := min δ (1 / ((m : ℝ) + 1))
    have hr_pos : 0 < r := lt_min hδ_pos (by positivity)
    rcases exists_rat_btwn (lt_add_of_pos_right (t : ℝ) hr_pos) with ⟨q, htq, hqr⟩
    have hq_pos : (0 : ℚ) < q := by
      have : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt (NNReal.coe_nonneg t) htq
      exact_mod_cast this
    let qp : PosRat := ⟨q, hq_pos⟩
    have hq_ge : t ≤ posRatToNN qp := by
      rw [← NNReal.coe_le_coe, posRatToNN_coe]
      exact htq.le
    have hq_ball : posRatToNN qp ∈ Metric.ball t δ := by
      rw [Metric.mem_ball, NNReal.dist_eq, posRatToNN_coe, abs_of_nonneg (by linarith)]
      linarith [min_le_left δ (1 / ((m : ℝ) + 1))]
    have hq_hit : x < X (posRatToNN qp) ω := hδ ⟨hq_ball, hq_ge⟩
    refine ⟨qp, ?_, hq_hit⟩
    rw [posRatToNN_coe]
    linarith [min_le_right δ (1 / ((m : ℝ) + 1))]
  · refine le_sInf ?_
    rintro _ ⟨q, hq, rfl⟩
    exact sInf_le ⟨posRatToNN q, ⟨posRatToNN_pos q, hq⟩, rfl⟩

private lemma measurable_ratHit (x : ℝ) :
    Measurable (ratHit x) := by
  refine measurable_of_Iic fun a => ?_
  cases a with
  | top =>
    have : ratHit x ⁻¹' Set.Iic ⊤ = Set.univ := by ext f; simp
    rw [this]; exact MeasurableSet.univ
  | coe t =>
    have hset : ratHit x ⁻¹' Set.Iic (t : WithTop NNReal) =
        ⋂ m : ℕ, ⋃ q : {q : PosRat // (posRatToNN q : ℝ) ≤ (t : ℝ) + 1 / ((m : ℝ) + 1)},
          {f : NNReal → ℝ | x < f (posRatToNN q.1)} := by
      ext f
      simp only [Set.mem_preimage, Set.mem_Iic, ratHit_le_coe_iff, Set.mem_iInter, Set.mem_iUnion,
        Set.mem_ofPred_eq]
      constructor
      · intro h m; rcases h m with ⟨q, hq1, hq2⟩; exact ⟨⟨q, hq1⟩, hq2⟩
      · intro h m; rcases h m with ⟨⟨q, hq1⟩, hq2⟩; exact ⟨q, hq1, hq2⟩
    rw [hset]
    refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => ?_
    exact measurableSet_lt measurable_const (measurable_pi_apply (posRatToNN q.1))

private lemma measurable_untopD_toReal :
    Measurable (fun a : WithTop NNReal => NNReal.toReal (WithTop.untopD (0 : NNReal) a)) := by
  refine NNReal.continuous_coe.measurable.comp ?_
  refine measurable_of_Iic fun r => ?_
  have hset : (fun a : WithTop NNReal => WithTop.untopD (0 : NNReal) a) ⁻¹' Set.Iic r =
      Set.Iic (r : WithTop NNReal) ∪ {⊤} := by
    ext a
    cases a with
    | top => simp
    | coe s =>
      simp only [mem_preimage, mem_Iic, mem_union, mem_singleton_iff,
        WithTop.untopD_coe, WithTop.coe_le_coe, WithTop.coe_ne_top, or_false]
  rw [hset]
  exact measurableSet_Iic.union (measurableSet_singleton ⊤)

private lemma measurableSet_rightCont_iff
    {Omega : Type} {mΩ : MeasurableSpace Omega} (F : Filtration NNReal mΩ)
    (s : NNReal) (A : Set Omega) :
    MeasurableSet[F.rightCont s] A ↔ ∀ u : NNReal, s < u → MeasurableSet[F u] A := by
  rw [Filtration.rightCont_eq]
  simp only [MeasurableSpace.measurableSet_iInf]

private lemma firstHittingTime_le_measurableSet_rightCont
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (x : ℝ) (s : NNReal) :
    MeasurableSet[F.rightCont s] {ω : Omega | firstHittingTime L.X (Set.Ioi x) ω ≤ (s : WithTop NNReal)} := by
  rw [measurableSet_rightCont_iff]
  intro u hsu
  have hpos : (0 : ℝ) < (u : ℝ) - (s : ℝ) := sub_pos.mpr (NNReal.coe_lt_coe.mpr hsu)
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hpos
  have hset : {ω : Omega | firstHittingTime L.X (Set.Ioi x) ω ≤ (s : WithTop NNReal)} =
      ⋂ k : ℕ, ⋃ q : {q : PosRat // (posRatToNN q : ℝ) ≤ (s : ℝ) + 1 / (((M + k : ℕ) : ℝ) + 1)},
        {ω : Omega | x < L.X (posRatToNN q.1) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [← ratHit_eq_firstHittingTime_of_rightCont L.X ω (L.rightCont ω) x, ratHit_le_coe_iff]
    constructor
    · intro h k
      rcases h (M + k) with ⟨q, hq1, hq2⟩
      exact ⟨⟨q, hq1⟩, hq2⟩
    · intro h m
      rcases h m with ⟨⟨q, hq1⟩, hq2⟩
      refine ⟨q, hq1.trans ?_, hq2⟩
      gcongr
      exact_mod_cast Nat.le_add_left m M
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => ?_
  have hq_le_u : posRatToNN q.1 ≤ u := by
    rw [← NNReal.coe_le_coe]
    have h1 : (1 : ℝ) / (((M + k : ℕ) : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      gcongr
      exact_mod_cast Nat.le_add_right M k
    linarith [q.2, hM]
  have hmeas : Measurable[F u] (L.X (posRatToNN q.1)) :=
    (L.adapted (posRatToNN q.1)).mono (F.mono hq_le_u) le_rfl
  exact hmeas measurableSet_Ioi

private lemma measurable_firstHittingTime_val
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F) (x : ℝ) :
    Measurable (fun ω : Omega => firstHittingTime L.X (Set.Ioi x) ω) := by
  have hX_meas : Measurable (fun ω : Omega => fun t : NNReal => L.X t ω) :=
    measurable_pi_lambda _ fun t => (L.adapted t).mono (F.le t) le_rfl
  have heq : (fun ω : Omega => firstHittingTime L.X (Set.Ioi x) ω) =
      fun ω => ratHit x (fun t => L.X t ω) := by
    ext ω
    exact (ratHit_eq_firstHittingTime_of_rightCont L.X ω (L.rightCont ω) x).symm
  rw [heq]
  exact (measurable_ratHit x).comp hX_meas

private lemma firstHittingTime_mono_barrier
    {Omega : Type} (X : NNReal → Omega → ℝ) (ω : Omega) {x y : ℝ} (hxy : x ≤ y) :
    firstHittingTime X (Set.Ioi x) ω ≤ firstHittingTime X (Set.Ioi y) ω := by
  refine le_sInf ?_
  rintro _ ⟨t, ⟨ht_pos, hyt⟩, rfl⟩
  exact sInf_le ⟨t, ⟨ht_pos, lt_of_le_of_lt hxy hyt⟩, rfl⟩

/-! ### 2. Almost-sure immediate upward passage `τ_0 = 0` (BV + UBV) and finiteness `τ_x < ⊤` -/

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

private lemma bv_firstHitting_zero_ae
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hZeroRoot : ∀ θ : ℝ, 0 ≤ θ → L.ψ θ = 0 → θ = 0)
    (hPsiNonneg : ∀ θ : ℝ, 0 ≤ θ → 0 ≤ L.ψ θ) :
    ∀ᵐ ω ∂P, firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = 0 := by
  have hdrift_pos : 0 < L.drift := by
    have h1 : 0 ≤ L.ψ 1 := hPsiNonneg 1 zero_le_one
    have h2 : L.ψ 1 ≤ L.drift * 1 := bv_psi_le_drift_mul L hBV zero_le_one
    have hne : L.ψ 1 ≠ 0 := fun h0 => one_ne_zero (hZeroRoot 1 zero_le_one h0)
    linarith [lt_of_le_of_ne h1 (Ne.symm hne)]
  -- Scaled Laplace exponent limit: t_n * ψ(1/t_n) → L.drift for t_n = 1/(n+1)
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
  -- From P(X(t_n) ≤ 0) → 0, deduce P(τ_0 ≥ ε) = 0 for every ε > 0
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

/-- Full-measure regularity event where `τ_0 = 0` and every `τ_x` is finite. -/
private def GoodFin {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F) : Set Omega :=
  {ω : Omega | firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = 0 ∧
    ∀ x : NNReal, firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}

private lemma goodFin_ae
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ ω : Omega ∂P, Antitone (fun t : NNReal => L.X t ω)))
    (hZeroRoot : ∀ θ : ℝ, 0 ≤ θ → L.ψ θ = 0 → θ = 0) :
    ∀ᵐ ω ∂P, ω ∈ GoodFin L := by
  rcases Kyprianou.Ch03.upwardPassageProbabilityAndDrift P F L hNotDecreasing with
    ⟨φ, hφ_nn, hφ_zero, _, _, hprob_iff, hpsi_iff, _⟩
  have hφ_eq : φ = 0 := hZeroRoot φ hφ_nn hφ_zero
  have hPsiNonneg : ∀ θ : ℝ, 0 ≤ θ → 0 ≤ L.ψ θ := hpsi_iff.mp hφ_eq
  have hzero_ae : ∀ᵐ ω ∂P, firstHittingTime L.X (Set.Ioi (0 : ℝ)) ω = 0 := by
    by_cases hBV : L.BoundedVariation
    · exact bv_firstHitting_zero_ae L hBV hZeroRoot hPsiNonneg
    · exact Kyprianou.Ch03.firstHittingIoi_zero_ae_of_unboundedVariation P F L hBV
  have hfin_nat : ∀ n : ℕ, ∀ᵐ ω ∂P, firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω ≠ ⊤ := by
    intro n
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have htoReal : (P {ω : Omega | firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω != ⊤}).toReal = 1 :=
      (hprob_iff ((n + 1 : ℕ) : ℝ) hpos).mpr hφ_eq
    have hset_eq : {ω : Omega | firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω != ⊤} =
        {ω : Omega | firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω ≠ ⊤} := by
      ext ω; simp
    rw [hset_eq] at htoReal
    have hmeas : MeasurableSet {ω : Omega | firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω ≠ ⊤} :=
      ((measurable_firstHittingTime_val L ((n + 1 : ℕ) : ℝ)) (measurableSet_singleton ⊤)).compl
    have hP1 : P {ω : Omega | firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω ≠ ⊤} = 1 := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top P _), htoReal, ENNReal.ofReal_one]
    rw [ae_iff]
    have hcompl_eq : {ω : Omega | ¬firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω ≠ ⊤} =
        {ω : Omega | firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω ≠ ⊤}ᶜ := rfl
    rw [hcompl_eq, prob_compl_eq_one_sub hmeas, hP1, tsub_self]
  have hfin_all : ∀ᵐ ω ∂P, ∀ n : ℕ, firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω ≠ ⊤ :=
    ae_all_iff.mpr hfin_nat
  filter_upwards [hzero_ae, hfin_all] with ω h0 hn
  refine ⟨h0, fun x => ?_⟩
  obtain ⟨n, hxn⟩ := exists_nat_gt (x : ℝ)
  have hle : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤
      firstHittingTime L.X (Set.Ioi ((n + 1 : ℕ) : ℝ)) ω :=
    firstHittingTime_mono_barrier L.X ω (by push_cast; linarith)
  intro htop
  rw [htop, top_le_iff] at hle
  exact hn n hle

/-! ### 3. Candidate process `S`, monotonicity, càdlàg paths, and creeping -/

/-- The finite-valued upward passage process `S_x(ω) = τ_x^+(ω)` (with `S_0 ≡ 0`). -/
private noncomputable def upPass {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (x : NNReal) (ω : Omega) : ℝ :=
  if x = 0 then 0 else NNReal.toReal (WithTop.untopD (0 : NNReal) (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω))

private lemma upPass_zero
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F) :
    upPass L 0 = fun _ => 0 := by
  ext ω; simp [upPass]

private lemma measurable_upPass
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F) (x : NNReal) :
    Measurable (upPass L x) := by
  by_cases hx : x = 0
  · subst hx; rw [upPass_zero]; exact measurable_const
  · have : upPass L x = fun ω => NNReal.toReal (WithTop.untopD (0 : NNReal) (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω)) := by
      ext ω; simp [upPass, hx]
    rw [this]
    exact measurable_untopD_toReal.comp (measurable_firstHittingTime_val L (x : ℝ))

private lemma upPass_nonneg
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F) (x : NNReal) (ω : Omega) :
    0 ≤ upPass L x ω := by
  unfold upPass
  split_ifs
  · exact le_rfl
  · exact NNReal.coe_nonneg _

private lemma upPass_coe_eq_firstHitting_of_goodFin
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {ω : Omega} (hω : ω ∈ GoodFin L) (x : NNReal) :
    (Real.toNNReal (upPass L x ω) : WithTop NNReal) =
      firstHittingTime L.X (Set.Ioi (x : ℝ)) ω := by
  by_cases hx : x = 0
  · subst hx
    simp [upPass, hω.1]
  · have hfin : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤ := hω.2 x
    cases hτ : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω with
    | top => exact absurd hτ hfin
    | coe t =>
      dsimp only [upPass]
      rw [if_neg hx, hτ, WithTop.untopD_coe]
      exact congrArg (fun r : NNReal => (r : WithTop NNReal)) Real.toNNReal_coe

private lemma upPass_eq_untopD_of_goodFin
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {ω : Omega} (hω : ω ∈ GoodFin L) (x : NNReal) :
    upPass L x ω = NNReal.toReal (WithTop.untopD (0 : NNReal) (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω)) := by
  by_cases hx : x = 0
  · subst hx; simp [upPass, hω.1]
  · simp [upPass, hx]

private lemma upPass_mono_of_goodFin
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {ω : Omega} (hω : ω ∈ GoodFin L) :
    Monotone (fun x : NNReal => upPass L x ω) := by
  intro x y hxy
  have hle : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ firstHittingTime L.X (Set.Ioi (y : ℝ)) ω :=
    firstHittingTime_mono_barrier L.X ω (NNReal.coe_le_coe.mpr hxy)
  rw [← upPass_coe_eq_firstHitting_of_goodFin L hω x,
    ← upPass_coe_eq_firstHitting_of_goodFin L hω y,
    WithTop.coe_le_coe, ← NNReal.coe_le_coe,
    Real.coe_toNNReal _ (upPass_nonneg L x ω),
    Real.coe_toNNReal _ (upPass_nonneg L y ω)] at hle
  exact hle

private lemma upPass_isCadlag_of_goodFin
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {ω : Omega} (hω : ω ∈ GoodFin L) :
    IsCadlag (fun x : NNReal => upPass L x ω) := by
  have hmono := upPass_mono_of_goodFin L hω
  intro x
  refine ⟨?_, ?_⟩
  · -- Right-continuity at x
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    let tx : NNReal := Real.toNNReal (upPass L x ω)
    have htx_coe : (tx : ℝ) = upPass L x ω := Real.coe_toNNReal _ (upPass_nonneg L x ω)
    have hτx : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω = (tx : WithTop NNReal) :=
      (upPass_coe_eq_firstHitting_of_goodFin L hω x).symm
    let u : NNReal := tx + ⟨ε / 2, by positivity⟩
    have hlt : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (u : WithTop NNReal) := by
      rw [hτx, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe]
      change (tx : ℝ) < (tx : ℝ) + ε / 2
      linarith
    rcases sInf_lt_iff.mp hlt with ⟨_, ⟨s, ⟨hs_pos, hxs⟩, rfl⟩, hsu⟩
    have hsu' : (s : ℝ) < upPass L x ω + ε := by
      have : (s : ℝ) < (u : ℝ) := NNReal.coe_lt_coe.mpr (WithTop.coe_lt_coe.mp hsu)
      change (s : ℝ) < (tx : ℝ) + ε / 2 at this
      linarith
    let δ : ℝ := L.X s ω - (x : ℝ)
    have hδ_pos : 0 < δ := sub_pos.mpr hxs
    refine ⟨δ, hδ_pos, fun y hy hdist => ?_⟩
    have hxy : x ≤ y := hy
    have hylt : (y : ℝ) < L.X s ω := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hxy))] at hdist
      linarith
    have hτy_le : firstHittingTime L.X (Set.Ioi (y : ℝ)) ω ≤ (s : WithTop NNReal) :=
      sInf_le ⟨s, ⟨hs_pos, hylt⟩, rfl⟩
    rw [← upPass_coe_eq_firstHitting_of_goodFin L hω y, WithTop.coe_le_coe, ← NNReal.coe_le_coe,
      Real.coe_toNNReal _ (upPass_nonneg L y ω)] at hτy_le
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hmono hxy))]
    linarith
  · -- Left limit exists by monotonicity
    by_cases hx0 : x = 0
    · subst hx0
      refine ⟨0, ?_⟩
      have hbot : 𝓝[Iio (0 : NNReal)] (0 : NNReal) = ⊥ := by
        have hempty : Iio (0 : NNReal) = ∅ := by
          ext y; simp only [mem_Iio, mem_empty_iff_false, iff_false, not_lt]; exact zero_le (a := y)
        rw [hempty]; simp
      rw [hbot]
      exact tendsto_bot
    · exact ⟨sSup ((fun z : NNReal => upPass L z ω) '' Iio x), hmono.tendsto_nhdsLT x⟩

/-- Pathwise creeping (no positive overshoot) at finite upward passage times. -/
private lemma creeping_of_goodFin
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {ω : Omega} (hω : ω ∈ GoodFin L) (x : NNReal) :
    L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0) ω = (x : ℝ) := by
  by_cases hx : x = 0
  · subst hx
    simp [hω.1, L.X_zero ω]
  · have hx_pos : (0 : ℝ) < (x : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hx)
    have hfin := hω.2 x
    cases hτ : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω with
    | top => exact absurd hτ hfin
    | coe t =>
      simp only [WithTop.untopD_coe]
      -- Step 1: t > 0 by right-continuity at 0 and X 0 = 0 < x
      have ht_pos : (0 : NNReal) < t := by
        have hnhds : (fun s => L.X s ω) ⁻¹' Iio (x : ℝ) ∈ 𝓝[≥] (0 : NNReal) := by
          have h0 : L.X 0 ω ∈ Iio (x : ℝ) := by rw [L.X_zero ω]; exact hx_pos
          exact L.rightCont ω 0 (isOpen_Iio.mem_nhds h0)
        rw [Metric.mem_nhdsWithin_iff] at hnhds
        rcases hnhds with ⟨δ, hδ_pos, hδ⟩
        let d : NNReal := ⟨δ / 2, by positivity⟩
        have hd_pos : (0 : NNReal) < d := by
          rw [← NNReal.coe_lt_coe, NNReal.coe_zero]; change 0 < δ / 2; positivity
        have hd_le : (d : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi (x : ℝ)) ω := by
          refine le_sInf ?_
          rintro _ ⟨s, ⟨_, hxs⟩, rfl⟩
          rw [WithTop.coe_le_coe]
          by_contra hslt
          push_neg at hslt
          have hs_ball : s ∈ Metric.ball (0 : NNReal) δ := by
            rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
              abs_of_nonneg (NNReal.coe_nonneg s)]
            have : (s : ℝ) < (d : ℝ) := NNReal.coe_lt_coe.mpr hslt
            change (s : ℝ) < δ / 2 at this
            linarith
          have hs_lt : L.X s ω < (x : ℝ) := hδ ⟨hs_ball, zero_le (a := s)⟩
          have hxs' : (x : ℝ) < L.X s ω := mem_Ioi.mp hxs
          linarith
        rw [hτ, WithTop.coe_le_coe] at hd_le
        exact lt_of_lt_of_le hd_pos hd_le
      -- Step 2: x ≤ X t by right-continuity at t
      have hge : (x : ℝ) ≤ L.X t ω := by
        by_contra hlt
        push Not at hlt
        have hnhds : (fun s => L.X s ω) ⁻¹' Iio (x : ℝ) ∈ 𝓝[≥] t :=
          L.rightCont ω t (isOpen_Iio.mem_nhds hlt)
        rw [Metric.mem_nhdsWithin_iff] at hnhds
        rcases hnhds with ⟨δ, hδ_pos, hδ⟩
        let u : NNReal := t + ⟨δ / 2, by positivity⟩
        have hτ_lt : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (u : WithTop NNReal) := by
          rw [hτ, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe]
          change (t : ℝ) < (t : ℝ) + δ / 2
          linarith
        rcases sInf_lt_iff.mp hτ_lt with ⟨_, ⟨s, ⟨hs_pos, hxs⟩, rfl⟩, hsu⟩
        have ht_le_s : t ≤ s := by
          have := sInf_le (show (s : WithTop NNReal) ∈ (fun t : NNReal => (t : WithTop NNReal)) ''
            {t : NNReal | 0 < t ∧ L.X t ω ∈ Set.Ioi (x : ℝ)} from ⟨s, ⟨hs_pos, hxs⟩, rfl⟩)
          rwa [← firstHittingTime, hτ, WithTop.coe_le_coe] at this
        have hs_ball : s ∈ Metric.ball t δ := by
          rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht_le_s))]
          have : (s : ℝ) < (u : ℝ) := NNReal.coe_lt_coe.mpr (WithTop.coe_lt_coe.mp hsu)
          change (s : ℝ) < (t : ℝ) + δ / 2 at this
          linarith
        have hlt_s : L.X s ω < (x : ℝ) := hδ ⟨hs_ball, ht_le_s⟩
        have hxs' : (x : ℝ) < L.X s ω := mem_Ioi.mp hxs
        linarith
      -- Step 3: X t ≤ x by left limit + no positive jumps
      have hle : L.X t ω ≤ (x : ℝ) := by
        rcases L.leftLim ω t ht_pos with ⟨l, hl⟩
        have hnojump : L.X t ω ≤ l := L.noPosJumps ω t l ht_pos hl
        have hl_le : l ≤ (x : ℝ) := by
          have hne : (𝓝[<] t).NeBot := by
            rw [nhdsWithin_neBot]
            intro U hU
            rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ_pos, hδ⟩
            let s : NNReal := ⟨max 0 ((t : ℝ) - δ / 2), le_max_left _ _⟩
            have hslt : s < t := by
              rw [← NNReal.coe_lt_coe]
              exact max_lt (NNReal.coe_pos.mpr ht_pos) (by linarith)
            refine ⟨s, hδ ?_, hslt⟩
            rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hslt.le))]
            have : (t : ℝ) - δ / 2 ≤ (s : ℝ) := le_max_right _ _
            linarith
          have hev : ∀ᶠ s in 𝓝[<] t, L.X s ω ≤ (x : ℝ) := by
            have hmem : Ioo (0 : NNReal) t ∈ 𝓝[<] t :=
              Ioo_mem_nhdsLT ht_pos
            filter_upwards [hmem] with s hs
            by_contra hgt
            push_neg at hgt
            have h1 : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (s : WithTop NNReal) :=
              sInf_le ⟨s, ⟨hs.1, hgt⟩, rfl⟩
            rw [hτ, WithTop.coe_le_coe] at h1
            exact not_lt_of_ge h1 hs.2
          exact le_of_tendsto hl hev
        exact hnojump.trans hl_le
      exact le_antisymm hle hge

/-! ### 4. Shifted-path hitting-time additivity on `GoodFin` -/

private noncomputable def ratPass (h : NNReal) (f : NNReal → ℝ) : ℝ :=
  if h = 0 then 0 else NNReal.toReal (WithTop.untopD (0 : NNReal) (ratHit (h : ℝ) f))

private lemma measurable_ratPass (h : NNReal) : Measurable (ratPass h) := by
  by_cases hh : h = 0
  · subst hh
    have : ratPass 0 = fun _ => 0 := by ext f; simp [ratPass]
    rw [this]; exact measurable_const
  · have : ratPass h = fun f => NNReal.toReal (WithTop.untopD (0 : NNReal) (ratHit (h : ℝ) f)) := by
      ext f; simp [ratPass, hh]
    rw [this]
    exact measurable_untopD_toReal.comp (measurable_ratHit (h : ℝ))

private lemma increment_upPass_eq_ratPass_shifted_of_goodFin
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {ω : Omega} (hω : ω ∈ GoodFin L) (x h : NNReal) :
    increment (upPass L) x (x + h) ω =
      ratPass h (fun s => L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD (0 : NNReal) + s) ω -
        L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD (0 : NNReal)) ω) := by
  by_cases hh : h = 0
  · subst hh
    simp [increment, ratPass]
  · have hh_pos : (0 : ℝ) < (h : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hh)
    let tx : NNReal := (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD (0 : NNReal)
    have hτx : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω = (tx : WithTop NNReal) := by
      cases hEq : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω with
      | top => exact absurd hEq (hω.2 x)
      | coe t => dsimp only [tx]; rw [hEq, WithTop.untopD_coe]
    have hXtx : L.X tx ω = (x : ℝ) := creeping_of_goodFin L hω x
    let Y : NNReal → Omega → ℝ := fun s ω' => L.X (tx + s) ω' - L.X tx ω'
    have hY_rc : ∀ s : NNReal, ContinuousWithinAt (fun u => Y u ω) (Ici s) s := by
      intro s
      have h1 : ContinuousWithinAt (fun u => L.X (tx + u) ω) (Ici s) s := by
        have hadd : ContinuousWithinAt (fun u : NNReal => tx + u) (Ici s) s :=
          (continuous_const.add continuous_id).continuousWithinAt
        have hmaps : MapsTo (fun u : NNReal => tx + u) (Ici s) (Ici (tx + s)) :=
          fun u hu => add_le_add_right hu tx
        exact (L.rightCont ω (tx + s)).comp hadd hmaps
      exact h1.sub continuousWithinAt_const
    have hrat_eq : ratHit (h : ℝ) (fun s => Y s ω) = firstHittingTime Y (Set.Ioi (h : ℝ)) ω :=
      ratHit_eq_firstHittingTime_of_rightCont Y ω hY_rc (h : ℝ)
    -- Show τ_{x+h} = tx + τ_h(Y)
    have hadd_hit : firstHittingTime L.X (Set.Ioi ((x + h : NNReal) : ℝ)) ω =
        (tx : WithTop NNReal) + firstHittingTime Y (Set.Ioi (h : ℝ)) ω := by
      have hset_eq : {u : NNReal | 0 < u ∧ ((x + h : NNReal) : ℝ) < L.X u ω} =
          (fun s : NNReal => tx + s) '' {s : NNReal | 0 < s ∧ (h : ℝ) < Y s ω} := by
        ext u
        simp only [mem_ofPred_eq, mem_image, NNReal.coe_add]
        constructor
        · rintro ⟨hu_pos, hxu⟩
          have htx_lt_u : tx < u := by
            have hle : tx ≤ u := by
              have hgt_x : L.X u ω ∈ Set.Ioi (x : ℝ) := by
                show (x : ℝ) < L.X u ω; linarith
              have h1 : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (u : WithTop NNReal) :=
                sInf_le ⟨u, ⟨hu_pos, hgt_x⟩, rfl⟩
              rwa [hτx, WithTop.coe_le_coe] at h1
            refine lt_of_le_of_ne hle ?_
            intro heq
            subst heq
            linarith
          refine ⟨u - tx, ⟨tsub_pos_of_lt htx_lt_u, ?_⟩, add_tsub_cancel_of_le htx_lt_u.le⟩
          dsimp only [Y]
          rw [add_tsub_cancel_of_le htx_lt_u.le, hXtx]
          linarith
        · rintro ⟨s, ⟨hs_pos, hys⟩, rfl⟩
          refine ⟨lt_of_lt_of_le hs_pos (le_add_self), ?_⟩
          dsimp only [Y] at hys
          rw [hXtx] at hys
          linarith
      -- Now take sInf in WithTop NNReal
      refine le_antisymm ?_ ?_
      · cases hYhit : firstHittingTime Y (Set.Ioi (h : ℝ)) ω with
        | top => rw [WithTop.add_top]; exact le_top
        | coe ty =>
          cases hLhit : firstHittingTime L.X (Set.Ioi ((x + h : NNReal) : ℝ)) ω with
          | top => exact absurd hLhit (hω.2 (x + h))
          | coe tl =>
            rw [← WithTop.coe_add, WithTop.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add]
            refine le_of_forall_pos_le_add fun ε hε => ?_
            let εnn : NNReal := ⟨ε, hε.le⟩
            have hεnn_pos : (0 : NNReal) < εnn := by
              rw [← NNReal.coe_lt_coe, NNReal.coe_zero]; exact hε
            have hlt : firstHittingTime Y (Set.Ioi (h : ℝ)) ω < ((ty + εnn : NNReal) : WithTop NNReal) := by
              rw [hYhit, WithTop.coe_lt_coe]
              exact lt_add_of_pos_right ty hεnn_pos
            rcases sInf_lt_iff.mp hlt with ⟨_, ⟨s, ⟨hs_pos, hys⟩, rfl⟩, hs_lt⟩
            have hs_lt' : s < ty + εnn := WithTop.coe_lt_coe.mp hs_lt
            have hmem : tx + s ∈ {u : NNReal | 0 < u ∧ ((x + h : NNReal) : ℝ) < L.X u ω} := by
              rw [hset_eq]; exact ⟨s, ⟨hs_pos, hys⟩, rfl⟩
            have h1 : firstHittingTime L.X (Set.Ioi ((x + h : NNReal) : ℝ)) ω ≤
                ((tx + s : NNReal) : WithTop NNReal) := sInf_le ⟨tx + s, hmem, rfl⟩
            rw [hLhit, WithTop.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add] at h1
            have hs_coe : (s : ℝ) < (ty : ℝ) + ε := by
              have hlt_r := NNReal.coe_lt_coe.mpr hs_lt'
              rw [NNReal.coe_add] at hlt_r
              exact hlt_r
            linarith
      · refine le_sInf ?_
        rintro _ ⟨u, hu, rfl⟩
        change u ∈ {u : NNReal | 0 < u ∧ ((x + h : NNReal) : ℝ) < L.X u ω} at hu
        rw [hset_eq] at hu
        rcases hu with ⟨s, hs, rfl⟩
        have hs_ge : firstHittingTime Y (Set.Ioi (h : ℝ)) ω ≤ (s : WithTop NNReal) :=
          sInf_le ⟨s, hs, rfl⟩
        have hadd_le := add_le_add_right hs_ge (tx : WithTop NNReal)
        simpa [WithTop.coe_add] using hadd_le
    -- Extract finite NNReal values
    have hY_fin : firstHittingTime Y (Set.Ioi (h : ℝ)) ω ≠ ⊤ := by
      intro htop
      rw [htop, WithTop.add_top] at hadd_hit
      exact hω.2 (x + h) hadd_hit
    cases hYhit : firstHittingTime Y (Set.Ioi (h : ℝ)) ω with
    | top => exact absurd hYhit hY_fin
    | coe ty =>
      rw [hYhit] at hadd_hit
      have hxh_eq : firstHittingTime L.X (Set.Ioi ((x + h : NNReal) : ℝ)) ω =
          ((tx + ty : NNReal) : WithTop NNReal) := by
        simpa [WithTop.coe_add] using hadd_hit
      dsimp only [increment, ratPass]
      rw [if_neg hh, upPass_eq_untopD_of_goodFin L hω (x + h),
        upPass_eq_untopD_of_goodFin L hω x, hxh_eq, hτx]
      change ((tx + ty : NNReal) : ℝ) - (tx : ℝ) =
        NNReal.toReal (WithTop.untopD (0 : NNReal) (ratHit (h : ℝ) (fun s => Y s ω)))
      rw [hrat_eq, hYhit, WithTop.untopD_coe]
      change ((tx + ty : NNReal) : ℝ) - (tx : ℝ) = (ty : ℝ)
      rw [NNReal.coe_add]
      ring

private lemma increment_upPass_zero_eq_ratPass_of_goodFin
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {ω : Omega} (hω : ω ∈ GoodFin L) (h : NNReal) :
    increment (upPass L) 0 h ω = ratPass h (fun s => L.X s ω) := by
  by_cases hh : h = 0
  · subst hh; simp [increment, ratPass]
  · dsimp only [increment, ratPass]
    rw [if_neg hh, upPass_zero, sub_zero, upPass_eq_untopD_of_goodFin L hω h,
      ratHit_eq_firstHittingTime_of_rightCont L.X ω (L.rightCont ω) (h : ℝ)]

/-! ### 5. Truncated stopping times and full-path Strong Markov independence -/

private noncomputable def truncHit
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (x M : NNReal) (ω : Omega) : NNReal :=
  (min (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) (M : WithTop NNReal)).untopD M

private lemma truncHit_le_iff
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (x M s : NNReal) (ω : Omega) :
    truncHit L x M ω ≤ s ↔
      M ≤ s ∨ firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (s : WithTop NNReal) := by
  dsimp only [truncHit]
  cases hτ : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω with
  | top =>
    have hmin : min (⊤ : WithTop NNReal) (M : WithTop NNReal) = (M : WithTop NNReal) :=
      min_eq_right le_top
    rw [hmin, WithTop.untopD_coe]
    simp only [top_le_iff, WithTop.coe_ne_top, or_false]
  | coe t =>
    rw [← WithTop.coe_min, WithTop.untopD_coe, min_le_iff, WithTop.coe_le_coe]
    tauto

private lemma truncHit_eq_untopD_of_lt
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (x M : NNReal) {ω : Omega} (h : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)) :
    truncHit L x M ω = (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD (0 : NNReal) := by
  dsimp only [truncHit]
  cases hτ : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω with
  | top => rw [hτ] at h; exact absurd h not_top_lt
  | coe t =>
    rw [hτ, WithTop.coe_lt_coe] at h
    rw [← WithTop.coe_min, min_eq_left h.le, WithTop.untopD_coe, WithTop.untopD_coe]

private lemma truncHit_isStoppingTime_rightCont
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (x M s : NNReal) :
    MeasurableSet[F.rightCont s] {ω : Omega | truncHit L x M ω ≤ s} := by
  by_cases hMs : M ≤ s
  · have hset : {ω : Omega | truncHit L x M ω ≤ s} = Set.univ := by
      ext ω; simp [truncHit_le_iff, hMs]
    rw [hset]; exact MeasurableSet.univ
  · have hset : {ω : Omega | truncHit L x M ω ≤ s} =
        {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (s : WithTop NNReal)} := by
      ext ω; simp [truncHit_le_iff, hMs]
    rw [hset]
    exact firstHittingTime_le_measurableSet_rightCont L (x : ℝ) s

/-- The stopped σ-algebra associated with a finite `F.rightCont`-stopping time `τ`. -/
private def stoppedRightContMS
    {Omega : Type} {mΩ : MeasurableSpace Omega} (F : Filtration NNReal mΩ)
    (τ : Omega → NNReal) (hτ : ∀ s : NNReal, MeasurableSet[F.rightCont s] {ω | τ ω ≤ s}) :
    MeasurableSpace Omega where
  MeasurableSet' A := ∀ s : NNReal, MeasurableSet[F.rightCont s] (A ∩ {ω | τ ω ≤ s})
  measurableSet_empty s := by simp
  measurableSet_compl A hA s := by
    have hdiff : Aᶜ ∩ {ω | τ ω ≤ s} = {ω | τ ω ≤ s} \ (A ∩ {ω | τ ω ≤ s}) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, mem_diff, mem_setOf_eq]; tauto
    rw [hdiff]
    exact (hτ s).diff (hA s)
  measurableSet_iUnion f hf s := by
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion fun n => hf n s

private lemma firstHittingTime_le_inter_lt_measurableSet_stopped
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {x u : NNReal} (hux : u ≤ x) (M r : NNReal) :
    MeasurableSet[stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M)]
      ({ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤ (r : WithTop NNReal)} ∩
        {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)}) := by
  intro s
  have hAux : ∀ q : NNReal, q ≤ s →
      MeasurableSet[F.rightCont s]
        ({ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤ (r : WithTop NNReal)} ∩
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (q : WithTop NNReal)}) := by
    intro q hqs
    by_cases hrq : r ≤ q
    · have h1 : MeasurableSet[F.rightCont s]
          {ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤ (r : WithTop NNReal)} :=
        F.rightCont.mono (hrq.trans hqs) _ (firstHittingTime_le_measurableSet_rightCont L (u : ℝ) r)
      have h2 : MeasurableSet[F.rightCont s]
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (q : WithTop NNReal)} :=
        F.rightCont.mono hqs _ (firstHittingTime_le_measurableSet_rightCont L (x : ℝ) q)
      exact h1.inter h2
    · push_neg at hrq
      have heq : {ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤ (r : WithTop NNReal)} ∩
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (q : WithTop NNReal)} =
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (q : WithTop NNReal)} := by
        ext ω
        simp only [mem_inter_iff, mem_setOf_eq, and_iff_right_iff_imp]
        intro hqω
        exact (firstHittingTime_mono_barrier L.X ω (NNReal.coe_le_coe.mpr hux)).trans
          (hqω.trans (WithTop.coe_le_coe.mpr hrq.le))
      rw [heq]
      exact F.rightCont.mono hqs _ (firstHittingTime_le_measurableSet_rightCont L (x : ℝ) q)
  by_cases hMs : M ≤ s
  · have huniv : {ω : Omega | truncHit L x M ω ≤ s} = Set.univ := by
      ext ω; simp [truncHit_le_iff, hMs]
    rw [huniv, inter_univ]
    have hlt_eq : {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)} =
        ⋃ q : {q : ℚ // 0 ≤ q ∧ (q : ℝ) < (M : ℝ)},
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤
            ((Real.toNNReal (q.1 : ℝ) : NNReal) : WithTop NNReal)} := by
      ext ω
      simp only [mem_setOf_eq, mem_iUnion, Subtype.exists]
      constructor
      · intro hlt
        cases hτ : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω with
        | top => rw [hτ] at hlt; exact absurd hlt not_top_lt
        | coe t =>
          rw [hτ, WithTop.coe_lt_coe] at hlt
          rcases exists_rat_btwn (NNReal.coe_lt_coe.mpr hlt) with ⟨q, htq, hqM⟩
          have hq_nn : (0 : ℚ) ≤ q := by
            have : (0 : ℝ) ≤ (q : ℝ) := (NNReal.coe_nonneg t).trans htq.le
            exact_mod_cast this
          refine ⟨q, ⟨hq_nn, hqM⟩, ?_⟩
          rw [WithTop.coe_le_coe, ← NNReal.coe_le_coe,
            Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq_nn)]
          exact htq.le
      · rintro ⟨q, ⟨hq_nn, hqM⟩, hle⟩
        refine lt_of_le_of_lt hle ?_
        rw [WithTop.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq_nn)]
        exact hqM
    rw [hlt_eq, Set.inter_iUnion]
    refine MeasurableSet.iUnion fun q => hAux (Real.toNNReal (q.1 : ℝ)) ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Rat.cast_nonneg.mpr q.2.1)]
    exact q.2.2.le.trans (NNReal.coe_le_coe.mpr hMs)
  · push_neg at hMs
    have hEq : ({ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤ (r : WithTop NNReal)} ∩
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)}) ∩
        {ω : Omega | truncHit L x M ω ≤ s} =
        {ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤ (r : WithTop NNReal)} ∩
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (s : WithTop NNReal)} := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, truncHit_le_iff, not_le.mpr hMs, false_or]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, lt_of_le_of_lt h3 (WithTop.coe_lt_coe.mpr hMs)⟩, h3⟩
    rw [hEq]
    exact hAux s le_rfl

private lemma lt_M_measurableSet_stopped
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F) (x M : NNReal) :
    MeasurableSet[stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M)]
      {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)} := by
  have heq : {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)} =
      {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≤ (M : WithTop NNReal)} ∩
        {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)} := by
    ext ω; simp only [mem_inter_iff, mem_setOf_eq, iff_and_self]; exact le_of_lt
  rw [heq]
  exact firstHittingTime_le_inter_lt_measurableSet_stopped L le_rfl M M

private noncomputable def truncUpPass
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (x M u : NNReal) (ω : Omega) : ℝ :=
  if firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal) then upPass L u ω else 0

private lemma measurable_of_Iic_ms {α : Type*} (m : MeasurableSpace α) (f : α → ℝ)
    (h : ∀ a : ℝ, MeasurableSet[m] (f ⁻¹' Set.Iic a)) :
    @Measurable α ℝ m inferInstance f := by
  letI : MeasurableSpace α := m
  exact measurable_of_Iic h

private lemma measurable_sub_ms {α : Type*} (m : MeasurableSpace α) {f g : α → ℝ}
    (hf : @Measurable α ℝ m inferInstance f) (hg : @Measurable α ℝ m inferInstance g) :
    @Measurable α ℝ m inferInstance (fun a => f a - g a) := by
  letI : MeasurableSpace α := m
  exact hf.sub hg

private lemma measurableSet_biInter_ms {α ι : Type*} (m : MeasurableSpace α)
    (S : Finset ι) (f : ι → Set α) (hf : ∀ i ∈ S, MeasurableSet[m] (f i)) :
    MeasurableSet[m] (⋂ i ∈ S, f i) := by
  letI : MeasurableSpace α := m
  exact MeasurableSet.biInter S.countable_toSet hf

private lemma measurable_truncUpPass_stopped
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    {x u : NNReal} (hux : u ≤ x) (M : NNReal) :
    @Measurable Omega ℝ
      (stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M))
      inferInstance (truncUpPass L x M u) := by
  refine measurable_of_Iic_ms
    (stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M))
    (truncUpPass L x M u) fun a => ?_
  by_cases ha : a < 0
  · have hempty : truncUpPass L x M u ⁻¹' Set.Iic a = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      dsimp only [truncUpPass]
      split_ifs
      · exact lt_of_lt_of_le ha (upPass_nonneg L u ω)
      · exact ha
    rw [hempty]
    exact @MeasurableSet.empty Omega
      (stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M))
  · push Not at ha
    by_cases hu : u = 0
    · subst hu
      have huniv : truncUpPass L x M 0 ⁻¹' Set.Iic a = Set.univ := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true, truncUpPass, upPass, ↓reduceIte, ite_self]
        exact ha
      rw [huniv]
      exact @MeasurableSet.univ Omega
        (stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M))
    · have hset : truncUpPass L x M u ⁻¹' Set.Iic a =
          ({ω : Omega | firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≤
              ((Real.toNNReal a : NNReal) : WithTop NNReal)} ∩
            {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)}) ∪
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)}ᶜ := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
        dsimp only [truncUpPass]
        by_cases hlt : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)
        · rw [if_pos hlt]
          have hufin : firstHittingTime L.X (Set.Ioi (u : ℝ)) ω ≠ ⊤ := by
            intro htop
            have h1 := firstHittingTime_mono_barrier L.X ω (NNReal.coe_le_coe.mpr hux)
            rw [htop, top_le_iff] at h1
            rw [h1] at hlt
            exact not_top_lt hlt
          cases hτu : firstHittingTime L.X (Set.Ioi (u : ℝ)) ω with
          | top => exact absurd hτu hufin
          | coe tu =>
            simp only [upPass, hu, ↓reduceIte, hτu, WithTop.untopD_coe, WithTop.coe_le_coe,
              hlt, and_true, not_true_eq_false, or_false]
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ha]
        · rw [if_neg hlt]
          exact ⟨fun _ => Or.inr hlt, fun _ => ha⟩
      rw [hset]
      exact (firstHittingTime_le_inter_lt_measurableSet_stopped L hux M (Real.toNNReal a)).union
        (lt_M_measurableSet_stopped L x M).compl

/-- Full-path strong Markov independence for any finite-dimensional event of `upPass L` up to `x`. -/
private lemma strongMarkov_upPass_past_indep_shifted
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hGood : ∀ᵐ ω ∂P, ω ∈ GoodFin L)
    (x : NNReal)
    {A : Set Omega}
    (hA_meas : MeasurableSet A)
    (hA_stopped : ∀ M : NNReal,
      MeasurableSet[stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M)]
        (A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)}))
    {E : Set (NNReal → ℝ)} (hE : MeasurableSet E) :
    P (A ∩ {ω : Omega |
        (fun s => L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0 + s) ω -
          L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0) ω) ∈ E}) =
      P A * P {ω : Omega | (fun s => L.X s ω) ∈ E} := by
  let Y : Omega → NNReal → ℝ := fun ω s =>
    L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0 + s) ω -
      L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0) ω
  let Xpath : Omega → NNReal → ℝ := fun ω s => L.X s ω
  have hXpath_meas : Measurable Xpath :=
    measurable_pi_lambda _ fun s => (L.adapted s).mono (F.le s) le_rfl
  -- Step 1: For each M : ℕ, apply proved right-continuous strong Markov theorem to (truncHit L x M, A_M)
  have hStepM : ∀ M : ℕ,
      P (A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)} ∩
          (Y ⁻¹' E)) =
      P (A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)}) *
        P (Xpath ⁻¹' E) := by
    intro M
    let AM : Set Omega :=
      A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)}
    let τM : Omega → NNReal := truncHit L x (M : NNReal)
    let YM : Omega → NNReal → ℝ := fun ω s => L.X (τM ω + s) ω - L.X (τM ω) ω
    have hτM_stop := truncHit_isStoppingTime_rightCont L x (M : NNReal)
    have hAM_stop : ∀ s : NNReal, MeasurableSet[F.rightCont s] (AM ∩ {ω | τM ω ≤ s}) :=
      hA_stopped (M : NNReal)
    have hSM := AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent_rightCont
      L τM hτM_stop AM hAM_stop
    -- Evaluate hSM on {1} ×ˢ E
    have hAM_meas : MeasurableSet AM :=
      hA_meas.inter ((measurable_firstHittingTime_val L (x : ℝ)) measurableSet_Iio)
    have hind_meas : Measurable (Set.indicator AM (fun _ : Omega => (1 : ℝ))) :=
      measurable_const.indicator hAM_meas
    -- Note: YM is measurable because τM is measurable and X is right-continuous
    have hτM_meas : Measurable τM := by
      refine measurable_of_Iic fun s => ?_
      exact F.rightCont.le s _ (hτM_stop s)
    have hX_shift_meas : ∀ s : NNReal, Measurable (fun ω => L.X (τM ω + s) ω) := by
      intro s
      let approx : ℕ → Omega → NNReal := fun n ω =>
        ⟨((Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)) + 1 : ℕ) : ℝ) / ((n : ℝ) + 1), by positivity⟩
      have hlim : ∀ ω, Tendsto
          (fun n : ℕ => L.X (approx n ω + s) ω)
          atTop (𝓝 (L.X (τM ω + s) ω)) := by
        intro ω
        have hrc := L.rightCont ω (τM ω + s)
        refine hrc.tendsto.comp ?_
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun n => ?_⟩
        · rw [Metric.tendsto_nhds]
          intro ε hε
          obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
          refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
          rw [NNReal.dist_eq, NNReal.coe_add, NNReal.coe_add]
          have h1 : (τM ω : ℝ) * ((n : ℝ) + 1) < (Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)) : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          have h2 : (Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)) : ℝ) ≤ (τM ω : ℝ) * ((n : ℝ) + 1) :=
            Nat.floor_le (by positivity)
          have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have hap_coe : (approx n ω : ℝ) =
              ((Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)) + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) := rfl
          have hge : (τM ω : ℝ) ≤ (approx n ω : ℝ) := by
            rw [hap_coe, le_div_iff₀ hpos]; push_cast; linarith
          have hle : (approx n ω : ℝ) ≤ (τM ω : ℝ) + 1 / ((n : ℝ) + 1) := by
            rw [hap_coe, div_le_iff₀ hpos]; push_cast
            have : ((τM ω : ℝ) + 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = (τM ω : ℝ) * ((n : ℝ) + 1) + 1 := by
              field_simp
            linarith
          have hdiff : (approx n ω : ℝ) + (s : ℝ) - ((τM ω : ℝ) + (s : ℝ)) =
              (approx n ω : ℝ) - (τM ω : ℝ) := by ring
          rw [hdiff, abs_of_nonneg (sub_nonneg.mpr hge)]
          have hN' : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
            gcongr
          linarith
        · show τM ω + s ≤ approx n ω + s
          refine add_le_add_left ?_ s
          rw [← NNReal.coe_le_coe]
          have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have h1 : (τM ω : ℝ) * ((n : ℝ) + 1) < (Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)) : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          change (τM ω : ℝ) ≤ ((Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)) + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)
          rw [le_div_iff₀ hpos]; push_cast; linarith
      refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.mpr hlim)
      have hfloor_meas : Measurable (fun ω => Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1))) :=
        Nat.measurable_floor.comp ((NNReal.continuous_coe.measurable.comp hτM_meas).mul_const _)
      let qn : ℕ → NNReal := fun k => ⟨((k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1), by positivity⟩
      let g : ℕ → Omega → ℝ := fun k ω => L.X (qn k + s) ω
      have hg_meas : ∀ k : ℕ, Measurable (g k) := fun k =>
        (L.adapted (qn k + s)).mono (F.le (qn k + s)) le_rfl
      refine measurable_of_Iic fun a => ?_
      have hEq : (fun ω => L.X (approx n ω + s) ω) ⁻¹' Set.Iic a =
          ⋃ k : ℕ, ({ω | Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)) = k} ∩ (g k ⁻¹' Set.Iic a)) := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
        constructor
        · intro h
          refine ⟨Nat.floor ((τM ω : ℝ) * ((n : ℝ) + 1)), rfl, ?_⟩
          exact h
        · rintro ⟨k, hk, hg⟩
          have hap : approx n ω = qn k := by
            ext; simp [approx, qn, hk]
          rw [hap]
          exact hg
      rw [hEq]
      exact MeasurableSet.iUnion fun k =>
        (hfloor_meas (measurableSet_singleton k)).inter ((hg_meas k) measurableSet_Iic)
    have hYM_meas : Measurable YM :=
      measurable_pi_lambda _ fun s => (hX_shift_meas s).sub (by simpa using hX_shift_meas 0)
    have hpair_meas : Measurable (fun ω => (Set.indicator AM (fun _ : Omega => (1 : ℝ)) ω, YM ω)) :=
      hind_meas.prodMk hYM_meas
    have hprod_eval := congrArg (fun μ : Measure (ℝ × (NNReal → ℝ)) => μ ({(1 : ℝ)} ×ˢ E)) hSM
    have hprod_set : MeasurableSet ({(1 : ℝ)} ×ˢ E) := (measurableSet_singleton (1 : ℝ)).prod hE
    rw [Measure.map_apply hpair_meas hprod_set,
      Measure.prod_prod,
      Measure.map_apply hind_meas (measurableSet_singleton (1 : ℝ)),
      Measure.map_apply hXpath_meas hE] at hprod_eval
    have hind_pre : Set.indicator AM (fun _ : Omega => (1 : ℝ)) ⁻¹' {(1 : ℝ)} = AM := by
      ext ω
      by_cases hω : ω ∈ AM <;> simp [hω]
    have hlhs_pre : (fun ω => (Set.indicator AM (fun _ : Omega => (1 : ℝ)) ω, YM ω)) ⁻¹' ({(1 : ℝ)} ×ˢ E) =
        AM ∩ (Y ⁻¹' E) := by
      ext ω
      simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_inter_iff]
      by_cases hω : ω ∈ AM
      · simp only [Set.indicator_of_mem hω, true_and, hω]
        have hτeq : τM ω = (firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0 :=
          truncHit_eq_untopD_of_lt L x (M : NNReal) hω.2
        have hYeq : YM ω = Y ω := by
          ext s; simp only [YM, Y, hτeq]
        rw [hYeq]
      · simp [hω]
    rw [hlhs_pre, hind_pre] at hprod_eval
    exact hprod_eval
  -- Step 2: Take monotone limit M → ∞ using a.s. finiteness of τ_x
  have hmono_L : Monotone (fun M : ℕ =>
      A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)} ∩
        (Y ⁻¹' E)) := by
    intro M₁ M₂ h12 ω ⟨⟨hA, hlt⟩, hY⟩
    refine ⟨⟨hA, ?_⟩, hY⟩
    show firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M₂ : NNReal) : WithTop NNReal)
    exact lt_of_lt_of_le hlt (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr h12))
  have hmono_R : Monotone (fun M : ℕ =>
      A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)}) := by
    intro M₁ M₂ h12 ω ⟨hA, hlt⟩
    refine ⟨hA, ?_⟩
    show firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M₂ : NNReal) : WithTop NNReal)
    exact lt_of_lt_of_le hlt (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr h12))
  have hunion_fin : (⋃ M : ℕ,
      {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)}) =
      {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤} := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq]
    cases hτ : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω with
    | top => simp
    | coe t =>
      simp only [WithTop.coe_lt_coe, ne_eq, WithTop.coe_ne_top, not_false_eq_true, iff_true]
      obtain ⟨M, hM⟩ := exists_nat_gt (t : ℝ)
      exact ⟨M, by rw [← NNReal.coe_lt_coe]; exact_mod_cast hM⟩
  have hfin_ae : P {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}ᶜ = 0 := by
    rw [ae_iff] at hGood
    refine measure_mono_null (fun ω hω => ?_) hGood
    show ω ∉ GoodFin L
    intro hG
    exact hω (hG.2 x)
  have hEq_L : P (A ∩ (Y ⁻¹' E)) =
      ⨆ M : ℕ, P (A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)} ∩
        (Y ⁻¹' E)) := by
    rw [← hmono_L.measure_iUnion]
    have hset : (⋃ M : ℕ, A ∩ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)} ∩
        (Y ⁻¹' E)) = (A ∩ (Y ⁻¹' E)) ∩ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤} := by
      ext ω
      simp only [mem_iUnion, mem_inter_iff, ← hunion_fin]
      tauto
    rw [hset]
    have h1 := measure_mono_null (s := (A ∩ (Y ⁻¹' E)) \ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤})
      (fun ω hω => hω.2) hfin_ae
    have hcov : A ∩ (Y ⁻¹' E) ⊆
        ((A ∩ (Y ⁻¹' E)) ∩ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) ∪
        ((A ∩ (Y ⁻¹' E)) \ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) := by
      intro ω hω; by_cases h : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr ⟨hω, h⟩
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    exact (measure_mono hcov).trans ((measure_union_le _ _).trans (by rw [h1, add_zero]))
  have hEq_R : P A =
      ⨆ M : ℕ, P (A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)}) := by
    rw [← hmono_R.measure_iUnion]
    have hset : (⋃ M : ℕ, A ∩ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((M : NNReal) : WithTop NNReal)}) =
        A ∩ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤} := by
      rw [← Set.inter_iUnion, hunion_fin]
    rw [hset]
    have h1 := measure_mono_null (s := A \ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤})
      (fun ω hω => hω.2) hfin_ae
    have hcov : A ⊆ (A ∩ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) ∪
        (A \ {ω | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤}) := by
      intro ω hω; by_cases h : firstHittingTime L.X (Set.Ioi (x : ℝ)) ω ≠ ⊤
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr ⟨hω, h⟩
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    exact (measure_mono hcov).trans ((measure_union_le _ _).trans (by rw [h1, add_zero]))
  change P (A ∩ (Y ⁻¹' E)) = P A * P (Xpath ⁻¹' E)
  rw [hEq_L, hEq_R, ENNReal.iSup_mul]
  exact iSup_congr hStepM

/-! ### 6. Stationary & independent increments of `upPass L` -/

private lemma upPass_stationaryIncrements
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hGood : ∀ᵐ ω ∂P, ω ∈ GoodFin L) :
    HasStationaryIncrements (upPass L) P := by
  intro x h
  have hmeasL : Measurable (increment (upPass L) x (x + h)) :=
    (measurable_upPass L (x + h)).sub (measurable_upPass L x)
  have hmeasR : Measurable (increment (upPass L) 0 h) :=
    (measurable_upPass L h).sub (measurable_upPass L 0)
  refine ⟨hmeasL.aemeasurable, hmeasR.aemeasurable, ?_⟩
  ext B hB
  rw [Measure.map_apply hmeasL hB, Measure.map_apply hmeasR hB]
  let E : Set (NNReal → ℝ) := ratPass h ⁻¹' B
  have hE : MeasurableSet E := (measurable_ratPass h) hB
  have hSM := strongMarkov_upPass_past_indep_shifted L hGood x MeasurableSet.univ
    (fun M => by
      rw [Set.univ_inter]
      exact lt_M_measurableSet_stopped L x M) hE
  rw [Set.univ_inter, measure_univ, one_mul] at hSM
  have hL_ae : P (increment (upPass L) x (x + h) ⁻¹' B) =
      P {ω : Omega |
        (fun s => L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0 + s) ω -
          L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0) ω) ∈ E} := by
    refine measure_congr ?_
    filter_upwards [hGood] with ω hω
    change (increment (upPass L) x (x + h) ω ∈ B) = (ratPass h _ ∈ B)
    rw [increment_upPass_eq_ratPass_shifted_of_goodFin L hω x h]
  have hR_ae : P (increment (upPass L) 0 h ⁻¹' B) =
      P {ω : Omega | (fun s => L.X s ω) ∈ E} := by
    refine measure_congr ?_
    filter_upwards [hGood] with ω hω
    change (increment (upPass L) 0 h ω ∈ B) = (ratPass h _ ∈ B)
    rw [increment_upPass_zero_eq_ratPass_of_goodFin L hω h]
  rw [hL_ae, hR_ae, hSM]

private lemma upPass_independentIncrements
    {Omega : Type} [mΩ : MeasurableSpace Omega] {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hGood : ∀ᵐ ω ∂P, ω ∈ GoodFin L) :
    HasIndependentIncrements (upPass L) P := by
  intro n t ht
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  induction S using Finset.induction_on_max with
  | empty =>
    simp
  | @insert m S' hmax ih =>
    have hnotmem : m ∉ S' := fun hm => lt_irrefl m (hmax m hm)
    have hsets' : ∀ i ∈ S', MeasurableSet (sets i) := fun i hi => hsets i (Finset.mem_insert_of_mem hi)
    have hm_set : MeasurableSet (sets m) := hsets m (Finset.mem_insert_self m S')
    rw [Finset.prod_insert hnotmem]
    let x : NNReal := t m.castSucc
    let h : NNReal := t m.succ - x
    have hxh : x + h = t m.succ := add_tsub_cancel_of_le (ht (Fin.castSucc_le_succ m))
    let A : Set Omega := ⋂ i ∈ S', increment (upPass L) (t i.castSucc) (t i.succ) ⁻¹' sets i
    have hA_meas : MeasurableSet A :=
      MeasurableSet.biInter S'.countable_toSet fun i hi =>
        ((measurable_upPass L (t i.succ)).sub (measurable_upPass L (t i.castSucc))) (hsets' i hi)
    have hA_stopped : ∀ M : NNReal,
        MeasurableSet[stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M)]
          (A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)}) := by
      intro M
      let B_M : Set Omega :=
        ⋂ i ∈ S', (fun ω => truncUpPass L x M (t i.succ) ω - truncUpPass L x M (t i.castSucc) ω) ⁻¹' sets i
      have hBM_meas :
          MeasurableSet[stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M)] B_M := by
        refine measurableSet_biInter_ms
          (stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M)) S' _ fun i hi => ?_
        have hi_lt : i < m := hmax i hi
        have hsucc_le : t i.succ ≤ x := ht (by
          change i.succ ≤ m.castSucc
          exact Fin.succ_le_castSucc_iff.mpr hi_lt)
        have hcast_le : t i.castSucc ≤ x := (ht (Fin.castSucc_le_succ i)).trans hsucc_le
        have hm1 := measurable_truncUpPass_stopped L hsucc_le M
        have hm2 := measurable_truncUpPass_stopped L hcast_le M
        exact (measurable_sub_ms
          (stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M)) hm1 hm2)
          (hsets' i hi)
      have hEq : A ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)} =
          B_M ∩ {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (M : WithTop NNReal)} := by
        ext ω
        simp only [A, B_M, mem_inter_iff, mem_iInter, mem_preimage, mem_ofPred_eq]
        constructor
        · rintro ⟨h1, hlt⟩
          refine ⟨fun i hi => ?_, hlt⟩
          have h1i := h1 i hi
          dsimp only [increment] at h1i
          simp only [truncUpPass, if_pos hlt]
          exact h1i
        · rintro ⟨h1, hlt⟩
          refine ⟨fun i hi => ?_, hlt⟩
          have h1i := h1 i hi
          dsimp only [increment]
          simp only [truncUpPass, if_pos hlt] at h1i
          exact h1i
      rw [hEq]
      exact @MeasurableSet.inter Omega
        (stoppedRightContMS F (truncHit L x M) (truncHit_isStoppingTime_rightCont L x M))
        _ _ hBM_meas (lt_M_measurableSet_stopped L x M)
    let E : Set (NNReal → ℝ) := ratPass h ⁻¹' sets m
    have hE : MeasurableSet E := (measurable_ratPass h) hm_set
    have hSM := strongMarkov_upPass_past_indep_shifted L hGood x hA_meas hA_stopped hE
    have hL_ae : P (⋂ i ∈ insert m S', increment (upPass L) (t i.castSucc) (t i.succ) ⁻¹' sets i) =
        P (A ∩ {ω : Omega |
          (fun s => L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0 + s) ω -
            L.X ((firstHittingTime L.X (Set.Ioi (x : ℝ)) ω).untopD 0) ω) ∈ E}) := by
      refine measure_congr ?_
      filter_upwards [hGood] with ω hω
      change (ω ∈ ⋂ i ∈ insert m S', increment (upPass L) (t i.castSucc) (t i.succ) ⁻¹' sets i) =
        (ω ∈ A ∧ ratPass h _ ∈ sets m)
      have h1 : (ω ∈ ⋂ i ∈ insert m S', increment (upPass L) (t i.castSucc) (t i.succ) ⁻¹' sets i) =
          (ω ∈ A ∧ increment (upPass L) x (x + h) ω ∈ sets m) := by
        simp only [A, mem_iInter, Finset.mem_insert, mem_preimage, hxh]
        exact propext ⟨fun H => ⟨fun i hi => H i (Or.inr hi), H m (Or.inl rfl)⟩,
          fun ⟨hA, hm⟩ i hi => by rcases hi with rfl | hi'; exact hm; exact hA i hi'⟩
      rw [h1, increment_upPass_eq_ratPass_shifted_of_goodFin L hω x h]
    have hR_ae : P (increment (upPass L) (t m.castSucc) (t m.succ) ⁻¹' sets m) =
        P {ω : Omega | (fun s => L.X s ω) ∈ E} := by
      have hstat := upPass_stationaryIncrements L hGood x h
      have h1 : P (increment (upPass L) x (x + h) ⁻¹' sets m) = P (increment (upPass L) 0 h ⁻¹' sets m) := by
        have hmeasL : Measurable (increment (upPass L) x (x + h)) :=
          (measurable_upPass L (x + h)).sub (measurable_upPass L x)
        have hmeasR : Measurable (increment (upPass L) 0 h) :=
          (measurable_upPass L h).sub (measurable_upPass L 0)
        have hmeq := congrArg (fun μ : Measure ℝ => μ (sets m)) hstat.map_eq
        rwa [Measure.map_apply hmeasL hm_set, Measure.map_apply hmeasR hm_set] at hmeq
      rw [← hxh, h1]
      refine measure_congr ?_
      filter_upwards [hGood] with ω hω
      change (increment (upPass L) 0 h ω ∈ sets m) = (ratPass h _ ∈ sets m)
      rw [increment_upPass_zero_eq_ratPass_of_goodFin L hω h]
    rw [hL_ae, hSM, ih hsets', ← hR_ae, mul_comm]

end UpwardPassageSubordinator

end Kyprianou.Ch03

/-! ### Target theorem `solution` -/

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hZeroRoot : forall theta : Real, 0 <= theta -> L.ψ theta = 0 -> theta = 0) :
    exists (S : NNReal -> Omega -> Real),
      Kyprianou.Ch03.IsSubordinator P S ∧
      (forall x : NNReal, Measurable (S x)) ∧
      Measure.map
        (fun omega : Omega =>
          fun x : NNReal =>
            (Real.toNNReal (S x omega) : WithTop NNReal)) P =
      Measure.map
        (fun omega : Omega =>
          fun x : NNReal =>
            Kyprianou.Ch03.firstHittingTime L.X (Set.Ioi (x : Real)) omega) P := by
  have hGood := Kyprianou.Ch03.goodFin_ae L hNotDecreasing hZeroRoot
  refine ⟨Kyprianou.Ch03.upPass L, ?_, Kyprianou.Ch03.measurable_upPass L, ?_⟩
  · refine ⟨⟨Kyprianou.Ch03.upPass_zero L,
        Kyprianou.Ch03.upPass_independentIncrements L hGood,
        Kyprianou.Ch03.upPass_stationaryIncrements L hGood, ?_⟩, ?_⟩
    · filter_upwards [hGood] with ω hω
      exact Kyprianou.Ch03.upPass_isCadlag_of_goodFin L hω
    · filter_upwards [hGood] with ω hω
      exact Kyprianou.Ch03.upPass_mono_of_goodFin L hω
  · refine Measure.map_congr ?_
    filter_upwards [hGood] with ω hω
    funext x
    exact Kyprianou.Ch03.upPass_coe_eq_firstHitting_of_goodFin L hω x
