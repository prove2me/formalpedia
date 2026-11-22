-- Prove2me | solution 1 for MasulloGRH.infiniteLocalMulTamagawa_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:20:12.434302+00:00
-- url     : https://prove2.me/submissions/48ea62b6-a645-4032-82db-7e225c9d153c

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_MasulloGRH_infiniteLocalMulTamagawa_isHaarMeasure

/-- On the units of a normed field `K`, an additive Haar measure `μ` weighted by `‖x‖⁻ᵐ` and
restricted to `Kˣ` is a multiplicative Haar measure, provided multiplication by `a ≠ 0` scales
`μ` by `‖a‖ᵐ`, i.e. `μ.map (a * ·) = ‖a‖⁻ᵐ • μ`. -/
theorem isHaarMeasure_comap_units_withDensity {K : Type*} [NormedField K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (μ : Measure K) [μ.IsAddHaarMeasure] (m : ℕ)
    (hscale : ∀ a : K, a ≠ 0 → μ.map (a * ·) = (((‖a‖₊ : ℝ≥0∞) ^ m))⁻¹ • μ) :
    ((μ.withDensity fun x ↦ ((‖x‖₊ : ℝ≥0∞) ^ m)⁻¹).comap Units.val).IsHaarMeasure := by
  set ρ : K → ℝ≥0∞ := fun x ↦ ((‖x‖₊ : ℝ≥0∞) ^ m)⁻¹ with hρ
  set μ' := μ.withDensity ρ
  have hρm : Measurable ρ := by
    simp only [hρ]
    fun_prop
  have hopen : Topology.IsOpenEmbedding (Units.val : Kˣ → K) :=
    IsOpenUnits.isOpenEmbedding_unitsVal (M := K)
  have hemb : MeasurableEmbedding (Units.val : Kˣ → K) := hopen.measurableEmbedding
  have himg : ∀ s : Set Kˣ, MeasurableSet s → MeasurableSet (Units.val '' s) :=
    fun s hs ↦ hemb.measurableSet_image.mpr hs
  -- invariance of `μ'` under multiplication by a nonzero scalar
  have hinv : ∀ a : K, a ≠ 0 → μ'.map (a * ·) = μ' := by
    intro a ha
    have hmeas : Measurable (a * · : K → K) := (continuous_const.mul continuous_id).measurable
    set N : ℝ≥0∞ := (‖a‖₊ : ℝ≥0∞) ^ m with hN
    have hN0 : N ≠ 0 := by
      have : (‖a‖₊ : ℝ≥0∞) ≠ 0 := by simpa using ha
      exact pow_ne_zero m this
    have hNt : N ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hρa (x : K) : ρ x = N * ρ (a * x) := by
      have hx : ((‖a * x‖₊ : ℝ≥0∞)) ^ m = N * (‖x‖₊ : ℝ≥0∞) ^ m := by
        rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
      simp only [hρ]
      rw [hx, ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt), ← mul_assoc,
        ENNReal.mul_inv_cancel hN0 hNt, one_mul]
    ext t ht
    rw [Measure.map_apply hmeas ht, withDensity_apply _ (hmeas ht), withDensity_apply _ ht]
    conv_lhs => rw [show ρ = fun x ↦ N * ρ (a * x) from funext hρa]
    rw [lintegral_const_mul' _ _ hNt, ← setLIntegral_map ht hρm hmeas, hscale a ha,
      Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, one_mul]
  have hρpos : ∀ x, ρ x ≠ 0 := fun x ↦
    ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have h1 : IsFiniteMeasureOnCompacts (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun C hC ↦ ?_⟩
    rw [hemb.comap_apply]
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨u₀, -, hu₀⟩ := hC.exists_isMinOn hne
      (continuous_norm.comp Units.continuous_val).continuousOn
    have hbound : ∀ x ∈ Units.val '' C, ρ x ≤ ρ u₀.val := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [hρ]
      refine ENNReal.inv_le_inv.mpr (pow_le_pow_left₀ zero_le ?_ m)
      exact ENNReal.coe_le_coe.mpr (hu₀ hu)
    have hfin : ρ u₀.val ≠ ⊤ := by
      have : (‖(u₀ : K)‖₊ : ℝ≥0∞) ≠ 0 := by simp
      exact ENNReal.inv_ne_top.mpr (pow_ne_zero m this)
    calc μ' (Units.val '' C) = ∫⁻ x in Units.val '' C, ρ x ∂μ :=
          withDensity_apply _ (himg _ hC.measurableSet)
      _ ≤ ∫⁻ _ in Units.val '' C, ρ u₀.val ∂μ := setLIntegral_mono measurable_const hbound
      _ = ρ u₀.val * μ (Units.val '' C) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top hfin.lt_top
          (hC.image Units.continuous_val).measure_lt_top
  have h3 : Measure.IsOpenPosMeasure (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun U hU hne ↦ ?_⟩
    rw [hemb.comap_apply]
    intro h0
    rw [withDensity_apply_eq_zero' hρm.aemeasurable] at h0
    have : {x | ρ x ≠ 0} = Set.univ := Set.eq_univ_of_forall hρpos
    rw [this, Set.univ_inter] at h0
    have hopen' : IsOpen (Units.val '' U) := hopen.isOpenMap U hU
    exact (hopen'.measure_pos μ (hne.image _)).ne' h0
  have h2 : Measure.IsMulLeftInvariant (μ'.comap (Units.val : Kˣ → K)) := by
    refine ⟨fun g ↦ ?_⟩
    ext s hs
    have hmeas : Measurable (g * · : Kˣ → Kˣ) := (continuous_const.mul continuous_id).measurable
    rw [Measure.map_apply hmeas hs, hemb.comap_apply, hemb.comap_apply]
    have himage : Units.val '' ((g * ·) ⁻¹' s) = (g.val * ·) ⁻¹' (Units.val '' s) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨g * u, hu, rfl⟩
      · rintro ⟨u, hu, hux⟩
        refine ⟨g⁻¹ * u, by simpa using hu, ?_⟩
        simp only [Units.val_mul, hux, ← mul_assoc, Units.inv_mul, one_mul]
    rw [himage, ← Measure.map_apply (measurable_const_mul g.val) (himg s hs),
      hinv g.val g.ne_zero]
  exact { toIsFiniteMeasureOnCompacts := h1, toIsMulLeftInvariant := h2, toIsOpenPosMeasure := h3 }

/-- A scaling law for multiplication on one field transports along a measurable ring
isomorphism to its pushforward. -/
theorem map_mul_left_map_ringEquiv {E K : Type*} [Field E] [Field K] [MeasurableSpace E]
    [MeasurableSpace K] [MeasurableMul E] [MeasurableMul K] (e : E ≃+* K) (he : Measurable e)
    (ν : Measure E) (c : E → ℝ≥0∞) (h : ∀ b : E, b ≠ 0 → ν.map (b * ·) = c b • ν)
    (a : K) (ha : a ≠ 0) : (ν.map e).map (a * ·) = c (e.symm a) • ν.map e := by
  have hcomp : (a * ·) ∘ e = e ∘ (e.symm a * ·) := by
    ext x
    simp
  rw [Measure.map_map (measurable_const_mul a) he, hcomp,
    ← Measure.map_map he (measurable_const_mul _), h _ (by simpa using ha), Measure.map_smul]

/-- Multiplication by `b ≠ 0` scales Lebesgue measure on the real line by `|b|⁻¹`. -/
theorem real_map_mul_left_volume (b : ℝ) (hb : b ≠ 0) :
    (volume : Measure ℝ).map (b * ·) = ((‖b‖₊ : ℝ≥0∞) ^ 1)⁻¹ • volume := by
  rw [Real.map_volume_mul_left hb, pow_one, abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hb),
    ← Real.norm_eq_abs, ofReal_norm]
  rfl

/-- Multiplication by `b ≠ 0` scales Lebesgue measure on the complex plane by `|b|⁻²`. -/
theorem complex_map_mul_left_volume (b : ℂ) (hb : b ≠ 0) :
    (volume : Measure ℂ).map (b * ·) = ((‖b‖₊ : ℝ≥0∞) ^ 2)⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ b) = Complex.normSq b := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ b) (by rw [hdet]; exact (Complex.normSq_pos.mpr hb).ne')
  rw [hdet] at h
  change (volume : Measure ℂ).map (LinearMap.mulLeft ℝ b) = _
  rw [h, Complex.normSq_eq_norm_sq, abs_inv, abs_of_nonneg (sq_nonneg _),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm]
  rfl

open InfinitePlace.Completion in
/-- The archimedean local additive Tamagawa measure is an additive Haar measure, by transport
from the real line or the complex plane. -/
theorem infiniteLocalAdditiveTamagawaMeasure_isAddHaarMeasure
    (F : Type*) [Field F] [NumberField F] (w : InfinitePlace F) :
    letI : MeasurableSpace w.Completion := borel _
    (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := by
  let : MeasurableSpace w.Completion := borel _
  have : BorelSpace w.Completion := ⟨rfl⟩
  by_cases h : w.IsReal
  · rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
    exact (ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
      (isometryEquivRealOfIsReal h).symm.continuous (isometryEquivRealOfIsReal h).continuous
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous

end Sol_MasulloGRH_infiniteLocalMulTamagawa_isHaarMeasure

open MasulloGRH Sol_MasulloGRH_infiniteLocalMulTamagawa_isHaarMeasure in
open InfinitePlace.Completion in
theorem solution
    (F : Type*) [Field F] [NumberField F] (w : InfinitePlace F) :
    (infiniteLocalMulTamagawa F w).IsHaarMeasure := by
  have := infiniteLocalAdditiveTamagawaMeasure_isAddHaarMeasure F w
  unfold infiniteLocalMulTamagawa
  apply isHaarMeasure_comap_units_withDensity
  intro a ha
  by_cases h : w.IsReal
  · rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
    let e := (ringEquivRealOfIsReal h).symm
    have he : Measurable e := (isometryEquivRealOfIsReal h).symm.continuous.measurable
    rw [map_mul_left_map_ringEquiv e he volume _ real_map_mul_left_volume a ha, h.mult_eq_one]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero (map_zero _) a
    rw [hn]
  · have h' := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg h]
    let e := (ringEquivComplexOfIsComplex h').symm
    have he : Measurable e := (isometryEquivComplexOfIsComplex h').symm.continuous.measurable
    have hscale (b : ℂ) (hb : b ≠ 0) : ((2 : ℕ) • (volume : Measure ℂ)).map (b * ·) =
        ((‖b‖₊ : ℝ≥0∞) ^ 2)⁻¹ • ((2 : ℕ) • (volume : Measure ℂ)) := by
      rw [Measure.map_smul, complex_map_mul_left_volume b hb, ← Nat.cast_smul_eq_nsmul ENNReal,
        ← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, smul_smul, mul_comm]
    rw [map_mul_left_map_ringEquiv e he _ _ hscale a ha, h'.mult_eq_two]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a
    rw [hn]
