-- Prove2me | solution 1 for MultivarScores.LevelSet.cdf_level_set_consistent
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:00:23.337845+00:00
-- url     : https://prove2.me/submissions/36886b52-3c93-48b8-8e21-76a97c062bd2

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

set_option autoImplicit false
open MeasureTheory MultivarScores.LevelSet

lemma msl_key {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ)
    (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY]
    (hh_int : Integrable h)
    (hwh_int : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d =>
      w (p.2 - p.1) * h p.2) (PY.prod volume))
    (α : ℝ) (S : Set (MultivarScores.L2Rule.E d)) (hS : MeasurableSet S) :
    Integrable (fun z => S.indicator (1 : MultivarScores.L2Rule.E d → ℝ) z *
        ((α - MultivarScores.L2Rule.smooth PY w z) * h z)) ∧
    ∫ y, scoreΓ w h α S y ∂PY = ∫ z, S.indicator (1 : MultivarScores.L2Rule.E d → ℝ) z *
        ((α - MultivarScores.L2Rule.smooth PY w z) * h z) := by
  have hG : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d =>
      (α - w (p.2 - p.1)) * h p.2) (PY.prod volume) := by
    have := ((hh_int.comp_snd PY).const_mul α).sub hwh_int
    refine this.congr ?_
    filter_upwards with p
    simp only [Pi.sub_apply]; ring
  set K : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d → ℝ := fun p =>
    S.indicator (1 : MultivarScores.L2Rule.E d → ℝ) p.2 * ((α - w (p.2 - p.1)) * h p.2) with hKdef
  have hK : Integrable K (PY.prod volume) := by
    have : Integrable ((Prod.snd ⁻¹' S).indicator (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d =>
        (α - w (p.2 - p.1)) * h p.2)) (PY.prod volume) := hG.indicator (measurable_snd hS)
    refine this.congr ?_
    filter_upwards with p
    by_cases hp : p.2 ∈ S <;> simp [K, Set.indicator, hp]
  have hscore : ∀ y, scoreΓ w h α S y = ∫ z, K (y, z) := by
    intro y
    unfold scoreΓ
    rw [← integral_indicator hS]
    congr 1; funext z
    by_cases hz : z ∈ S <;> simp [K, Set.indicator, hz]
  have hae : ∀ᵐ z ∂(volume : Measure (MultivarScores.L2Rule.E d)), ∫ y, K (y, z) ∂PY =
      S.indicator (1 : MultivarScores.L2Rule.E d → ℝ) z *
        ((α - MultivarScores.L2Rule.smooth PY w z) * h z) := by
    filter_upwards [hwh_int.prod_left_ae] with z hz
    have h1 : ∀ y, K (y, z) = S.indicator (1 : MultivarScores.L2Rule.E d → ℝ) z *
        (α * h z - w (z - y) * h z) := by intro y; simp only [K]; ring
    simp_rw [h1]
    rw [integral_const_mul, integral_sub (integrable_const _) hz, integral_mul_const,
      integral_mul_const]
    have h2 : ∫ _y, α ∂PY = α := by simp
    rw [h2]
    unfold MultivarScores.L2Rule.smooth
    ring
  have hint : Integrable (fun z => ∫ y, K (y, z) ∂PY) volume := hK.integral_prod_right
  refine ⟨hint.congr hae, ?_⟩
  calc ∫ y, scoreΓ w h α S y ∂PY = ∫ y, ∫ z, K (y, z) ∂volume ∂PY := by simp_rw [hscore]
    _ = ∫ p, K p ∂(PY.prod volume) := (integral_prod K hK).symm
    _ = ∫ z, ∫ y, K (y, z) ∂PY := integral_prod_symm K hK
    _ = _ := integral_congr_ae hae

lemma msl_smooth_meas {d : ℕ} (w : MultivarScores.L2Rule.E d → ℝ) (hw_meas : Measurable w)
    (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY] :
    Measurable (MultivarScores.L2Rule.smooth PY w) := by
  have : Measurable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d => w (p.1 - p.2)) :=
    hw_meas.comp (measurable_fst.sub measurable_snd)
  exact (this.stronglyMeasurable.integral_prod_right' (ν := PY)).measurable

lemma msl_eq19 {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ)
    (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY]
    (hw_meas : Measurable w) (hh_int : Integrable h)
    (hwh_int : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d =>
      w (p.2 - p.1) * h p.2) (PY.prod volume))
    (α : ℝ) (A : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) :
    Integrable (fun z => (α - MultivarScores.L2Rule.smooth PY w z) *
        ((A \ levelSet (MultivarScores.L2Rule.smooth PY w) α).indicator 1 z
          - (levelSet (MultivarScores.L2Rule.smooth PY w) α \ A).indicator 1 z) * h z) ∧
    (∫ y, scoreΓ w h α A y ∂PY) - ∫ y, scoreΓ w h α (levelSet (MultivarScores.L2Rule.smooth PY w) α) y ∂PY =
      ∫ z, (α - MultivarScores.L2Rule.smooth PY w z) *
        ((A \ levelSet (MultivarScores.L2Rule.smooth PY w) α).indicator 1 z
          - (levelSet (MultivarScores.L2Rule.smooth PY w) α \ A).indicator 1 z) * h z := by
  have hL : MeasurableSet (levelSet (MultivarScores.L2Rule.smooth PY w) α) :=
    measurableSet_le measurable_const (msl_smooth_meas w hw_meas PY)
  obtain ⟨iA, eA⟩ := msl_key w h PY hh_int hwh_int α A hA
  obtain ⟨iL, eL⟩ := msl_key w h PY hh_int hwh_int α _ hL
  have hfun : ∀ z, A.indicator (1 : MultivarScores.L2Rule.E d → ℝ) z *
        ((α - MultivarScores.L2Rule.smooth PY w z) * h z) -
      (levelSet (MultivarScores.L2Rule.smooth PY w) α).indicator (1 : MultivarScores.L2Rule.E d → ℝ) z *
        ((α - MultivarScores.L2Rule.smooth PY w z) * h z) =
      (α - MultivarScores.L2Rule.smooth PY w z) *
        ((A \ levelSet (MultivarScores.L2Rule.smooth PY w) α).indicator 1 z
          - (levelSet (MultivarScores.L2Rule.smooth PY w) α \ A).indicator 1 z) * h z := by
    intro z
    by_cases hzA : z ∈ A <;> by_cases hzL : z ∈ levelSet (MultivarScores.L2Rule.smooth PY w) α <;>
      simp [Set.indicator, hzA, hzL] <;> ring
  have hi := iA.sub iL
  have hi' : Integrable (fun z => (α - MultivarScores.L2Rule.smooth PY w z) *
        ((A \ levelSet (MultivarScores.L2Rule.smooth PY w) α).indicator 1 z
          - (levelSet (MultivarScores.L2Rule.smooth PY w) α \ A).indicator 1 z) * h z) := by
    refine hi.congr ?_
    filter_upwards with z
    simpa using hfun z
  refine ⟨hi', ?_⟩
  rw [eA, eL, ← integral_sub iA iL]
  refine integral_congr_ae ?_
  filter_upwards with z
  exact hfun z

lemma msl_nonneg {d : ℕ} (s h : MultivarScores.L2Rule.E d → ℝ) (hh : ∀ z, 0 ≤ h z) (α : ℝ)
    (A : Set (MultivarScores.L2Rule.E d)) (z : MultivarScores.L2Rule.E d) :
    0 ≤ (α - s z) * ((A \ levelSet s α).indicator 1 z - (levelSet s α \ A).indicator 1 z) * h z := by
  have hz := hh z
  by_cases hzA : z ∈ A
  · by_cases hzL : z ∈ levelSet s α
    · simp [Set.indicator, hzA, hzL]
    · have hlt : s z < α := by
        have : ¬ α ≤ s z := hzL
        exact not_le.1 this
      have := mul_nonneg (sub_nonneg.2 hlt.le) hz
      simpa [Set.indicator, hzA, hzL] using this
  · by_cases hzL : z ∈ levelSet s α
    · have hle : α ≤ s z := hzL
      have := mul_nonneg (sub_nonneg.2 hle) hz
      simp only [Set.indicator, Set.mem_diff, hzA, hzL, not_true, and_false, if_false, not_false_eq_true,
        and_self, if_true, Pi.one_apply]
      nlinarith
    · simp [Set.indicator, hzA, hzL]

theorem solution {d : ℕ} (h : MultivarScores.L2Rule.E d → ℝ)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY]
    (α : ℝ) (hα : 0 < α) (A : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) :
    ∫ y, scoreΓ MultivarScores.L2Rule.heaviside h α (levelSet (MultivarScores.L2Rule.cdf PY) α) y ∂PY ≤ ∫ y, scoreΓ MultivarScores.L2Rule.heaviside h α A y ∂PY := by
  have hmeas : Measurable (MultivarScores.L2Rule.heaviside : MultivarScores.L2Rule.E d → ℝ) :=
    measurable_const.indicator measurableSet_Ici
  have hsm : MultivarScores.L2Rule.smooth PY MultivarScores.L2Rule.heaviside = MultivarScores.L2Rule.cdf PY := by
    funext z
    unfold MultivarScores.L2Rule.smooth MultivarScores.L2Rule.cdf
    have : ∀ s : MultivarScores.L2Rule.E d, MultivarScores.L2Rule.heaviside (z - s) =
        (Set.Iic z).indicator (1 : MultivarScores.L2Rule.E d → ℝ) s := by
      intro s
      unfold MultivarScores.L2Rule.heaviside
      by_cases hs : s ≤ z
      · have h1 : z - s ∈ Set.Ici (0 : MultivarScores.L2Rule.E d) := sub_nonneg.2 hs
        have h2 : s ∈ Set.Iic z := hs
        simp [Set.indicator, h1, h2]
      · have h1 : z - s ∉ Set.Ici (0 : MultivarScores.L2Rule.E d) := fun h' => hs (sub_nonneg.1 h')
        have h2 : s ∉ Set.Iic z := hs
        simp [Set.indicator, h1, h2]
    simp_rw [this]
    rw [integral_indicator_one measurableSet_Iic]
    rfl
  have hwh : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d =>
      MultivarScores.L2Rule.heaviside (p.2 - p.1) * h p.2) (PY.prod volume) := by
    refine (hh_int.comp_snd PY).mono' ?_ ?_
    · exact ((hmeas.comp (measurable_snd.sub measurable_fst)).mul (hh_meas.comp measurable_snd)).aestronglyMeasurable
    · filter_upwards with p
      have h0 : 0 ≤ MultivarScores.L2Rule.heaviside (p.2 - p.1) := by
        unfold MultivarScores.L2Rule.heaviside; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have h1 : MultivarScores.L2Rule.heaviside (p.2 - p.1) ≤ 1 := by
        unfold MultivarScores.L2Rule.heaviside; exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (hh_nonneg _))]
      exact mul_le_of_le_one_left (hh_nonneg _) h1
  rw [← hsm]
  obtain ⟨hi, he⟩ := msl_eq19 MultivarScores.L2Rule.heaviside h PY hmeas hh_int hwh α A hA
  have : 0 ≤ ∫ z, (α - MultivarScores.L2Rule.smooth PY MultivarScores.L2Rule.heaviside z) *
        ((A \ levelSet (MultivarScores.L2Rule.smooth PY MultivarScores.L2Rule.heaviside) α).indicator 1 z
          - (levelSet (MultivarScores.L2Rule.smooth PY MultivarScores.L2Rule.heaviside) α \ A).indicator 1 z) * h z :=
    integral_nonneg fun z => msl_nonneg _ h hh_nonneg α A z
  linarith
