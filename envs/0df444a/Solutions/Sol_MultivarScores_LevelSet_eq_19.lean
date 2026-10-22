-- Prove2me | solution 1 for MultivarScores.LevelSet.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:53:41.236753+00:00
-- url     : https://prove2.me/submissions/6e473d86-8996-4ed6-931b-e8c11d43562c

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

theorem solution {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ) (PY : Measure (MultivarScores.L2Rule.E d)) [IsProbabilityMeasure PY]
    (hw_meas : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (hwh_int : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d => w (p.2 - p.1) * h p.2) (PY.prod volume))
    (α : ℝ) (hα : 0 < α) (A : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A) :
    (∫ y, scoreΓ w h α A y ∂PY) - ∫ y, scoreΓ w h α (levelSet (MultivarScores.L2Rule.smooth PY w) α) y ∂PY =
      ∫ z, (α - MultivarScores.L2Rule.smooth PY w z) *
        ((A \ levelSet (MultivarScores.L2Rule.smooth PY w) α).indicator 1 z
          - (levelSet (MultivarScores.L2Rule.smooth PY w) α \ A).indicator 1 z) * h z :=
  (msl_eq19 w h PY hw_meas hh_int hwh_int α A hA).2
