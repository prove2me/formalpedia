-- Prove2me | solution 1 for HunterPDE.Harmonic.ball_average_ge_of_sphereAverage_ge
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T14:26:15.279486+00:00
-- url     : https://prove2.me/submissions/939194f6-a1f7-47ff-9e5b-b04acc1f2cde

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set Metric
open HunterPDE.Harmonic

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r c : ℝ} (hr : 0 < r)
    (hu : ContinuousOn u (Metric.closedBall x r))
    (havg : ∀ t ∈ Ioc 0 r, c ≤ sphereAverage u x t) :
    c ≤ (⨍ y in Metric.ball x r, u y) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let T := Ioi (0 : ℝ)
  let μ : Measure E := volume
  let σ : Measure S := μ.toSphere
  let ν : Measure T := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let f : E → ℝ := (ball x r).indicator (fun y => u y - c)
  let g : E → ℝ := (ball x r).indicator (fun _ => c)
  have hf : Integrable f μ := by
    apply (integrable_indicator_iff measurableSet_ball).2
    exact ((hu.sub continuousOn_const).integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hg : Integrable g μ := by
    apply (integrable_indicator_iff measurableSet_ball).2
    exact integrableOn_const (measure_ball_lt_top (μ := μ) (x := x) (r := r)).ne
  have polar : ∀ (v : E → ℝ), Integrable v μ →
      (∫ y, v y ∂μ) = ∫ t : T, ∫ z : S, v (x + t.1 • z.1) ∂σ ∂ν := by
    intro v hv
    let w : E → ℝ := fun y => v (x + y)
    have hw : Integrable w μ := by
      exact ((measurePreserving_add_left μ x).integrable_comp hv.aestronglyMeasurable).2 hv
    have hw' : Integrable (fun y : ({0}ᶜ : Set E) => w y.1) (μ.comap (↑)) := by
      exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hw.integrableOn
    have hmp := μ.measurePreserving_homeomorphUnitSphereProd
    have hprod : Integrable (fun p : S × T => w (p.2.1 • p.1.1)) (σ.prod ν) := by
      have hh := (hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)
        (g := fun p => w ((homeomorphUnitSphereProd E).symm p).1))
      simp only [Function.comp_def, Homeomorph.symm_apply_apply] at hh
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh.mp hw'
    calc
      (∫ y, v y ∂μ) = ∫ y, w y ∂μ := (integral_add_left_eq_self v x).symm
      _ = ∫ y : ({0}ᶜ : Set E), w y.1 ∂(μ.comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl,
          restrict_compl_singleton]
      _ = ∫ p : S × T, w (p.2.1 • p.1.1) ∂(σ.prod ν) := by
        simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using
          hmp.integral_comp (Homeomorph.measurableEmbedding _)
            (fun p => w ((homeomorphUnitSphereProd E).symm p).1)
      _ = _ := integral_prod_symm _ hprod
  have inner : ∀ t : T, 0 ≤ (∫ z : S, f (x + t.1 • z.1) ∂σ) := by
    intro t
    have htpos : 0 < t.1 := t.2
    have hz : ∀ z : S, ‖z.1‖ = 1 := fun z => mem_sphere_zero_iff_norm.mp z.2
    have hd : ∀ z : S, dist (x + t.1 • z.1) x = t.1 := by
      intro z
      simp [dist_eq_norm, norm_smul, hz z, abs_of_pos htpos]
    by_cases ht : t.1 < r
    · have hmem : ∀ z : S, x + t.1 • z.1 ∈ ball x r := fun z => by
        simpa only [mem_ball, hd z] using ht
      simp only [f, indicator_of_mem (hmem _)]
      have hc : Continuous (fun z : S => u (x + t.1 • z.1)) := by
        exact hu.comp_continuous (f := fun z : S => x + t.1 • z.1)
          (by fun_prop) (fun z => ball_subset_closedBall (hmem z))
      have ha : 0 ≤ (⨍ z : S, u (x + t.1 • z.1) - c ∂σ) := by
        letI : NeZero σ := ⟨Measure.toSphere_ne_zero μ⟩
        change 0 ≤ ∫ z : S, u (x + t.1 • z.1) - c ∂((σ univ)⁻¹ • σ)
        rw [integral_sub (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).to_average
          (integrable_const c).to_average]
        change 0 ≤ (⨍ z : S, u (x + t.1 • z.1) ∂σ) - (⨍ _ : S, c ∂σ)
        rw [average_const]
        exact sub_nonneg.mpr (havg t.1 ⟨t.2, ht.le⟩)
      have hi := mul_nonneg (measureReal_nonneg (μ := σ) (s := univ)) ha
      simpa only [← smul_eq_mul, measure_smul_average] using hi
    · have hmem : ∀ z : S, x + t.1 • z.1 ∉ ball x r := fun z => by
        simpa only [mem_ball, hd z] using ht
      simp only [f, indicator_of_notMem (hmem _), integral_zero, le_refl]
  have hi : 0 ≤ (∫ y in ball x r, u y - c) := by
    rw [← integral_indicator measurableSet_ball]
    change 0 ≤ (∫ y, f y ∂μ)
    rw [polar f hf]
    exact integral_nonneg inner
  have ha : 0 ≤ (⨍ y in ball x r, u y - c) := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (measureReal_nonneg)) hi
  change 0 ≤ ∫ y, u y - c ∂(((μ.restrict (ball x r)) univ)⁻¹ • μ.restrict (ball x r)) at ha
  rw [integral_sub ((hu.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall).to_average
    (integrableOn_const (measure_ball_lt_top (μ := μ) (x := x) (r := r)).ne).to_average] at ha
  change 0 ≤ (⨍ y in ball x r, u y) - (⨍ _ in ball x r, c) at ha
  rw [setAverage_const (measure_ball_pos μ x hr).ne' (measure_ball_lt_top (μ := μ) (x := x) (r := r)).ne] at ha
  exact sub_nonneg.mp ha
