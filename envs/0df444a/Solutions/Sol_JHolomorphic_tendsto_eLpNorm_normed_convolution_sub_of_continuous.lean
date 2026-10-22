-- Prove2me | solution 1 for JHolomorphic.tendsto_eLpNorm_normed_convolution_sub_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:22:52.382608+00:00
-- url     : https://prove2.me/submissions/f2c9657e-8c15-4c6b-8686-59fddc909766

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.MetricSpace.Thickening



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal

theorem tendsto_eLpNorm_normed_convolution_sub_of_continuous_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {g : ℂ → E} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun n => eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) p volume)
      atTop (𝓝 0) := by
  set K := cthickening 1 (tsupport g) with hK
  have hKc : IsCompact K := hgc.isCompact.cthickening
  set M := volume K ^ p.toReal⁻¹ with hMdef
  have hM : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hKc.measure_lt_top.ne
  have hu := hgc.uniformContinuous_of_continuous hg
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hc : Tendsto (fun η : ℝ => M * ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal η) (𝓝[>] 0) (𝓝 (ENNReal.ofReal 0)) :=
      (ENNReal.tendsto_ofReal tendsto_id).mono_left nhdsWithin_le_nhds
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hM)
    simpa using this
  obtain ⟨η, hηε, hη0⟩ : ∃ η : ℝ, M * ENNReal.ofReal η ≤ ε ∧ 0 < η :=
    ((hc.eventually (ge_mem_nhds hε)).and self_mem_nhdsWithin).exists
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 hu η hη0
  filter_upwards [hφ.eventually (gt_mem_nhds (lt_min hδ one_pos))] with n hn
  have hpt : ∀ x, ‖((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) x‖ ≤ η := by
    intro x
    rw [Pi.sub_apply, ← dist_eq_norm]
    refine (φ n).dist_normed_convolution_le hg.aestronglyMeasurable (fun y hy => ?_)
    rw [mem_ball] at hy
    exact (hδu (hy.trans (hn.trans_le (min_le_left _ _)))).le
  have hsupp : Function.support ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) ⊆ K := by
    intro x hx
    by_contra hxK
    apply hx
    have hgx : g x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxK (self_subset_cthickening _ h))
    have hcx : ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g) x = 0 := by
      by_contra hne
      obtain ⟨a, ha, b, hb, hab⟩ := support_convolution_subset (lsmul ℝ ℝ) hne
      rw [(φ n).support_normed_eq, mem_ball, dist_zero_right] at ha
      refine hxK (mem_cthickening_of_dist_le _ b 1 _ (subset_tsupport _ hb) ?_)
      rw [← hab, dist_eq_norm, add_sub_cancel_right]
      exact (ha.trans (hn.trans_le (min_le_right _ _))).le
    simp [hgx, hcx]
  rw [← Set.indicator_eq_self.2 hsupp,
    eLpNorm_indicator_eq_eLpNorm_restrict isClosed_cthickening.measurableSet]
  refine (eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hpt)).trans ?_
  rw [Measure.restrict_apply_univ]
  exact hηε

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞} (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {g : ℂ → E} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun n => eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] g - g) p volume)
      atTop (𝓝 0) :=
  tendsto_eLpNorm_normed_convolution_sub_of_continuous_aux φ hφ hg hgc
