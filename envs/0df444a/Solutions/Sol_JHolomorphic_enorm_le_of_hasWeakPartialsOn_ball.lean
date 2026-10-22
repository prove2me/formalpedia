-- Prove2me | solution 1 for JHolomorphic.enorm_le_of_hasWeakPartialsOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:07:37.496871+00:00
-- url     : https://prove2.me/submissions/3baf055d-739a-4a82-9204-bc823151ffd6

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_enorm_le_of_contDiff_tsupport_ball
import Theorems.Thm_JHolomorphic_eLpNorm_normed_convolution_le
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_univ_indicator_tsupport
import Theorems.Thm_JHolomorphic_fderiv_normed_convolution_eq_of_hasWeakPartialsOn
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.Thickening



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

theorem enorm_le_of_hasWeakPartialsOn_ball_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → ∀ ξ ξs ξt : ℂ → E, Continuous ξ →
      tsupport ξ ⊆ ball c ρ → HasWeakPartialsOn (ball c ρ) ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict (ball c ρ)) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict (ball c ρ)) →
      ∀ z, ‖ξ z‖ₑ ≤ ENNReal.ofReal (C * ρ ^ (1 - 2 / p)) *
        (eLpNorm ξs (ENNReal.ofReal p) (volume.restrict (ball c ρ)) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict (ball c ρ))) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC⟩ := enorm_le_of_contDiff_tsupport_ball (E := E) p hp
  refine ⟨C, ?_⟩
  intro c r hr ξ ξs ξt hξ hsub hW hs ht z
  set U := ball c r with hUdef
  have hU : IsOpen U := isOpen_ball
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact ENNReal.one_le_ofReal.2 (by linarith)
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : HasCompactSupport ξ :=
    (isCompact_closedBall c r).of_isClosed_subset (isClosed_tsupport ξ)
      (hsub.trans ball_subset_closedBall)
  set K := tsupport ξ with hK
  have hKm : MeasurableSet K := (isClosed_tsupport ξ).measurableSet
  obtain ⟨hWu, hae⟩ := HasWeakPartialsOn.univ_indicator_tsupport hU hq1 hξ hc hsub hW hs ht
  set gs := K.indicator ξs with hgs
  set gt := K.indicator ξt with hgt
  have hrestr : ∀ {f : ℂ → E}, MemLp f q (volume.restrict U) → MemLp (K.indicator f) q volume :=
    fun hf => (memLp_indicator_iff_restrict hKm).2
      (hf.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hgsL : MemLp gs q volume := hrestr hs
  have hgtL : MemLp gt q volume := hrestr ht
  have hae' := (ae_restrict_iff' hU.measurableSet).1 hae
  have hLs : eLpNorm ξs q (volume.restrict U) = eLpNorm gs q volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae'] with z hz
    by_cases hzU : z ∈ U
    · rw [Set.indicator_of_mem hzU]; exact (hz hzU).1
    · have hzK : z ∉ K := fun h => hzU (hsub h)
      rw [Set.indicator_of_notMem hzU, hgs, Set.indicator_of_notMem hzK]
  have hLt : eLpNorm ξt q (volume.restrict U) = eLpNorm gt q volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae'] with z hz
    by_cases hzU : z ∈ U
    · rw [Set.indicator_of_mem hzU]; exact (hz hzU).2
    · have hzK : z ∉ K := fun h => hzU (hsub h)
      rw [Set.indicator_of_notMem hzU, hgt, Set.indicator_of_notMem hzK]
  -- a margin between the support and the boundary of the disc
  obtain ⟨δ, hδ, hδsub⟩ := hc.isCompact.exists_cthickening_subset_open hU hsub
  -- mollifiers
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
      by gcongr; norm_num⟩
  have hφr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    show Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hξli : LocallyIntegrable ξ volume := hξ.locallyIntegrable
  have hlimz : Tendsto (fun n => ‖((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] ξ) z‖ₑ) atTop
      (𝓝 ‖ξ z‖ₑ) :=
    (continuous_enorm.tendsto _).comp
      (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφr hξ z)
  have hbound : ∀ n, (φ n).rOut < δ →
      ‖((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] ξ) z‖ₑ ≤ ENNReal.ofReal (C * r ^ (1 - 2 / p)) *
        (eLpNorm ξs q (volume.restrict U) + eLpNorm ξt q (volume.restrict U)) := by
    intro n hn
    have hwc : HasCompactSupport ((φ n).normed volume) := (φ n).hasCompactSupport_normed
    have hcd : ContDiff ℝ 1 ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] ξ) :=
      hwc.contDiff_convolution_left (lsmul ℝ ℝ) (φ n).contDiff_normed hξli
    have hts : tsupport ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] ξ) ⊆ U := by
      refine (closure_minimal ?_ isClosed_cthickening).trans hδsub
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
      rw [(φ n).support_normed_eq, mem_ball, dist_zero_right] at ha
      refine mem_cthickening_of_dist_le _ b δ K (subset_tsupport _ hb) ?_
      rw [dist_eq_norm, add_sub_cancel_right]
      exact (ha.trans hn).le
    have h1 := hC c r hr _ hcd hts z
    have hd := fun y => fderiv_normed_convolution_eq_of_hasWeakPartialsOn (φ n) hWu hξli y
    simp only [fun y => (hd y).1, fun y => (hd y).2] at h1
    refine h1.trans ?_
    rw [hLs, hLt]
    gcongr
    · exact eLpNorm_normed_convolution_le (φ n) hq1 hqt hgsL.1
    · exact eLpNorm_normed_convolution_le (φ n) hq1 hqt hgtL.1
  exact le_of_tendsto hlimz ((hφr.eventually (gt_mem_nhds hδ)).mono hbound)

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → ∀ ξ ξs ξt : ℂ → E, Continuous ξ →
      tsupport ξ ⊆ ball c ρ → HasWeakPartialsOn (ball c ρ) ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict (ball c ρ)) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict (ball c ρ)) →
      ∀ z, ‖ξ z‖ₑ ≤ ENNReal.ofReal (C * ρ ^ (1 - 2 / p)) *
        (eLpNorm ξs (ENNReal.ofReal p) (volume.restrict (ball c ρ)) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict (ball c ρ))) :=
  enorm_le_of_hasWeakPartialsOn_ball_aux p hp
