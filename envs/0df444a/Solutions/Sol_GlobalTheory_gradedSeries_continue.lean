-- Prove2me | solution 1 for GlobalTheory.gradedSeries_continue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:59.798221+00:00
-- url     : https://prove2.me/submissions/0ff486a8-700f-47d4-bc62-d3c655fefc09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GradedSeriesContinuationDominated
import Theorems.Thm_GlobalTheory_gradedSeries_regroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Metric Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} (deg : ι → ℕ) (c : ι → ℂ) (δ ρ : ℝ) (Q : ℂ → ℂ)
    (hδ : 0 < δ) (hQ : DifferentiableOn ℂ Q (ball 0 ρ))
    (h : ∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => c i * (x : ℂ) ^ deg i) (Q x))
    (X : ℂ) (hX : ‖X‖ < ρ) :
    HasSum (fun k => (∑' i : deg ⁻¹' {k}, c i) * X ^ k) (Q X) := by
  set A : ℕ → ℂ := fun k => ∑' i : deg ⁻¹' {k}, c i with hAdef
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ A with hpdef
  have hx0 : 0 < δ / 2 := by positivity
  set x0 : NNReal := ⟨δ / 2, hx0.le⟩ with hx0def
  have hrad : (x0 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm
    have hs := (gradedSeries_regroup deg c _ _ (h (δ / 2) hx0 (by linarith))).summable
    have hs' := summable_norm_iff.mpr hs
    refine hs'.congr fun n => ?_
    simp only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0]
    rfl
  have hF := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (ENNReal.coe_pos.2 (by rw [← NNReal.coe_pos]; exact hx0)) hrad)
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  have hs0 : 0 < min (δ / 2) ρ := lt_min hx0 hρ
  have hQan : AnalyticOnNhd ℂ Q (ball 0 ρ) := hQ.analyticOnNhd isOpen_ball
  have hmem : ∀ z : ℂ, ‖z‖ < δ / 2 → z ∈ EMetric.ball (0 : ℂ) p.radius := by
    intro z hz
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    refine lt_of_lt_of_le ?_ hrad
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; exact hz)
  have hFan : AnalyticOnNhd ℂ p.sum (ball 0 (min (δ / 2) ρ)) := fun z hz =>
    hF.analyticAt_of_mem (hmem z (lt_of_lt_of_le (by simpa using hz) (min_le_left _ _)))
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = Q z := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hx0] with x hx
    have h1 := gradedSeries_regroup deg c _ _ (h x hx.1 (by linarith [hx.2]))
    simp only [p, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact h1.tsum_eq
  have heq : EqOn p.sum Q (ball 0 (min (δ / 2) ρ)) :=
    hFan.eqOn_of_preconnected_of_frequently_eq
      (hQan.mono (ball_subset_ball (min_le_right _ _)))
      (convex_ball _ _).isPreconnected (mem_ball_self hs0) hfreq
  have hQp : HasFPowerSeriesAt Q p 0 :=
    hF.hasFPowerSeriesAt.congr (Filter.eventuallyEq_of_mem (ball_mem_nhds 0 hs0) heq)
  have hR0 : 0 < (‖X‖ + ρ) / 2 := by positivity
  set R : NNReal := ⟨(‖X‖ + ρ) / 2, hR0.le⟩ with hRdef
  have hR : 0 < R := by rw [← NNReal.coe_pos]; exact hR0
  have hdR : DifferentiableOn ℂ Q (closedBall 0 R) :=
    hQ.mono (closedBall_subset_ball (by change (‖X‖ + ρ) / 2 < ρ; linarith))
  have hC := hdR.hasFPowerSeriesOnBall hR
  have hCp : cauchyPowerSeries Q 0 R = p := hC.hasFPowerSeriesAt.eq_formalMultilinearSeries hQp
  rw [hCp] at hC
  have hXm : X ∈ EMetric.ball (0 : ℂ) R := by
    change edist _ (0 : ℂ) < _
    rw [edist_zero_right]
    exact ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, coe_nnnorm]; change ‖X‖ < (‖X‖ + ρ) / 2; linarith)
  have := hC.hasSum hXm
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this
  exact this
end GlobalTheory
