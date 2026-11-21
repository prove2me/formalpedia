-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_weak_moment_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:25:09.484183+00:00
-- url     : https://prove2.me/submissions/66b8a304-a20c-4089-85c4-bd28f2ccafee

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open MeasureTheory Filter
open scoped ENNReal Topology
set_option autoImplicit false

theorem solution
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hweak : Tendsto μs atTop (nhds μ))
    (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    (hint : ∀ n, Integrable f (μs n : Measure ℝ)) (C L : ℝ)
    (hsq : ∀ᶠ n in atTop, Integrable (fun x => f x ^ 2) (μs n : Measure ℝ) ∧
      (∫ x, f x ^ 2 ∂(μs n : Measure ℝ)) ≤ C)
    (hL : Tendsto (fun n => ∫ x, f x ∂(μs n : Measure ℝ)) atTop (nhds L)) :
    Integrable f (μ : Measure ℝ) ∧ (∫ x, f x ∂(μ : Measure ℝ)) = L := by
  have hnon : ∀ n, 0 ≤ ∫ x, f x ∂(μs n : Measure ℝ) := fun _ => integral_nonneg hfn
  have hL0 : 0 ≤ L := ge_of_tendsto' hL hnon
  have hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂(μs n : Measure ℝ))
      atTop (nhds (ENNReal.ofReal L)) := by
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hint _) (Eventually.of_forall hfn)]
    exact (ENNReal.continuous_ofReal.tendsto L).comp hL
  have hle := (lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (μ : Measure ℝ)) (μs := fun n => (μs n : Measure ℝ)) hf hfn
    (fun _ hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hG)).trans_eq hlim.liminf_eq
  have hfi : Integrable f (μ : Measure ℝ) :=
    ⟨hf.measurable.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hfn)).2
      (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hfi, le_antisymm ?_ ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfn) hfi.aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofReal hL0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  · by_contra! hlt
    let δ := L - (∫ x, f x ∂(μ : Measure ℝ))
    have hδ : 0 < δ := sub_pos.mpr hlt
    let R := (|C| + 1) / δ
    have hR : 0 < R := div_pos (by positivity) hδ
    have hsmall : C / R < δ := by
      apply (div_lt_iff₀ hR).2
      have he : R * δ = |C| + 1 := div_mul_cancel₀ _ hδ.ne'
      nlinarith only [he, le_abs_self C]
    let g := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (f x) R)
      (hf.min continuous_const) R (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hfn x) hR.le)]
        exact min_le_right _ _)
    have hpoint (x : ℝ) : f x ≤ g x + f x ^ 2 / R := by
      change f x ≤ min (f x) R + f x ^ 2 / R
      apply sub_le_iff_le_add.mp
      refine le_min (sub_le_self _ (by positivity)) ?_
      have hq : f x - R ≤ f x ^ 2 / R := (le_div_iff₀ hR).2 (by
        nlinarith only [sq_nonneg (f x - R), mul_nonneg (hfn x) hR.le])
      linarith only [hq]
    have hev : ∀ᶠ n in atTop, (∫ x, f x ∂(μs n : Measure ℝ)) - C / R ≤
        ∫ x, g x ∂(μs n : Measure ℝ) := by
      filter_upwards [hsq] with n hn
      have hg := BoundedContinuousFunction.integrable (μs n : Measure ℝ) g
      have hi := hn.1.div_const R
      have hv := integral_mono (hint n) (hg.add hi) hpoint
      simp only [Pi.add_apply, integral_add hg hi, integral_div] at hv
      linarith only [hv, div_le_div_of_nonneg_right hn.2 hR.le]
    have hlow := le_of_tendsto_of_tendsto (hL.sub_const (C / R))
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak g) hev
    have hu := integral_mono (BoundedContinuousFunction.integrable (μ : Measure ℝ) g) hfi
      (fun x => min_le_left (f x) R)
    dsimp [δ] at hsmall
    linarith only [hlow, hu, hsmall]
