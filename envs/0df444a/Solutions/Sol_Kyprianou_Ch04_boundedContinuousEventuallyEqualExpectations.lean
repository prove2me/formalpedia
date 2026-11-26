-- Prove2me | solution 1 for Kyprianou.Ch04.boundedContinuousEventuallyEqualExpectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:26.014776+00:00
-- url     : https://prove2.me/submissions/f82b866d-26cf-47fe-8c97-935d456ab84c

import Mathlib
open MeasureTheory Filter
open scoped NNReal Topology
set_option autoImplicit false

/-- Almost-sure eventual equality makes bounded continuous expectations asymptotically equal. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D W : NNReal → Ω → ℝ)
    (hD : ∀ t, Measurable (D t)) (hW : ∀ t, Measurable (W t))
    (he : ∀ᵐ z ∂P, ∀ᶠ t in atTop, W t z = D t z)
    (f : BoundedContinuousFunction ℝ ℝ) (a : ℝ)
    (hlim : Tendsto (fun t => ∫ z, f (D t z) ∂P) atTop (nhds a)) :
    Tendsto (fun t => ∫ z, f (W t z) ∂P) atTop (nhds a) := by
  have h : Tendsto (fun t : NNReal => ∫ z, (f (W t z)-f (D t z)) ∂P)
      atTop (nhds (∫ _ : Ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ‖f‖)
    · exact Eventually.of_forall fun t =>
        ((f.continuous.measurable.comp (hW t)).sub (f.continuous.measurable.comp (hD t))).aestronglyMeasurable
    · exact Eventually.of_forall fun t => Eventually.of_forall fun z => by
        calc
          ‖f (W t z)-f (D t z)‖ ≤ ‖f (W t z)‖+‖f (D t z)‖ := norm_sub_le _ _
          _ ≤ 2*‖f‖ := by linarith [f.norm_coe_le_norm (W t z),f.norm_coe_le_norm (D t z)]
    · exact integrable_const _
    · filter_upwards [he] with z hz
      apply tendsto_const_nhds.congr'
      filter_upwards [hz] with t ht
      simp [ht]
  simp only [integral_zero] at h
  have hint (g : Ω → ℝ) (hg : Measurable g) : Integrable (fun z => f (g z)) P :=
    (integrable_const ‖f‖).mono ((f.continuous.measurable.comp hg).aestronglyMeasurable)
      (Eventually.of_forall fun z => by simpa using f.norm_coe_le_norm (g z))
  have hh := h.add hlim
  rw [zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [integral_sub (hint _ (hW t)) (hint _ (hD t))]
    ring
