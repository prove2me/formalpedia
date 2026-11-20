-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:56:07.827738+00:00
-- url     : https://prove2.me/submissions/ab30db32-a956-46f6-980d-be2475b8691a

import Definitions.Def_LevyStochCalc_Probability_LevyProkhorovLipschitz_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrals of Lipschitz functions under the Lévy–Prokhorov metric

For probability measures `μ`, `ν` on a pseudo-metric space and a nonnegative bounded continuous
`K`-Lipschitz function `g`,
`|∫ g dμ - ∫ g dν| ≤ (K + ‖g‖) · levyProkhorovDist μ ν`.

By the layer-cake formula, `∫ g dμ` is bounded by the integral over `t ∈ (0, ‖g‖]` of the
`ν`-mass of the `ε`-thickening of `{t ≤ g}`, plus `ε ‖g‖`, whenever the Lévy–Prokhorov distance
is below `ε`. Since `g` is `K`-Lipschitz, that thickening lies inside `{t - K ε ≤ g}`, and shifting
the layer-cake integral by `K ε` costs at most `K ε`.

## Main statements

* `LevyStochCalc.Probability.thickening_setOf_le_subset` — the `ε`-thickening of a superlevel set
  `{t ≤ f}` of a `K`-Lipschitz function lies in `{t - K ε ≤ f}`.
* `LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt` — the one-sided
  bound `∫ g dμ ≤ ∫ g dν + ε (K + ‖g‖)` when `levyProkhorovEDist μ ν < ε`.
* `LevyStochCalc.Probability.abs_integral_sub_integral_le_levyProkhorovDist` — the two-sided
  bound `|∫ g dμ - ∫ g dν| ≤ (K + ‖g‖) · levyProkhorovDist μ ν`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω : Type*} [PseudoMetricSpace Ω]

variable [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

theorem _root_.solution {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (g : Ω →ᵇ ℝ) {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg_nn : ∀ x, 0 ≤ g x) {ε : ℝ} (hε : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) :
    ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν + ε * (K + ‖g‖) := by
  set c : ℝ := (K : ℝ) * ε with hc
  have hc0 : 0 ≤ c := mul_nonneg K.2 hε.le
  set h : Ω →ᵇ ℝ := g + BoundedContinuousFunction.const Ω c with hh
  have hhx : ∀ x, h x = g x + c := fun x => rfl
  have hh_nn : ∀ x, 0 ≤ h x := fun x => by rw [hhx]; linarith [hg_nn x]
  have hnorm : ‖g‖ ≤ ‖h‖ := by
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]
    calc g x ≤ h x := by rw [hhx]; linarith
      _ ≤ |h x| := le_abs_self _
      _ = ‖h x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖h‖ := h.norm_coe_le_norm x
  have step1 := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt μ ν hε hμν g
    (ae_of_all _ hg_nn)
  have hint : ∀ M : ℝ, IntegrableOn (fun t ↦ ν.real {a | t ≤ h a}) (Ioc 0 M) := by
    intro M
    apply Measure.integrableOn_of_bounded (M := ν.real univ) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono (fun _ h ↦ hst.trans h)
    · apply Eventually.of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (subset_univ _)
  have hint2 : IntegrableOn (fun t ↦ ν.real (Metric.thickening ε {a | t ≤ g a})) (Ioc 0 ‖g‖) := by
    apply Measure.integrableOn_of_bounded (M := ν.real univ) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst ↦ measure_mono <| Metric.thickening_subset_of_subset ε (fun _ h ↦ hst.trans h)
    · apply Eventually.of_forall <| fun t ↦ ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact ENNReal.toReal_mono (by finiteness) <| measure_mono (subset_univ _)
  have step2 : ∫ t in Ioc 0 ‖g‖, ν.real (Metric.thickening ε {a | t ≤ g a})
      ≤ ∫ t in Ioc 0 ‖g‖, ν.real {a | t ≤ h a} := by
    refine setIntegral_mono hint2 (hint _) fun t => ?_
    refine measureReal_mono (fun x hx => ?_)
    have := thickening_setOf_le_subset hg ε t hx
    simp only [mem_setOf_eq] at this ⊢
    rw [hhx]; linarith
  have step3 : ∫ t in Ioc 0 ‖g‖, ν.real {a | t ≤ h a} ≤ ∫ t in Ioc 0 ‖h‖, ν.real {a | t ≤ h a} :=
    setIntegral_mono_set (hint _) (ae_of_all _ fun _ => measureReal_nonneg)
      (Eventually.of_forall (Ioc_subset_Ioc_right hnorm))
  have step4 : ∫ x, h x ∂ν = ∫ x, g x ∂ν + c := by
    simp only [hhx]
    rw [integral_add (g.integrable ν) (integrable_const c)]
    simp
  rw [← BoundedContinuousFunction.integral_eq_integral_meas_le h ν (ae_of_all _ hh_nn), step4] at step3
  nlinarith [step1, step2, step3]

end LevyStochCalc.Probability
