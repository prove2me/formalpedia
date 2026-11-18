-- Prove2me | solution 1 for Kyprianou.Ch01.riskEmbeddedPositiveTailSource
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:57:40.259195+00:00
-- url     : https://prove2.me/submissions/56ebdccf-97c8-4444-9c53-504a001a155e

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_Kyprianou_Ch01_expDensityIoiTail
import Theorems.Thm_Kyprianou_Ch01_riskPositiveTailPushforward
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hClaims : F (Set.Iic (0 : ℝ)) = 0) :
    let Ebeta : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun e : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * e)))
    let mu : Measure ℝ :=
      (Ebeta.prod F).map (fun pair : ℝ × ℝ => pair.1 - pair.2)
    ∀ z : ℝ, 0 ≤ z →
      (mu (Set.Ioi z)).toReal =
        Real.exp (-beta * z) * (∫ u : ℝ, Real.exp (-beta * u) ∂F) := by
  intro Ebeta mu z hz
  have hclaims : ∀ᵐ u : ℝ ∂F, 0 < u := by
    rw [ae_iff]
    simpa only [not_lt, Set.Iic] using hClaims
  have htop : Ebeta (Set.Ioi (0 : ℝ)) < ⊤ := by
    have ht : (Ebeta (Set.Ioi (0 : ℝ))).toReal = 1 := by
      simpa [Ebeta] using
        (Kyprianou.Ch01.expDensityIoiTail beta hbeta 0 le_rfl)
    apply (lt_top_iff_ne_top).2
    intro h
    simp [h] at ht
  have hfinite : ∀ᵐ u : ℝ ∂F, Ebeta (Set.Ioi (z + u)) < ⊤ := by
    filter_upwards [hclaims] with u hu
    exact lt_of_le_of_lt (measure_mono (show
      Set.Ioi (z + u) ⊆ Set.Ioi 0 by
        intro e he
        change z + u < e at he
        change 0 < e
        linarith)) htop
  have hmeas : Measurable (fun u : ℝ => Ebeta (Set.Ioi (z + u))) := by
    apply Antitone.measurable
    intro u v huv
    exact measure_mono (show Set.Ioi (z + v) ⊆ Set.Ioi (z + u) by
      intro e he
      change z + v < e at he
      change z + u < e
      linarith)
  have hp := Kyprianou.Ch01.riskPositiveTailPushforward beta F z
  change (mu (Set.Ioi z)).toReal = _
  rw [hp, ← integral_toReal hmeas.aemeasurable hfinite]
  calc
    (∫ u : ℝ, (Ebeta (Set.Ioi (z + u))).toReal ∂F)
      = ∫ u : ℝ, Real.exp (-beta * (z + u)) ∂F := by
        apply integral_congr_ae
        filter_upwards [hclaims] with u hu
        exact Kyprianou.Ch01.expDensityIoiTail beta hbeta (z + u)
          (add_nonneg hz hu.le)
    _ = Real.exp (-beta * z) * (∫ u : ℝ, Real.exp (-beta * u) ∂F) := by
        simp_rw [show ∀ u : ℝ, Real.exp (-beta * (z + u)) =
          Real.exp (-beta * z) * Real.exp (-beta * u) by
            intro u
            rw [show -beta * (z + u) = -beta * z + -beta * u by ring, Real.exp_add]]
        rw [integral_const_mul]
