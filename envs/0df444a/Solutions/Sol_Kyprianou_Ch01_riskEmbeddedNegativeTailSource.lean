-- Prove2me | solution 1 for Kyprianou.Ch01.riskEmbeddedNegativeTailSource
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:51:40.713052+00:00
-- url     : https://prove2.me/submissions/d371b1ab-a439-4a48-9275-8c4504980407

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
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
    ∀ z : ℝ, 0 < z →
      (mu (Set.Iio (-z))).toReal =
        (∫ e : ℝ, (F (Set.Ioi (e + z))).toReal ∂Ebeta) := by
  intro Ebeta mu z hz
  have hm : Measurable (fun p : ℝ × ℝ => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  have hs : MeasurableSet ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹'
      Set.Iio (-z)) := hm measurableSet_Iio
  have hsec (e : ℝ) :
      F ((Prod.mk e) ⁻¹'
        ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Iio (-z))) =
      F (Set.Ioi (e + z)) := by
    congr 1
    ext u
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  change (((Ebeta.prod F).map
    (fun pair : ℝ × ℝ => pair.1 - pair.2)) (Set.Iio (-z))).toReal = _
  rw [Measure.map_apply hm measurableSet_Iio, Measure.prod_apply hs]
  have hfinite : ∀ᵐ e : ℝ ∂Ebeta,
      F ((Prod.mk e) ⁻¹'
        ((fun p : ℝ × ℝ => p.1 - p.2) ⁻¹' Set.Iio (-z))) < ⊤ := by
    exact Filter.Eventually.of_forall (fun e : ℝ =>
      (lt_top_iff_ne_top).2 (measure_ne_top F _))
  rw [← integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
    hfinite]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [hsec e]
