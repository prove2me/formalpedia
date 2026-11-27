-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PositiveLeftWeightV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:55:59.622137+00:00
-- url     : https://prove2.me/submissions/64b5675f-572f-49e2-a6e8-5e9700ca639c

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Positive left-limit coordinates of a measurable process are a.e. measurable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y L : NNReal → Ω → ℝ) (f : ℝ → ℝ → ℝ)
    (hm : ∀ t, AEMeasurable (Y t) P)
    (hl : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (hf : ∀ t : NNReal, Continuous (f (t : ℝ))) :
    ∀ t : NNReal, AEMeasurable (fun w => if t = 0 then 0 else f (t : ℝ) (L t w)) P := by
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have ht' : 0 < t := pos_iff_ne_zero.mpr ht
  haveI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht'⟩
  have hL : AEMeasurable (L t) P := by
    apply aemeasurable_of_tendsto_metrizable_ae (nhdsWithin t (Iio t)) hm
    filter_upwards [hl] with w hw
    exact hw t ht'
  simp only [if_neg ht]
  change AEMeasurable (f (t : ℝ) ∘ L t) P
  exact (hf t).measurable.comp_aemeasurable hL
