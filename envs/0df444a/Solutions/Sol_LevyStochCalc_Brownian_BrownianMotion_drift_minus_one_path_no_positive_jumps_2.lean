-- Prove2me | solution 2 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_path_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:06:45.478746+00:00
-- url     : https://prove2.me/submissions/3ad4c45f-7415-46c3-aa71-ecdcf2feabd9

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic

open MeasureTheory Filter Set Topology
open scoped NNReal
open LevyStochCalc.Brownian
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (ω : Ω) (hpath : Continuous (fun t : ℝ => W.W t ω)) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) (𝓝[<] t) (𝓝 l) →
      W.W (t : ℝ) ω - (t : ℝ) ≤ l := by
  intro t l ht hl
  have hc : Continuous (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) :=
    (hpath.comp NNReal.continuous_coe).sub NNReal.continuous_coe
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have h2 := (hc.continuousAt (x := t)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t))
  exact (tendsto_nhds_unique h2 hl).le
