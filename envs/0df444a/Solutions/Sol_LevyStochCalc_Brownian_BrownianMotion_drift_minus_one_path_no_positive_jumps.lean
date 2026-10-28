-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_path_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:06:25.742997+00:00
-- url     : https://prove2.me/submissions/50f93ef1-0d92-47d8-a6d4-33359a20a1c6

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  have hr : Continuous (fun t : ℝ => W.W t ω - t) :=
    hpath.sub continuous_id
  have hn : Continuous (fun t : ℝ≥0 => W.W (t : ℝ) ω - (t : ℝ)) :=
    hr.comp continuous_subtype_val
  intro t l ht hl
  haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hcont : Tendsto (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ))
      (𝓝[<] t) (𝓝 (W.W (t : ℝ) ω - (t : ℝ))) :=
    (hn.tendsto t).mono_left inf_le_left
  exact le_of_eq (tendsto_nhds_unique hcont hl)
