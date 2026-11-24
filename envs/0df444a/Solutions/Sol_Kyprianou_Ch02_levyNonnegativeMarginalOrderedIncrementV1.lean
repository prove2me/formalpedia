-- Prove2me | solution 1 for Kyprianou.Ch02.levyNonnegativeMarginalOrderedIncrementV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:39:15.042633+00:00
-- url     : https://prove2.me/submissions/c8dec7ed-cda3-4c98-b81a-47832c0d9ae0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hm : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, X s ω ≤ X t ω := by
  have hzero (ω : Ω) : X 0 ω = 0 := congrFun hX.start_zero ω
  have hid := hX.stationary_increments s (t - s)
  have hsum : s + (t - s) = t := add_tsub_cancel_of_le hst
  rw [hsum] at hid
  have hpos : ∀ᵐ ω ∂P, increment X 0 (t - s) ω ∈ Set.Ici (0 : ℝ) := by
    filter_upwards [hm (t - s)] with ω hω
    simpa [increment, hzero ω] using hω
  have hpos' : ∀ᵐ ω ∂P, increment X s t ω ∈ Set.Ici (0 : ℝ) := by
    first
    | exact hid.symm.ae_mem_snd measurableSet_Ici hpos
    | exact hid.symm.ae_mem_snd hpos measurableSet_Ici
    | exact hid.symm.ae_mem_snd hpos
  filter_upwards [hpos'] with ω hω
  exact sub_nonneg.mp hω
