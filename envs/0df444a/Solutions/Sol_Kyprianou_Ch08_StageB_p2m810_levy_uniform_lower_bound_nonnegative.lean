-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_levy_uniform_lower_bound_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:37:48.710923+00:00
-- url     : https://prove2.me/submissions/d2964782-1a46-4013-b946-9cbad0e85966

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_uniform_lower_bound_threshold
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
/-- Independent increment reduction. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess X P →
      ∀ a : ℝ, (∀ t : ℝ≥0, ∀ᵐ ω ∂P, -a ≤ X t ω) →
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω := by
  intro Ω mΩ P hP X hX a hb t
  have h (n : ℕ) : ∀ᵐ ω ∂P, -(1/((n:ℝ)+1)) ≤ X t ω :=
    p2m810_uniform_lower_bound_threshold Ω P X hX a _ t (neg_lt_zero.mpr (by positivity)) hb
  filter_upwards [ae_all_iff.2 h] with ω hw
  have hl := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hl' : Tendsto (fun n : ℕ => -(1/((n:ℝ)+1))) atTop (nhds 0) := by simpa using hl
  exact le_of_tendsto hl' (Filter.Eventually.of_forall hw)
