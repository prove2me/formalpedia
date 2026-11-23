-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_up_before_down_excursion_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:29:05.441797+00:00
-- url     : https://prove2.me/submissions/82029b6e-05a8-4211-a843-d88e4536785c

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_slice_lower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_slice_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_limit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ) (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ x a : ℝ, 0 < x → x < a →
      upBeforeDownExpectation P D.X q x a =
        Real.exp (-(∫ t in x..a, Phi ψ q + (n (Set.Ici t)).toReal)) := by
  intro x a hx hxa
  have hLow := source_result8_2_v2_bridge_slice_lower P D ψ hψ q hq n hLaw
  have hUp := source_result8_2_v2_bridge_slice_upper P D ψ hψ q hq n hLaw
  exact source_result8_2_v2_bridge_limit P D ψ hψ q hq n hLaw hLow hUp x a hx hxa
