-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_interval_occupation_qpos_set_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:48:09.058077+00:00
-- url     : https://prove2.me/submissions/a6632e0b-1960-4ddd-be71-98f8d73be3e4

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_halfline_occupation_qpos_set_identity
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_from_halfline_bridge
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Icc 0 a)).withDensity
      (fun y : ℝ => ENNReal.ofReal (killedIntervalDensity (W q) a x y))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            min (tauMinus (shifted D.X x) 0 ω)
              (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA
  exact Kyprianou.Ch08.StageB.p2m87_qpos_interval_from_halfline_bridge
    Ω P D ψ W hψ hW q a x hq ha hx hxa A hA
    (Kyprianou.Ch08.StageB.p2m88_halfline_occupation_qpos_set_identity
      Ω P D ψ W hψ hW q x hq hx A hA)
    (Kyprianou.Ch08.StageB.p2m88_halfline_occupation_qpos_set_identity
      Ω P D ψ W hψ hW q a hq ha.le A hA)
