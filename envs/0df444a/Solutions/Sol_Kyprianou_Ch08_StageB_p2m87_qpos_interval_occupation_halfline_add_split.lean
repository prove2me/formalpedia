-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_interval_occupation_halfline_add_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:02:26.883743+00:00
-- url     : https://prove2.me/submissions/c58f262f-ffbf-4a5b-b661-b70a11f9bb9e

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_occupation_upper_exit_markov_bridge
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio
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
        (∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        (∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              min (tauMinus (shifted D.X x) 0 ω)
                (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) +
        ENNReal.ofReal (W q x / W q a) *
          (∫⁻ t : ℝ≥0,
            ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
              P {ω | (t : WithTop ℝ≥0) <
                tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA
  have hmarkov :=
    Kyprianou.Ch08.StageB.p2m87_qpos_occupation_upper_exit_markov_bridge
      Ω P D ψ W hψ hW q a x hq ha hx hxa A hA
  have hratio :=
    Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio
      Ω P D ψ hψ W hW q x a hq.le ha hxa
  rw [hratio] at hmarkov
  exact hmarkov
