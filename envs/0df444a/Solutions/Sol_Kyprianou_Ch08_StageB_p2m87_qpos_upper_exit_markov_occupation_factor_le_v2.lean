-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T03:55:24.880468+00:00
-- url     : https://prove2.me/submissions/2b37a1b1-e782-4816-be49-3d907f82042d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_upper_exit_markov_occupation_factor_le_v2_no_scale_family
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
              tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
        ENNReal.ofReal (upBeforeDownExpectation P D.X q x a) *
          (∫⁻ t : ℝ≥0,
            ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
              P {ω | (t : WithTop ℝ≥0) <
                tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue) := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA
  exact Kyprianou.Ch08.StageB.p2m87_qpos_upper_exit_markov_occupation_factor_le_v2_no_scale_family
    Ω P D ψ hψ q a x hq ha hx hxa A hA
