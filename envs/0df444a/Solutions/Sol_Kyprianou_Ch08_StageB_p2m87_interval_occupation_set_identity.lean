-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_interval_occupation_set_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:44:34.52698+00:00
-- url     : https://prove2.me/submissions/cf59bb29-2469-43ca-a02e-2af3e123b80d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_interval_occupation_qpos_set_identity
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_interval_occupation_qzero_set_identity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

/-- Split the exact source occupation identity by zero or positive discount. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 ≤ q → 0 < a → 0 ≤ x → x ≤ a →
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
  rcases lt_or_eq_of_le hq with hpos | hzero
  · exact Kyprianou.Ch08.StageB.p2m87_interval_occupation_qpos_set_identity
      Ω P D ψ W hψ hW q a x hpos ha hx hxa A hA
  · exact Kyprianou.Ch08.StageB.p2m87_interval_occupation_qzero_set_identity
      Ω P D ψ W hψ hW q a x hzero.symm ha hx hxa A hA
