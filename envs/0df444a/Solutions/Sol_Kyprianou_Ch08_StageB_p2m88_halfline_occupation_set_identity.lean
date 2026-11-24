-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_halfline_occupation_set_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:44:58.251811+00:00
-- url     : https://prove2.me/submissions/b7bf24ec-84d5-45d5-821e-c4a3a32d12b9

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_halfline_occupation_qpos_set_identity
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_halfline_occupation_qzero_set_identity
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
    ∀ (q x : ℝ), 0 ≤ q → 0 ≤ x →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici 0)).withDensity
      (fun y : ℝ => ENNReal.ofReal
        (killedHalflineDensity ψ q (W q) x y))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            tauMinus (shifted D.X x) 0 ω ∧
            shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW q x hq hx A hA
  rcases lt_or_eq_of_le hq with hpos | hzero
  · exact Kyprianou.Ch08.StageB.p2m88_halfline_occupation_qpos_set_identity
      Ω P D ψ W hψ hW q x hpos hx A hA
  · exact Kyprianou.Ch08.StageB.p2m88_halfline_occupation_qzero_set_identity
      Ω P D ψ W hψ hW q x hzero.symm hx A hA
