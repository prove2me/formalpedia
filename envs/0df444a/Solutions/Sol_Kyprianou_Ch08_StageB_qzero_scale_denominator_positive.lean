-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_scale_denominator_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:16:37.877844+00:00
-- url     : https://prove2.me/submissions/95522fee-5900-411e-8663-d801aa2f843f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ a : ℝ, 0 < a → 0 < W 0 a := by
  intro Ω mΩ P hP D ψ W hψ hW a ha
  rcases source_result81_exponent_quadratic_upper Ω P D ψ hψ with ⟨K, hK, hgrowth⟩
  exact source_result81_scale_positive_from_quadratic ψ 0 (W 0) (hW 0 le_rfl)
    K hK hgrowth a ha
