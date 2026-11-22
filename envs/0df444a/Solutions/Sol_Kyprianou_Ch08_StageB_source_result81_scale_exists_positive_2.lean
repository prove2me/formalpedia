-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result81_scale_exists_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:07:52.586401+00:00
-- url     : https://prove2.me/submissions/f18a8b9a-f86c-446d-abfb-ca129f7744d0

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_normalized_scale_at_discount
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∃ W : ℝ → ℝ → ℝ, HasSourceScaleFamily ψ W ∧
      ∀ q a : ℝ, 0 ≤ q → 0 < a → 0 < W q a := by
  classical
  have hEx : ∀ q : ℝ, 0 ≤ q → ∃ w : ℝ → ℝ, IsQScale ψ q w := fun q hq =>
    Kyprianou.Ch08.StageB.source_result81_normalized_scale_at_discount Ω P D ψ hψ q hq
  have hAll : ∀ q : ℝ, ∃ w : ℝ → ℝ, (0 ≤ q → IsQScale ψ q w) := by
    intro q
    by_cases hq : 0 ≤ q
    · obtain ⟨w, hw⟩ := hEx q hq
      exact ⟨w, fun _ => hw⟩
    · exact ⟨fun _ => 0, fun hle => absurd hle hq⟩
  choose W hW using hAll
  obtain ⟨K, hK0, hgrow⟩ :=
    Kyprianou.Ch08.StageB.source_result81_exponent_quadratic_upper Ω P D ψ hψ
  have hFam : HasSourceScaleFamily ψ W := fun q hq => hW q hq
  refine ⟨W, hFam, fun q a hq ha => ?_⟩
  exact Kyprianou.Ch08.StageB.source_result81_scale_positive_from_quadratic
    ψ q (W q) (hW q hq) K hK0 hgrow a ha
