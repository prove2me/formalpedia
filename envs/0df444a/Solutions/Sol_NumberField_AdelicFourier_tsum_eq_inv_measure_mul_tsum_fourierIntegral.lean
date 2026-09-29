-- Prove2me | solution 1 for NumberField.AdelicFourier.tsum_eq_inv_measure_mul_tsum_fourierIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8fedfd6c-8e58-5708-936b-4af220a9dfd0

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral

open NumberField NumberField.AdelicFourier AutomorphicForm

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ)⁻¹ *
          ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by

  have h := NumberField.AdelicFourier.tsum_translate_eq_inv_measure_mul_tsum_fourierIntegral
    F μ hψ hf 0
  simpa only [zero_add, mul_zero, AddChar.map_zero_eq_one, mul_one] using h

end S_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral
end P2MW
export P2MW.S_NumberField_AdelicFourier_tsum_eq_inv_measure_mul_tsum_fourierIntegral (solution)
