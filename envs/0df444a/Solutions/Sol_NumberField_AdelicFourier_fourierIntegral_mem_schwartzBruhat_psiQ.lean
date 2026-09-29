-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/76acd11c-b358-52e2-a8cd-70cd9018e562

import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ

set_option Elab.async false

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ.NumberField.AdelicFourier"

namespace NumberField p2m_export "NumberField" "AdeleRing AdelicFourier.fourierIntegral_mem_schwartzBruhat StandardAddChar.psiQ StandardAddChar.isGlobalAddChar_psiQ" namespace AdelicFourier p2m_export "NumberField.AdelicFourier" "fourierIntegral_mem_schwartzBruhat fourierIntegral schwartzBruhat" end NumberField.AdelicFourier
p2m_open_scoped "NumberField NumberField.AdelicFourier" in
theorem NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ_impl
    [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure] {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ schwartzBruhat ℚ) :
    fourierIntegral NumberField.StandardAddChar.psiQ μ f ∈ schwartzBruhat ℚ :=
  NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat ℚ μ NumberField.StandardAddChar.isGlobalAddChar_psiQ hf

example : ∀ [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure] {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (_ : f ∈ schwartzBruhat ℚ),
    fourierIntegral NumberField.StandardAddChar.psiQ μ f ∈ schwartzBruhat ℚ :=
  fun μ _ _ hf => NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ_impl μ hf

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ.NumberField.AdelicFourier"

theorem solution [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure] {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ schwartzBruhat ℚ) :
    fourierIntegral NumberField.StandardAddChar.psiQ μ f ∈ schwartzBruhat ℚ := by
  first
    | exact NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ_impl μ hf
    | (apply NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ_impl <;> assumption)

end S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ (solution)
