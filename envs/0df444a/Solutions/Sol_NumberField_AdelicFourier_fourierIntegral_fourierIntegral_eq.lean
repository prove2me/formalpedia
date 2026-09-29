-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/363bd7ec-b44f-531c-b30b-044fdd358d99

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

open NumberField NumberField.AdelicFourier AutomorphicForm

set_option maxHeartbeats 3200000 in

theorem solution (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) (x : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fourierIntegral ψ μ f) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * f (-x) := by

  have hψu : ∀ y, ‖ψ y‖ = 1 := NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ
  have hInt : ∀ {g : AdeleRing (𝓞 F) F → ℂ} (_ : g ∈ schwartzBruhat F) (w : AdeleRing (𝓞 F) F),
      MeasureTheory.Integrable (fun v => ψ (-(v * w)) * g v) μ := by
    intro g hg w
    have h1 : MeasureTheory.Integrable g μ := NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat F μ hg
    refine h1.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact ((hψ.continuous.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable).mul
        h1.aestronglyMeasurable
    · rw [norm_mul, hψu, one_mul]

  have hadd : ∀ {g₁ g₂ : AdeleRing (𝓞 F) F → ℂ}, g₁ ∈ schwartzBruhat F → g₂ ∈ schwartzBruhat F →
      fourierIntegral ψ μ (g₁ + g₂) = fourierIntegral ψ μ g₁ + fourierIntegral ψ μ g₂ := by
    intro g₁ g₂ h₁ h₂
    funext w
    rw [Pi.add_apply, fourierIntegral_add ψ μ w (hInt h₁ w) (hInt h₂ w)]

  revert x
  refine schwartzBruhat_induction (p := fun g _ => ∀ x, fourierIntegral ψ μ (fourierIntegral ψ μ g) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * g (-x)) ?_ ?_ ?_ ?_ hf
  ·
    intro g hg x
    exact NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet F μ hψ hg x
  ·
    intro x
    rw [fourierIntegral_zero, fourierIntegral_zero]
    simp
  ·
    intro g₁ g₂ h₁ h₂ ih₁ ih₂ x
    have h₁' := NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat F μ hψ h₁
    have h₂' := NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat F μ hψ h₂
    rw [hadd h₁ h₂, hadd h₁' h₂', Pi.add_apply, ih₁ x, ih₂ x, Pi.add_apply]
    ring
  ·
    intro c g hg ih x
    rw [fourierIntegral_smul, fourierIntegral_smul, Pi.smul_apply, ih x, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring

end S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq (solution)
