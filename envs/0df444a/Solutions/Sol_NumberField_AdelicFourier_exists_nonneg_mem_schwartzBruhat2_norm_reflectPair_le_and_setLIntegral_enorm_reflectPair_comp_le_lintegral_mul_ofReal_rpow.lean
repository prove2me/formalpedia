-- Prove2me | solution 1 for NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/5cd0d103-c1ba-59be-9bc8-2ff37029e872

import Theorems.Thm_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
import Theorems.Thm_NumberField_AdelicFourier_fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier AutomorphicForm
open scoped ENNReal

namespace ReflectFinE9

variable {F : Type} [Field F] [NumberField F]

theorem setLIntegral_enorm_le_of_norm_le {T : Type} [MeasurableSpace T] (τ : Measure T)
    (f : T → ℂ) (b : T → ℝ) (hfb : ∀ t, ‖f t‖ ≤ b t)
    (N : T → ℝ) (hN : MeasurableSet {t | 1 ≤ N t}) (s : ℝ) (hs : 0 ≤ s) :
    ∫⁻ t in {t | 1 ≤ N t}, ‖f t‖ₑ ∂τ ≤ ∫⁻ t, ENNReal.ofReal (b t) * ENNReal.ofReal (N t ^ s) ∂τ := by
  refine le_trans (setLIntegral_mono' hN fun t ht => ?_) (setLIntegral_le_lintegral _ _)
  have h1 : (1 : ℝ) ≤ N t ^ s := Real.one_le_rpow ht hs
  have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (N t ^ s) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
  calc ‖f t‖ₑ = ENNReal.ofReal ‖f t‖ := (ofReal_norm (f t)).symm
    _ ≤ ENNReal.ofReal (b t) := ENNReal.ofReal_le_ofReal (hfb t)
    _ = ENNReal.ofReal (b t) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (b t) * ENNReal.ofReal (N t ^ s) := by gcongr

end ReflectFinE9

open ReflectFinE9 in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ, Ψ ∈ schwartzBruhat2 F ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, 0 ≤ (Ψ x).re ∧ (Ψ x).im = 0) ∧
      (∀ x : Fin 2 → AdeleRing (𝓞 F) F, ‖reflectPair ψ μ₁ Φ x‖ ≤ (Ψ x).re) ∧
      ∀ (T : Type) [MeasurableSpace T] (τ : Measure T) (col : T → (Fin 2 → AdeleRing (𝓞 F) F))
        (N : T → ℝ), MeasurableSet {t | 1 ≤ N t} → ∀ s : ℝ, 0 ≤ s →
          ∫⁻ t in {t | 1 ≤ N t}, ‖reflectPair ψ μ₁ Φ (col t)‖ₑ ∂τ ≤
            ∫⁻ t, ENNReal.ofReal (Ψ (col t)).re * ENNReal.ofReal (N t ^ s) ∂τ := by
  have hΦ' : reflectPair ψ μ₁ Φ ∈ schwartzBruhat2 F :=
    (NumberField.AdelicFourier.fourierTransform2_mem_schwartzBruhat2_and_reflectPair_mem_schwartzBruhat2
      F μ₁ hψ hΦ).2
  obtain ⟨Ψ, hΨ, hreal, hdom, -⟩ :=
    NumberField.AdelicFourier.exists_nonneg_mem_schwartzBruhat2_forall_norm_apply_vecMul_le_of_isCompact
      F (reflectPair ψ μ₁ Φ) hΦ' {1} isCompact_singleton
  refine ⟨Ψ, hΨ, fun x => ⟨(hreal x).2, ?_⟩, hdom, ?_⟩
  · have h := congrArg Complex.im (hreal x).1
    simpa using h.symm
  · intro T _ τ col N hN s hs
    exact setLIntegral_enorm_le_of_norm_le τ (fun t => reflectPair ψ μ₁ Φ (col t))
      (fun t => (Ψ (col t)).re) (fun t => hdom (col t)) N hN s hs

end S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow
end P2MW
export P2MW.S_NumberField_AdelicFourier_exists_nonneg_mem_schwartzBruhat2_norm_reflectPair_le_and_setLIntegral_enorm_reflectPair_comp_le_lintegral_mul_ofReal_rpow (solution)
