-- Prove2me | solution 1 for NumberField.TateGlobal.exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/847474c2-66dd-5738-87a0-7a642c88edbf

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion.NumberField.TateGlobal AutomorphicForm Set Complex Filter"

noncomputable section

namespace NumberField
p2m_export "NumberField" "AdeleRing TateGlobal.ideleNorm TateGlobal.normPowChar TateGlobal.setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos ideleNorm_mul mem_normOneIdeles_iff normPowChar coe_normPowChar_apply setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div exists_eq_normPowChar_of_forall_mem_normOneIdeles"
namespace PolarPart
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem ideleNorm_inv (t : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F t⁻¹ = (ideleNorm F t)⁻¹ := by
  unfold ideleNorm
  rw [map_inv, NNReal.coe_inv]

theorem ofReal_ideleNorm_ne_zero (t : (AdeleRing (𝓞 F) F)ˣ) : ((ideleNorm F t : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (ideleNorm_pos t).ne'

theorem norm_cpow_add (t : (AdeleRing (𝓞 F) F)ˣ) (w₁ w₂ : ℂ) :
    ((ideleNorm F t : ℝ) : ℂ) ^ (w₁ + w₂) = ((ideleNorm F t : ℝ) : ℂ) ^ w₁ * ((ideleNorm F t : ℝ) : ℂ) ^ w₂ :=
  cpow_add _ _ (ofReal_ideleNorm_ne_zero t)

theorem norm_inv_cpow (t : (AdeleRing (𝓞 F) F)ˣ) (w : ℂ) :
    ((ideleNorm F t⁻¹ : ℝ) : ℂ) ^ w = ((ideleNorm F t : ℝ) : ℂ) ^ (-w) := by
  rw [ideleNorm_inv, ofReal_inv, inv_cpow _ _ (by
    rw [arg_ofReal_of_nonneg (ideleNorm_pos t).le]; exact Real.pi_ne_zero.symm), cpow_neg]

theorem ideleNorm_principal (u : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  unfold ideleNorm
  have h' : distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) = 1 := h
  rw [h']
  rfl

variable {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}

theorem coe_inv_apply (t : (AdeleRing (𝓞 F) F)ˣ) : ((χ⁻¹ t : ℂˣ) : ℂ) = ((χ t : ℂˣ) : ℂ)⁻¹ := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

theorem coe_inv_apply' (t : (AdeleRing (𝓞 F) F)ˣ) : ((χ t : ℂˣ) : ℂ)⁻¹ = ((χ t⁻¹ : ℂˣ) : ℂ) := by
  rw [map_inv, Units.val_inv_eq_inv_val]

theorem isIdeleClassChar_inv (hχ : IsIdeleClassChar (𝓞 F) F χ) : IsIdeleClassChar (𝓞 F) F χ⁻¹ :=
  fun u => by rw [MonoidHom.inv_apply, hχ u, inv_one]

theorem isUnitaryChar_inv (hχu : IsUnitaryChar (𝓞 F) F χ) : IsUnitaryChar (𝓞 F) F χ⁻¹ :=
  fun x => by rw [coe_inv_apply, norm_inv, hχu x, inv_one]

theorem continuous_coe_inv (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) :
    Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ⁻¹ x : ℂˣ) : ℂ) := by
  simp_rw [coe_inv_apply, coe_inv_apply']
  exact hχc.comp continuous_inv

theorem continuous_units_of_continuous_coe (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) :
    Continuous χ := by
  refine Units.continuous_iff.mpr ⟨hχc, ?_⟩
  have h : (fun x : (AdeleRing (𝓞 F) F)ˣ => (((χ x)⁻¹ : ℂˣ) : ℂ)) = fun x => ((χ x⁻¹ : ℂˣ) : ℂ) := by
    funext x; rw [map_inv]
  rw [h]
  exact hχc.comp continuous_inv

theorem exists_normOne_ne_one (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    (hne : ∀ τ : ℝ, χ ≠ normPowChar F τ) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z = 1 ∧ χ z ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨τ, hτ⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles F χ
    (continuous_units_of_continuous_coe hχc) hχu (fun x hx => h x ((mem_normOneIdeles_iff x).mp hx))
  exact hne τ hτ

theorem normPowChar_mul_cpow (τ : ℝ) (w : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((normPowChar F τ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ w =
      ((ideleNorm F x : ℝ) : ℂ) ^ (w + (τ : ℂ) * I) := by
  rw [coe_normPowChar_apply, ← cpow_add _ _ (ofReal_ideleNorm_ne_zero x)]
  congr 1; ring

theorem normPowChar_inv_mul_cpow (τ : ℝ) (w : ℂ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    (((normPowChar F τ)⁻¹ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ w =
      ((ideleNorm F x : ℝ) : ℂ) ^ (w - (τ : ℂ) * I) := by
  rw [coe_inv_apply, coe_normPowChar_apply, ← cpow_neg, ← cpow_add _ _ (ofReal_ideleNorm_ne_zero x)]
  congr 1; ring

theorem re_add_mul_I (w : ℂ) (τ : ℝ) : (w + (τ : ℂ) * I).re = w.re := by
  simp [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]

theorem re_sub_mul_I (w : ℂ) (τ : ℝ) : (w - (τ : ℂ) * I).re = w.re := by
  simp [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]

section DualData

variable {θ θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ} {a b : ℂ} {d : ℝ}

theorem inversion_dual
    (hrel : ∀ t : (AdeleRing (𝓞 F) F)ˣ, θ t + a = ((ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b))
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    θ' t + b = ((ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ t⁻¹ + a) := by
  have h := hrel t⁻¹
  rw [inv_inv, norm_inv_cpow, neg_neg] at h
  rw [h, ← mul_assoc, ← norm_cpow_add, neg_add_cancel, cpow_zero, one_mul]

theorem invariant_of_inversion
    (hθ' : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t)
    (hrel : ∀ t : (AdeleRing (𝓞 F) F)ˣ, θ t + a = ((ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b))
    (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    θ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ t := by
  have h1 := hrel (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t)
  have h2 := hrel t
  have hinv : (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t)⁻¹ =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u⁻¹ * t⁻¹ := by
    rw [mul_inv_rev, map_inv, mul_comm]
  rw [ideleNorm_mul, ideleNorm_principal, one_mul, hinv, hθ'] at h1
  exact add_right_cancel (h1.trans h2.symm)

end DualData

end NumberField.TateGlobal.PolarPart

end

open NumberField.TateGlobal.PolarPart in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Set (AdeleRing (𝓞 F) F)ˣ),
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
      ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ →
        AutomorphicForm.IsUnitaryChar (𝓞 F) F χ →
        Continuous (fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) →
      ∀ (θ θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ),
        (∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
          θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t) →
      ∀ (a b : ℂ) (d : ℝ), 0 < d →
        (∀ t : (AdeleRing (𝓞 F) F)ˣ,
          θ t + a = ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b)) →
        (∀ σ : ℝ, IntegrableOn
          (fun t => θ t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
          (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) →
        (∀ σ : ℝ, IntegrableOn
          (fun t => θ' t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
          (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) →
        ∃ R R' : ℂ → ℂ,
          (∀ s : ℂ, R s =
            ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
              + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν) ∧
          (∀ s : ℂ, R' s =
            ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
              + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
                θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν) ∧
          (∀ s : ℂ, R s = R' ((d : ℂ) - s)) ∧
          ((∀ τ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar F τ) →
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν = R s) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν = R' s)) ∧
          (∀ τ : ℝ, χ = NumberField.TateGlobal.normPowChar F τ →
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R s + C * b / (s - d + (τ : ℂ) * Complex.I) - C * a / (s + (τ : ℂ) * Complex.I)) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R' s + C * a / (s - d - (τ : ℂ) * Complex.I) - C * b / (s - (τ : ℂ) * Complex.I))) ∧
          (∃ c₁ c₀ p₁ p₀ : ℂ,
            ((∀ τ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar F τ) → c₁ = 0 ∧ c₀ = 0) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R s + (c₁ / (s - p₁) + c₀ / (s - p₀))) ∧
            (∀ s : ℂ, d < s.re →
              ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
                R' s - (c₁ / (s - ((d : ℂ) - p₁)) + c₀ / (s - ((d : ℂ) - p₀))))) := by
  obtain ⟨C, hC, hK4⟩ :=
    NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div F ν
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ χ hχ hχu hχc θ θ' hθ' a b d hd hrel hdec hdec'

  set U : ℂ → ℂ := fun s => ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
      θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν with hU
  set U' : ℂ → ℂ := fun s => ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
      θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν with hU'
  set P : ℂ → ℂ := fun w => ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
      ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ w ∂ν with hP
  set P' : ℂ → ℂ := fun w => ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
      ((χ⁻¹ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ w ∂ν with hP'

  have hK7 := NumberField.TateGlobal.setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion F ν Ω hΩ
    χ hχ hχu hχc θ θ' hθ' a b d hd hrel hdec hdec'
  have hθ : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ t :=
    invariant_of_inversion hθ' hrel
  have hK7' := NumberField.TateGlobal.setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion F ν Ω hΩ
    χ⁻¹ (isIdeleClassChar_inv hχ) (isUnitaryChar_inv hχu) (continuous_coe_inv hχc) θ' θ hθ b a d hd
    (inversion_dual hrel) hdec' hdec
  have hZ : ∀ s : ℂ, d < s.re →
      ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
        U s + U' ((d : ℂ) - s) + b * P (s - d) - a * P s :=
    fun s hs => ((hK7.2 s hs).2.2.2)
  have hZ' : ∀ s : ℂ, d < s.re →
      ∫ t in Ω, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
        U' s + U ((d : ℂ) - s) + a * P' (s - d) - b * P' s := by
    intro s hs
    have h := (hK7'.2 s hs).2.2.2
    simp only [coe_inv_apply, inv_inv] at h
    simp only [hU', hU, hP', coe_inv_apply]
    exact h

  have hPole := (hK4 Ω hΩ).2.2 χ hχ hχu hχc
  have hPole' := (hK4 Ω hΩ).2.2 χ⁻¹ (isIdeleClassChar_inv hχ) (isUnitaryChar_inv hχu) (continuous_coe_inv hχc)
  have hPow := (hK4 Ω hΩ).2.1
  refine ⟨fun s => U s + U' ((d : ℂ) - s), fun s => U' s + U ((d : ℂ) - s), fun s => rfl, fun s => rfl,
    fun s => by simp only [sub_sub_cancel]; ring, ?_, ?_, ?_⟩
  ·
    intro hne
    obtain ⟨z, hz1, hzχ⟩ := exists_normOne_ne_one hχu hχc hne
    have hzχ' : χ⁻¹ z ≠ 1 := fun h => hzχ (inv_eq_one.mp ((MonoidHom.inv_apply χ z).symm.trans h))
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have hs0 : 0 < s.re := hd.trans hs
      have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
      rw [hZ s hs, show P (s - d) = 0 from ((hPole (s - d) hsd).2.2.1 ⟨z, hz1, hzχ⟩).1,
        show P s = 0 from ((hPole s hs0).2.2.1 ⟨z, hz1, hzχ⟩).1]
      ring
    · have hs0 : 0 < s.re := hd.trans hs
      have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
      rw [hZ' s hs, show P' (s - d) = 0 from ((hPole' (s - d) hsd).2.2.1 ⟨z, hz1, hzχ'⟩).1,
        show P' s = 0 from ((hPole' s hs0).2.2.1 ⟨z, hz1, hzχ'⟩).1]
      ring
  ·
    intro τ hτ
    have hPτ : ∀ w : ℂ, 0 < w.re → P w = C / (w + (τ : ℂ) * I) := by
      intro w hw
      simp only [hP, hτ, normPowChar_mul_cpow]
      exact (hPow (w + (τ : ℂ) * I) (by rw [re_add_mul_I]; exact hw)).2.1
    have hP'τ : ∀ w : ℂ, 0 < w.re → P' w = C / (w - (τ : ℂ) * I) := by
      intro w hw
      simp only [hP', hτ, normPowChar_inv_mul_cpow]
      exact (hPow (w - (τ : ℂ) * I) (by rw [re_sub_mul_I]; exact hw)).2.1
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have hs0 : 0 < s.re := hd.trans hs
      have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
      rw [hZ s hs, hPτ (s - d) hsd, hPτ s hs0]
      ring
    · have hs0 : 0 < s.re := hd.trans hs
      have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
      rw [hZ' s hs, hP'τ (s - d) hsd, hP'τ s hs0]
      ring
  ·
    by_cases hex : ∃ τ : ℝ, χ = NumberField.TateGlobal.normPowChar F τ
    · obtain ⟨τ, hτ⟩ := hex
      have hPτ : ∀ w : ℂ, 0 < w.re → P w = C / (w + (τ : ℂ) * I) := by
        intro w hw
        simp only [hP, hτ, normPowChar_mul_cpow]
        exact (hPow (w + (τ : ℂ) * I) (by rw [re_add_mul_I]; exact hw)).2.1
      have hP'τ : ∀ w : ℂ, 0 < w.re → P' w = C / (w - (τ : ℂ) * I) := by
        intro w hw
        simp only [hP', hτ, normPowChar_inv_mul_cpow]
        exact (hPow (w - (τ : ℂ) * I) (by rw [re_sub_mul_I]; exact hw)).2.1
      refine ⟨C * b, -(C * a), (d : ℂ) - (τ : ℂ) * I, -((τ : ℂ) * I), fun hne => absurd hτ (hne τ),
        fun s hs => ?_, fun s hs => ?_⟩
      · have hs0 : 0 < s.re := hd.trans hs
        have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
        rw [hZ s hs, hPτ (s - d) hsd, hPτ s hs0]
        have e1 : s - ((d : ℂ) - (τ : ℂ) * I) = s - d + (τ : ℂ) * I := by ring
        have e2 : s - -((τ : ℂ) * I) = s + (τ : ℂ) * I := by ring
        rw [e1, e2]
        ring
      · have hs0 : 0 < s.re := hd.trans hs
        have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
        rw [hZ' s hs, hP'τ (s - d) hsd, hP'τ s hs0]
        have e1 : s - ((d : ℂ) - ((d : ℂ) - (τ : ℂ) * I)) = s - (τ : ℂ) * I := by ring
        have e2 : s - ((d : ℂ) - -((τ : ℂ) * I)) = s - d - (τ : ℂ) * I := by ring
        rw [e1, e2]
        ring
    · push Not at hex
      obtain ⟨z, hz1, hzχ⟩ := exists_normOne_ne_one hχu hχc hex
      have hzχ' : χ⁻¹ z ≠ 1 := fun h => hzχ (inv_eq_one.mp ((MonoidHom.inv_apply χ z).symm.trans h))
      refine ⟨0, 0, 0, 0, fun _ => ⟨rfl, rfl⟩, fun s hs => ?_, fun s hs => ?_⟩
      · have hs0 : 0 < s.re := hd.trans hs
        have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
        rw [hZ s hs, show P (s - d) = 0 from ((hPole (s - d) hsd).2.2.1 ⟨z, hz1, hzχ⟩).1,
          show P s = 0 from ((hPole s hs0).2.2.1 ⟨z, hz1, hzχ⟩).1]
        ring
      · have hs0 : 0 < s.re := hd.trans hs
        have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
        rw [hZ' s hs, show P' (s - d) = 0 from ((hPole' (s - d) hsd).2.2.1 ⟨z, hz1, hzχ'⟩).1,
          show P' s = 0 from ((hPole' s hs0).2.2.1 ⟨z, hz1, hzχ'⟩).1]
        ring

end S_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_setIntegral_eq_entirePart_add_polarPart_and_fe_of_thetaInversion (solution)
