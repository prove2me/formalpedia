-- Prove2me | solution 1 for NumberField.TateGlobal.setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c92acfd2-b821-5630-b9be-d93892261b6a

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
import Theorems.Thm_NumberField_TateGlobal_exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField.TateGlobal AutomorphicForm Set Complex Filter"
open scoped Pointwise

noncomputable section

namespace NumberField
p2m_export "NumberField" "AdeleRing TateGlobal.ideleNorm TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log TateGlobal.continuous_ideleNorm AdeleRing.distribHaarChar_algebraMap AdeleRing.secondCountableTopology"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos ideleNorm_mul exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log continuous_ideleNorm"
namespace ThetaSplit
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem ideleNorm_inv (t : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F t⁻¹ = (ideleNorm F t)⁻¹ := by
  unfold ideleNorm
  rw [map_inv, NNReal.coe_inv]

theorem ideleNorm_ne_zero (t : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F t ≠ 0 := (ideleNorm_pos t).ne'

theorem ofReal_ideleNorm_ne_zero (t : (AdeleRing (𝓞 F) F)ˣ) : ((ideleNorm F t : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (ideleNorm_ne_zero t)

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

theorem norm_cpow_add (t : (AdeleRing (𝓞 F) F)ˣ) (w₁ w₂ : ℂ) :
    ((ideleNorm F t : ℝ) : ℂ) ^ (w₁ + w₂) = ((ideleNorm F t : ℝ) : ℂ) ^ w₁ * ((ideleNorm F t : ℝ) : ℂ) ^ w₂ :=
  cpow_add _ _ (ofReal_ideleNorm_ne_zero t)

theorem norm_inv_cpow (t : (AdeleRing (𝓞 F) F)ˣ) (w : ℂ) :
    ((ideleNorm F t⁻¹ : ℝ) : ℂ) ^ w = ((ideleNorm F t : ℝ) : ℂ) ^ (-w) := by
  rw [ideleNorm_inv, ofReal_inv, inv_cpow _ _ (by
    rw [arg_ofReal_of_nonneg (ideleNorm_pos t).le]; exact Real.pi_ne_zero.symm), cpow_neg]

theorem norm_norm_cpow (t : (AdeleRing (𝓞 F) F)ˣ) (w : ℂ) :
    ‖((ideleNorm F t : ℝ) : ℂ) ^ w‖ = (ideleNorm F t) ^ w.re :=
  norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos t) w

theorem norm_norm_cpow_of_re_eq_zero (t : (AdeleRing (𝓞 F) F)ˣ) {w : ℂ} (hw : w.re = 0) :
    ‖((ideleNorm F t : ℝ) : ℂ) ^ w‖ = 1 := by
  rw [norm_norm_cpow, hw, Real.rpow_zero]

theorem continuous_norm_cpow (w : ℂ) :
    Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F t : ℝ) : ℂ) ^ w :=
  (continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)).cpow continuous_const
    fun t => ofReal_mem_slitPlane.mpr (ideleNorm_pos t)

variable (F) in

def principalUnits : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

scoped instance countable_principalUnits : Countable (principalUnits F) := by
  haveI : Countable F :=
    (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable Fˣ :=
    Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)

theorem smul_def (γ : principalUnits F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    γ • t = (γ : (AdeleRing (𝓞 F) F)ˣ) * t := rfl

theorem ideleNorm_coe_principalUnits (γ : principalUnits F) :
    ideleNorm F (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  obtain ⟨u, hu⟩ := γ.2
  rw [← hu]
  exact ideleNorm_principal u

theorem ideleNorm_smul (γ : principalUnits F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F (γ • t) = ideleNorm F t := by
  rw [smul_def, ideleNorm_mul, ideleNorm_coe_principalUnits, one_mul]

theorem char_coe_principalUnits {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 F) F χ)
    (γ : principalUnits F) : χ (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  obtain ⟨u, hu⟩ := γ.2
  rw [← hu]
  exact hχ u

theorem char_smul {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 F) F χ)
    (γ : principalUnits F) (t : (AdeleRing (𝓞 F) F)ˣ) : χ (γ • t) = χ t := by
  rw [smul_def, map_mul, char_coe_principalUnits hχ, one_mul]

scoped instance smulCommClass_principalUnits :
    SMulCommClass (AdeleRing (𝓞 F) F)ˣ (principalUnits F) (AdeleRing (𝓞 F) F)ˣ :=
  ⟨fun a γ x => by
    show a * ((γ : (AdeleRing (𝓞 F) F)ˣ) * x) = (γ : (AdeleRing (𝓞 F) F)ˣ) * (a * x)
    rw [← mul_assoc, mul_comm a, mul_assoc]⟩

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

theorem measurable_ideleNorm : Measurable (ideleNorm F) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).measurable

theorem measurableSet_le_one : MeasurableSet {t : (AdeleRing (𝓞 F) F)ˣ | ideleNorm F t ≤ 1} :=
  measurableSet_le measurable_ideleNorm measurable_const

theorem measurableSet_one_le : MeasurableSet {t : (AdeleRing (𝓞 F) F)ˣ | 1 ≤ ideleNorm F t} :=
  measurableSet_le measurable_const measurable_ideleNorm

scoped instance smulInvariantMeasure_principalUnits (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] :
    SMulInvariantMeasure (principalUnits F) (AdeleRing (𝓞 F) F)ˣ ν :=
  ⟨fun γ A _hA => by
    show ν ((fun x => (γ : (AdeleRing (𝓞 F) F)ˣ) * x) ⁻¹' A) = ν A
    exact measure_preimage_mul _ _ _⟩

theorem isInvInvariant (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] : ν.IsInvInvariant := by
  haveI i2 : LocallyCompactSpace (AdeleRing (𝓞 F) F)ˣ := inferInstance
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI i1 : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := inferInstance
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  haveI : ν.Regular := inferInstance
  infer_instance

section Domain

variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 F) F)ˣ}

theorem measurePreserving_inv' : MeasurePreserving (fun t : (AdeleRing (𝓞 F) F)ˣ => t⁻¹) ν ν := by
  haveI := isInvInvariant ν
  exact Measure.measurePreserving_inv ν

theorem measurableEmbedding_inv :
    MeasurableEmbedding (fun t : (AdeleRing (𝓞 F) F)ˣ => t⁻¹) :=
  (MeasurableEquiv.inv (AdeleRing (𝓞 F) F)ˣ).measurableEmbedding

theorem isFundamentalDomain_inv (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) :
    IsFundamentalDomain (principalUnits F) ((fun t : (AdeleRing (𝓞 F) F)ˣ => t⁻¹) ⁻¹' Ω) ν := by
  refine hΩ.preimage_of_equiv (measurePreserving_inv' ν).quasiMeasurePreserving
    (e := fun γ : principalUnits F => γ⁻¹) inv_involutive.bijective fun γ t => ?_
  show ((γ⁻¹ : principalUnits F) • t)⁻¹ = γ • t⁻¹
  rw [smul_def, smul_def, mul_inv_rev, Subgroup.coe_inv, inv_inv, mul_comm]

end Domain

section Upper

variable {ν : Measure (AdeleRing (𝓞 F) F)ˣ} {S : Set (AdeleRing (𝓞 F) F)ˣ}

theorem integrableOn_mul_of_norm_le_one {f φ : (AdeleRing (𝓞 F) F)ˣ → ℂ} (hf : IntegrableOn f S ν)
    (hφ : Continuous φ) (hφ1 : ∀ t, ‖φ t‖ ≤ 1) : IntegrableOn (fun t => φ t * f t) S ν :=
  Integrable.bdd_mul hf hφ.aestronglyMeasurable (Eventually.of_forall hφ1)

variable {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem coe_inv_apply (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((χ t : ℂˣ) : ℂ)⁻¹ = ((χ t⁻¹ : ℂˣ) : ℂ) := by
  rw [map_inv, Units.val_inv_eq_inv_val]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem continuous_coe_inv (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) :
    Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)⁻¹ := by
  simp_rw [coe_inv_apply]
  exact hχc.comp continuous_inv

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem norm_coe_inv (hχu : IsUnitaryChar (𝓞 F) F χ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    ‖((χ t : ℂˣ) : ℂ)⁻¹‖ = 1 := by
  rw [norm_inv, hχu t, inv_one]

theorem integrableOn_mul_char_mul_cpow (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    {θ : (AdeleRing (𝓞 F) F)ˣ → ℂ} (s : ℂ)
    (h : IntegrableOn (fun t => θ t * ((ideleNorm F t : ℝ) : ℂ) ^ (s.re : ℂ)) S ν) :
    IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s) S ν := by
  have hφ : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - (s.re : ℂ)) :=
    hχc.mul (continuous_norm_cpow _)
  have hφ1 : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      ‖((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - (s.re : ℂ))‖ ≤ 1 := by
    intro t
    rw [norm_mul, hχu t, one_mul, norm_norm_cpow_of_re_eq_zero t (by simp)]
  refine (integrableOn_mul_of_norm_le_one h hφ hφ1).congr_fun_ae (Eventually.of_forall fun t => ?_)

  have hsplit : ((ideleNorm F t : ℝ) : ℂ) ^ s =
      ((ideleNorm F t : ℝ) : ℂ) ^ (s.re : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - (s.re : ℂ)) := by
    rw [← norm_cpow_add]; congr 1; ring
  simp only
  rw [hsplit]; ring

theorem integrableOn_mul_charInv_mul_cpow (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    {θ : (AdeleRing (𝓞 F) F)ˣ → ℂ} (s : ℂ)
    (h : IntegrableOn (fun t => θ t * ((ideleNorm F t : ℝ) : ℂ) ^ (s.re : ℂ)) S ν) :
    IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ s) S ν := by
  have hφ : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ (s - (s.re : ℂ)) :=
    (continuous_coe_inv hχc).mul (continuous_norm_cpow _)
  have hφ1 : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      ‖((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ (s - (s.re : ℂ))‖ ≤ 1 := by
    intro t
    rw [norm_mul, norm_coe_inv hχu t, one_mul, norm_norm_cpow_of_re_eq_zero t (by simp)]
  refine (integrableOn_mul_of_norm_le_one h hφ hφ1).congr_fun_ae (Eventually.of_forall fun t => ?_)
  have hsplit : ((ideleNorm F t : ℝ) : ℂ) ^ s =
      ((ideleNorm F t : ℝ) : ℂ) ^ (s.re : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - (s.re : ℂ)) := by
    rw [← norm_cpow_add]; congr 1; ring
  simp only
  rw [hsplit]; ring

end Upper

section Dual

variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
  {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ}

def dualUp (θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : ℂ) :
    (AdeleRing (𝓞 F) F)ˣ → ℂ :=
  {t | 1 ≤ ideleNorm F t}.indicator fun t => θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ w

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem dualUp_smul (hχ : IsIdeleClassChar (𝓞 F) F χ)
    (hθ' : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t)
    (w : ℂ) (γ : principalUnits F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    dualUp θ' χ w (γ • t) = dualUp θ' χ w t := by
  have hθ'γ : θ' (γ • t) = θ' t := by
    obtain ⟨u, hu⟩ := γ.2
    rw [smul_def, ← hu]
    exact hθ' u t
  unfold dualUp
  by_cases ht : 1 ≤ ideleNorm F t
  · have hγt : γ • t ∈ {t : (AdeleRing (𝓞 F) F)ˣ | 1 ≤ ideleNorm F t} := by
      show 1 ≤ ideleNorm F (γ • t); rwa [ideleNorm_smul]
    rw [indicator_of_mem hγt, indicator_of_mem (show t ∈ {t | 1 ≤ ideleNorm F t} from ht),
      hθ'γ, char_smul hχ, ideleNorm_smul]
  · have hγt : γ • t ∉ {t : (AdeleRing (𝓞 F) F)ˣ | 1 ≤ ideleNorm F t} := by
      show ¬ 1 ≤ ideleNorm F (γ • t); rwa [ideleNorm_smul]
    rw [indicator_of_notMem hγt, indicator_of_notMem (show t ∉ {t | 1 ≤ ideleNorm F t} from ht)]

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in

theorem dualUp_inv (w : ℂ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    dualUp θ' χ w t⁻¹ =
      {t | ideleNorm F t ≤ 1}.indicator
        (fun t => θ' t⁻¹ * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (-w)) t := by
  unfold dualUp
  have hiff : (1 ≤ ideleNorm F t⁻¹) ↔ ideleNorm F t ≤ 1 := by
    rw [ideleNorm_inv]; exact one_le_inv₀ (ideleNorm_pos t)
  by_cases ht : ideleNorm F t ≤ 1
  · rw [indicator_of_mem (show t⁻¹ ∈ {t | 1 ≤ ideleNorm F t} from hiff.mpr ht),
      indicator_of_mem (show t ∈ {t | ideleNorm F t ≤ 1} from ht), map_inv, Units.val_inv_eq_inv_val,
      inv_inv, norm_inv_cpow]
  · rw [indicator_of_notMem (show t⁻¹ ∉ {t | 1 ≤ ideleNorm F t} from fun h => ht (hiff.mp h)),
      indicator_of_notMem (show t ∉ {t | ideleNorm F t ≤ 1} from ht)]

theorem integrableOn_and_setIntegral_inv_eq
    (hΩ : IsFundamentalDomain (principalUnits F) Ω ν)
    (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    (hθ' : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t)
    (w : ℂ)
    (hdec' : IntegrableOn (fun t => θ' t * ((ideleNorm F t : ℝ) : ℂ) ^ (w.re : ℂ))
      (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν) :
    IntegrableOn (fun t => θ' t⁻¹ * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (-w))
        (Ω ∩ {t | ideleNorm F t ≤ 1}) ν ∧
    ∫ t in Ω ∩ {t | ideleNorm F t ≤ 1}, θ' t⁻¹ * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (-w) ∂ν =
      ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ w ∂ν := by
  set Ωi : Set (AdeleRing (𝓞 F) F)ˣ := (fun t : (AdeleRing (𝓞 F) F)ˣ => t⁻¹) ⁻¹' Ω with hΩi
  have hΩinv : IsFundamentalDomain (principalUnits F) Ωi ν := isFundamentalDomain_inv ν hΩ

  have hup : IntegrableOn (fun t => θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ w)
      (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν := integrableOn_mul_charInv_mul_cpow hχu hχc w hdec'
  have hgΩ : IntegrableOn (dualUp θ' χ w) Ω ν := by
    rw [dualUp, IntegrableOn, integrable_indicator_iff measurableSet_one_le, IntegrableOn,
      Measure.restrict_restrict measurableSet_one_le, inter_comm]
    exact hup
  have hinvt := dualUp_smul hχ hθ' w
  have hgΩi : IntegrableOn (dualUp θ' χ w) Ωi ν := (hΩinv.integrableOn_iff hΩ hinvt).mpr hgΩ
  have hint_eq : ∫ t in Ωi, dualUp θ' χ w t ∂ν = ∫ t in Ω, dualUp θ' χ w t ∂ν :=
    hΩinv.setIntegral_eq hΩ hinvt

  have hpre : (fun t : (AdeleRing (𝓞 F) F)ˣ => t⁻¹) ⁻¹' Ωi = Ω := by
    ext t; simp [hΩi]
  have hmp := measurePreserving_inv' ν (F := F)
  have hcompInt : IntegrableOn (fun t => dualUp θ' χ w t⁻¹) Ω ν := by
    have h := (hmp.integrableOn_comp_preimage (measurableEmbedding_inv (F := F))
      (f := dualUp θ' χ w) (s := Ωi)).mpr hgΩi
    rwa [hpre] at h
  have hcompEq : ∫ t in Ω, dualUp θ' χ w t⁻¹ ∂ν = ∫ t in Ωi, dualUp θ' χ w t ∂ν := by
    have h := hmp.setIntegral_preimage_emb (measurableEmbedding_inv (F := F)) (dualUp θ' χ w) Ωi
    rwa [hpre] at h

  simp_rw [dualUp_inv] at hcompInt hcompEq
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, integrable_indicator_iff measurableSet_le_one, IntegrableOn,
      Measure.restrict_restrict measurableSet_le_one, inter_comm] at hcompInt
    exact hcompInt
  · rw [← setIntegral_indicator measurableSet_le_one, hcompEq, hint_eq, dualUp,
      setIntegral_indicator measurableSet_one_le]

end Dual

section Small

variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 F) F)ˣ}
  {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {θ θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ} {a b : ℂ} {d : ℝ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in

theorem integrand_eq_of_inversion
    (hrel : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      θ t + a = ((ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b))
    (s : ℂ) (t : (AdeleRing (𝓞 F) F)ˣ) :
    θ t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s =
      θ' t⁻¹ * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (-((d : ℂ) - s))
        + b * (((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - d))
        - a * (((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s) := by
  have hθ : θ t = ((ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b) - a :=
    eq_sub_of_add_eq (hrel t)
  have h1 : ((ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * ((ideleNorm F t : ℝ) : ℂ) ^ s =
      ((ideleNorm F t : ℝ) : ℂ) ^ (s - d) := by
    rw [← norm_cpow_add]; congr 1; ring
  have h2 : ((ideleNorm F t : ℝ) : ℂ) ^ (-((d : ℂ) - s)) = ((ideleNorm F t : ℝ) : ℂ) ^ (s - d) := by
    congr 1; ring
  rw [hθ, h2]
  linear_combination (θ' t⁻¹ + b) * ((χ t : ℂˣ) : ℂ) * h1

theorem small_half
    (hΩ : IsFundamentalDomain (principalUnits F) Ω ν)
    (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    (hθ' : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t)
    (hd : 0 < d)
    (hrel : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      θ t + a = ((ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b))
    (hdec' : ∀ σ : ℝ, IntegrableOn (fun t => θ' t * ((ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν)
    {s : ℂ} (hs : d < s.re) :
    IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s)
        (Ω ∩ {t | ideleNorm F t ≤ 1}) ν ∧
    ∫ t in Ω ∩ {t | ideleNorm F t ≤ 1}, θ t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
      ∫ t in Ω ∩ {t | 1 ≤ ideleNorm F t}, θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν
      + b * ∫ t in Ω ∩ {t | ideleNorm F t ≤ 1}, ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - d) ∂ν
      - a * ∫ t in Ω ∩ {t | ideleNorm F t ≤ 1}, ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s ∂ν := by

  have hw : (((d : ℂ) - s).re : ℂ) = (((d - s.re : ℝ)) : ℂ) := by simp
  have hdual := integrableOn_and_setIntegral_inv_eq ν hΩ hχ hχu hχc hθ' ((d : ℂ) - s)
    (by rw [hw]; exact hdec' (d - s.re))

  obtain ⟨C, _hC, hK4⟩ :=
    NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div F ν
  have hK := (hK4 Ω hΩ).2.2 χ hχ hχu hχc
  have hs0 : 0 < s.re := hd.trans hs
  have hsd : 0 < (s - (d : ℂ)).re := by simp; linarith
  have hP1 : IntegrableOn (fun t => ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - d))
      (Ω ∩ {t | ideleNorm F t ≤ 1}) ν := (hK (s - d) hsd).1
  have hP0 : IntegrableOn (fun t => ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s)
      (Ω ∩ {t | ideleNorm F t ≤ 1}) ν := (hK s hs0).1
  have hfun : (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s) =
      fun t => θ' t⁻¹ * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (-((d : ℂ) - s))
        + b * (((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - d))
        - a * (((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s) :=
    funext (integrand_eq_of_inversion hrel s)
  rw [hfun]
  have hI2 : IntegrableOn (fun t => b * (((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - d)))
      (Ω ∩ {t | ideleNorm F t ≤ 1}) ν := hP1.const_mul b
  have hI3 : IntegrableOn (fun t => a * (((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ s))
      (Ω ∩ {t | ideleNorm F t ≤ 1}) ν := hP0.const_mul a
  have hI12 : IntegrableOn (fun t => θ' t⁻¹ * ((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (-((d : ℂ) - s))
        + b * (((χ t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (s - d)))
      (Ω ∩ {t | ideleNorm F t ≤ 1}) ν := hdual.1.add hI2
  refine ⟨hI12.sub hI3, ?_⟩
  rw [integral_sub hI12 hI3, integral_add hdual.1 hI2, integral_const_mul, integral_const_mul, hdual.2]

end Small

section Split

variable (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] {Ω : Set (AdeleRing (𝓞 F) F)ˣ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
theorem eq_union_halves (Ω : Set (AdeleRing (𝓞 F) F)ˣ) :
    Ω = (Ω ∩ {t | 1 ≤ ideleNorm F t}) ∪ (Ω ∩ {t | ideleNorm F t ≤ 1}) := by
  ext t
  simp only [mem_union, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro ht
    rcases le_total 1 (ideleNorm F t) with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩
  · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht

theorem measure_inter_norm_eq_one (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) :
    ν (Ω ∩ {t | 1 ≤ ideleNorm F t} ∩ (Ω ∩ {t | ideleNorm F t ≤ 1})) = 0 := by
  obtain ⟨C, _hC0, _hC, hband⟩ :=
    NumberField.TateGlobal.exists_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_mul_log F ν
  have h := hband Ω hΩ 1 1 one_pos le_rfl
  rw [div_one, Real.log_one, ENNReal.ofReal_zero, mul_zero] at h
  refine measure_mono_null (fun t ht => ?_) h
  exact ⟨ht.1.1, ⟨ht.1.2, ht.2.2⟩⟩

theorem aedisjoint_halves (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) :
    AEDisjoint ν (Ω ∩ {t | 1 ≤ ideleNorm F t}) (Ω ∩ {t | ideleNorm F t ≤ 1}) :=
  measure_inter_norm_eq_one ν hΩ

omit [ν.IsHaarMeasure] in
theorem nullMeasurableSet_lower (hΩ : IsFundamentalDomain (principalUnits F) Ω ν) :
    NullMeasurableSet (Ω ∩ {t | ideleNorm F t ≤ 1}) ν :=
  hΩ.nullMeasurableSet.inter measurableSet_le_one.nullMeasurableSet

end Split

end NumberField.TateGlobal.ThetaSplit
p2m_reactivate "P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField.TateGlobal.ThetaSplit"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion.NumberField.TateGlobal.ThetaSplit"

open NumberField.TateGlobal.ThetaSplit in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ)
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    (θ θ' : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hθ' : ∀ (u : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      θ' (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u * t) = θ' t)
    (a b : ℂ) (d : ℝ) (hd : 0 < d)
    (hrel : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      θ t + a = ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (-(d : ℂ)) * (θ' t⁻¹ + b))
    (hdec : ∀ σ : ℝ, IntegrableOn
      (fun t => θ t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν)
    (hdec' : ∀ σ : ℝ, IntegrableOn
      (fun t => θ' t * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (σ : ℂ))
      (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) :
    (∀ s : ℂ,
      IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s)
        (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν ∧
      IntegrableOn (fun t => θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s)
        (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν) ∧
    (∀ s : ℂ, d < s.re →
      IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s) Ω ν ∧
      IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s)
        (Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1}) ν ∧
      ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
          θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
        ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
            θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν
          + b * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (s - d) ∂ν
          - a * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν ∧
      ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
        ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
            θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
          + ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
              θ' t * ((χ t : ℂˣ) : ℂ)⁻¹ * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ ((d : ℂ) - s) ∂ν
          + b * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ (s - d) ∂ν
          - a * ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
              ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν) := by
  have hΩ' : IsFundamentalDomain (principalUnits F) Ω ν := hΩ
  refine ⟨fun s => ⟨integrableOn_mul_char_mul_cpow hχu hχc s (hdec s.re),
    integrableOn_mul_charInv_mul_cpow hχu hχc s (hdec' s.re)⟩, fun s hs => ?_⟩
  have hup : IntegrableOn (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s)
      (Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t}) ν :=
    integrableOn_mul_char_mul_cpow hχu hχc s (hdec s.re)
  have hsm := small_half ν hΩ' hχ hχu hχc hθ' hd hrel hdec' hs
  have hwhole : IntegrableOn
      (fun t => θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s) Ω ν := by
    rw [eq_union_halves Ω]
    exact hup.union hsm.1
  refine ⟨hwhole, hsm.1, hsm.2, ?_⟩
  have hsplit : ∫ t in Ω, θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν =
      ∫ t in Ω ∩ {t | 1 ≤ NumberField.TateGlobal.ideleNorm F t},
          θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν
        + ∫ t in Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ≤ 1},
          θ t * ((χ t : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm F t : ℝ) : ℂ) ^ s ∂ν := by
    rw [← setIntegral_union₀ (aedisjoint_halves ν hΩ') (nullMeasurableSet_lower ν hΩ') hup hsm.1,
      ← eq_union_halves Ω]
  rw [hsplit, hsm.2]
  ring

end S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion
end P2MW
export P2MW.S_NumberField_TateGlobal_setIntegral_eq_upperHalves_add_poleIntegrals_of_thetaInversion (solution)
