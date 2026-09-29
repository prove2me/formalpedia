-- Prove2me | solution 1 for NumberField.AdeleRing.map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/33b095b5-30b1-5073-928a-e51cae5b29aa

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self
p2m_attr_erase "instance" "Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdeleRing_map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self.NumberField IsDedekindDomain"
open scoped ENNReal NNReal Matrix

noncomputable section

namespace NumberField
p2m_export "NumberField" "AdeleRing TateGlobal.ideleNorm AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul AdeleRing.secondCountableTopology TateGlobal.continuous_ideleNorm"
namespace MirabolicMeasure
p2m_open "NumberField"

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "Gp" => Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 K) K)

theorem secondCountable_A : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology K

theorem secondCountable_units : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := secondCountable_A K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem t1Space_A : T1Space (AdeleRing (𝓞 K) K) := T2Space.t1Space

theorem locallyCompactSpace_units : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := inferInstance

attribute [local instance] secondCountable_A secondCountable_units t1Space_A locallyCompactSpace_units

def dens (δ : (AdeleRing (𝓞 K) K)ˣ) : ℝ≥0∞ := ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹

theorem dens_eq (δ : (AdeleRing (𝓞 K) K)ˣ) :
    dens K δ = ((distribHaarChar (AdeleRing (𝓞 K) K) δ : ℝ≥0) : ℝ≥0∞)⁻¹ := by
  have hpos : (distribHaarChar (AdeleRing (𝓞 K) K) δ : ℝ≥0) ≠ 0 := (distribHaarChar_pos).ne'
  unfold dens NumberField.TateGlobal.ideleNorm
  rw [← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inv hpos]

theorem dens_ne_top (δ : (AdeleRing (𝓞 K) K)ˣ) : dens K δ ≠ ⊤ := ENNReal.ofReal_ne_top

theorem dens_ne_zero (δ : (AdeleRing (𝓞 K) K)ˣ) : dens K δ ≠ 0 := by
  rw [dens_eq]; exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top

theorem dens_mul (d δ : (AdeleRing (𝓞 K) K)ˣ) :
    dens K (d * δ) = ((distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0) : ℝ≥0∞)⁻¹ * dens K δ := by
  rw [dens_eq, dens_eq, map_mul, ENNReal.coe_mul,
    ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]

theorem measurable_dens : Measurable (dens K) := by
  unfold dens
  exact ENNReal.measurable_ofReal.comp
    (NumberField.TateGlobal.continuous_ideleNorm K).measurable.inv

theorem map_mul_left_withDensity (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (d : (AdeleRing (𝓞 K) K)ˣ) :
    Measure.map (fun δ => d * δ) (ν.withDensity (dens K)) =
      ((distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0) : ℝ≥0∞) • ν.withDensity (dens K) := by
  set D : ℝ≥0∞ := ((distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0) : ℝ≥0∞) with hD
  have hDtop : D ≠ ⊤ := ENNReal.coe_ne_top
  have hD0 : D ≠ 0 := ENNReal.coe_ne_zero.mpr (distribHaarChar_pos).ne'
  ext s hs
  rw [Measure.map_apply (measurable_const_mul d) hs, withDensity_apply _ (measurable_const_mul d hs),
    Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]
  rw [← lintegral_indicator (measurable_const_mul d hs), ← lintegral_indicator hs]
  have h1 : (fun δ => ((fun δ' => d * δ') ⁻¹' s).indicator (dens K) δ) =
      fun δ => D * s.indicator (dens K) (d * δ) := by
    funext δ
    by_cases hδ : d * δ ∈ s
    · rw [Set.indicator_of_mem (show δ ∈ (fun δ' => d * δ') ⁻¹' s from hδ), Set.indicator_of_mem hδ,
        dens_mul, ← mul_assoc, ENNReal.mul_inv_cancel hD0 hDtop, one_mul]
    · rw [Set.indicator_of_notMem (show δ ∉ (fun δ' => d * δ') ⁻¹' s from hδ), Set.indicator_of_notMem hδ,
        mul_zero]
  rw [h1, lintegral_const_mul' D _ hDtop, lintegral_mul_left_eq_self (fun δ => s.indicator (dens K) δ) d]

def transposeGL (h : GL (Fin 2) (AdeleRing (𝓞 K) K)) : GL (Fin 2) (AdeleRing (𝓞 K) K) where
  val := ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)ᵀ
  inv := (((h⁻¹ : Gp) : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem det_transposeGL (h : Gp) :
    Matrix.GeneralLinearGroup.det (transposeGL K h) = Matrix.GeneralLinearGroup.det h := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

theorem map_mulVec_pi (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure] (h : Gp) :
    Measure.map (fun c : Fin 2 → 𝔸 => ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec c) (Measure.pi fun _ : Fin 2 => μ) =
      ((distribHaarChar (AdeleRing (𝓞 K) K) (Matrix.GeneralLinearGroup.det h) : ℝ≥0) : ℝ≥0∞)⁻¹ •
        (Measure.pi fun _ : Fin 2 => μ) := by
  have hfun : (fun c : Fin 2 → 𝔸 => ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec c) =
      fun c => Matrix.vecMul c ((transposeGL K h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸) := by
    funext c
    show ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec c = Matrix.vecMul c ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸)ᵀ
    rw [Matrix.vecMul_transpose]
  rw [hfun]
  have := (NumberField.AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
    K (transposeGL K h)).1 (Measure.pi fun _ : Fin 2 => μ)
  rw [this, det_transposeGL]
  rw [← ENNReal.coe_inv (distribHaarChar_pos).ne']
  rfl

theorem main (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) (h : Gp) :
    Measure.map (fun p : (Fin 2 → 𝔸) × (AdeleRing (𝓞 K) K)ˣ =>
        (((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec p.1, Matrix.GeneralLinearGroup.det h * p.2))
      ((Measure.pi fun _ : Fin 2 => μ).prod (ν.withDensity (dens K))) =
    (Measure.pi fun _ : Fin 2 => μ).prod (ν.withDensity (dens K)) := by
  haveI := hμ
  haveI := hν
  set d := Matrix.GeneralLinearGroup.det h with hd
  set D : ℝ≥0∞ := ((distribHaarChar (AdeleRing (𝓞 K) K) d : ℝ≥0) : ℝ≥0∞) with hD
  have hDtop : D ≠ ⊤ := ENNReal.coe_ne_top
  have hD0 : D ≠ 0 := ENNReal.coe_ne_zero.mpr (distribHaarChar_pos).ne'
  have hA : Measurable fun c : Fin 2 → 𝔸 => ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec c := by
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _
  have hB : Measurable fun δ : (AdeleRing (𝓞 K) K)ˣ => d * δ := measurable_const_mul d
  have hmap : (fun p : (Fin 2 → 𝔸) × (AdeleRing (𝓞 K) K)ˣ =>
      (((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec p.1, Matrix.GeneralLinearGroup.det h * p.2)) =
      Prod.map (fun c : Fin 2 → 𝔸 => ((h : Gp) : Matrix (Fin 2) (Fin 2) 𝔸).mulVec c)
        (fun δ : (AdeleRing (𝓞 K) K)ˣ => d * δ) := by
    funext p; rfl
  rw [hmap, ← Measure.map_prod_map _ _ hA hB, map_mulVec_pi K μ h, map_mul_left_withDensity K ν d,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ← hd, ENNReal.inv_mul_cancel hD0 hDtop, one_smul]

end NumberField.MirabolicMeasure

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure)
    (h : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    Measure.map (fun p : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ =>
        ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).mulVec p.1, Matrix.GeneralLinearGroup.det h * p.2))
      ((Measure.pi fun _ : Fin 2 => μ).prod
        (ν.withDensity fun δ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹)) =
    (Measure.pi fun _ : Fin 2 => μ).prod
      (ν.withDensity fun δ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K δ)⁻¹) :=
  NumberField.MirabolicMeasure.main K μ hμ ν hν h

end

end S_NumberField_AdeleRing_map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self
end P2MW
export P2MW.S_NumberField_AdeleRing_map_mulVec_det_mul_pi_prod_withDensity_ideleNorm_inv_eq_self (solution)
