-- Prove2me | solution 1 for NumberField.IdeleLocalInv.eq_of_hasLocalInv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bf5bfd05-2bb7-5eaa-b521-a070647cf06f

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant
import Theorems.Thm_M4aHerbrand_exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq
import Theorems.Thm_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_eq_of_hasLocalInv
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

set_option linter.unusedSectionVars false

set_option maxHeartbeats 6400000 in

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (v : HeightOneSpectrum (𝓞 E)) (t₁ t₂ : AddCircle (1 : ℚ))
    (h₁ : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t₁) (h₂ : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t₂) :
    t₁ = t₂ := by
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  obtain ⟨prG₁, hprG₁, w₁, hw₁, q₁, hq₁, hqw₁, L₁, fd₁, act₁, faith₁, actU₁, Φ₁, h11, h12, h13, K₁, fdK₁, base₁, θ₁, hθ₁, u₁, hu₁, n₁, hx₁, ht₁⟩ := h₁
  obtain ⟨prG₂, hprG₂, w₂, hw₂, q₂, hq₂, hqw₂, L₂, fd₂, act₂, faith₂, actU₂, Φ₂, h21, h22, h23, K₂, fdK₂, base₂, θ₂, hθ₂, u₂, hu₂, n₂, hx₂, ht₂⟩ := h₂

  have hpr : prG₂ w₂ = prG₁ w₂ := by
    refine Rep.hom_ext ?_
    ext z
    obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
    show (prG₂ w₂).hom (Additive.ofMul y) = (prG₁ w₂).hom (Additive.ofMul y)
    rw [hprG₂, hprG₁]
  rw [hpr] at hx₂

  have hw : w₂.under (𝓞 E) = w₁.under (𝓞 E) := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.under_def]
    exact hw₂.trans hw₁.symm
  obtain ⟨hcard, act', actU', Φ', θ', u', h1', h2', h3', base', hθ', hu', hx'⟩ :=
    M4aHerbrand.exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq E K D hactI prG₁ hprG₁ x w₁ w₂ hw
      q₁ L₁ Φ₁ h11 h12 h13 K₁ base₁ θ₁ hθ₁ u₁ hu₁ n₁ hx₁

  haveI : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w₂)) (w₂.adicCompletion K) := NumberField.PlaceDecomp.faithfulSMul_decomp E K w₂
  have faith' : @FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w₂)) L₁ act'.toSMul :=
    @FaithfulSMul.mk _ _ act'.toSMul fun {g₁ g₂} h =>
      FaithfulSMul.eq_of_smul_eq_smul (α := w₂.adicCompletion K) fun y => Φ'.injective (by rw [h3' g₁ y, h3' g₂ y]; exact h _)
  obtain ⟨-, hqw₁'⟩ :=
    NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv K w₂ q₁ L₁ Φ'
  have hU : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w₂)) θ' 2).hom u' =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w₂)) θ₂ 2).hom u₂ :=
    @NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E K _ _ _ _ _ _ w₂
      q₁ _ hqw₁' L₁ _ act' faith' actU' Φ' h1' h2' h3' K₁ _ base' θ' hθ' u' hu'
      q₂ _ hqw₂ L₂ _ act₂ faith₂ actU₂ Φ₂ h21 h22 h23 K₂ _ base₂ θ₂ hθ₂ u₂ hu₂
  rw [hU] at hx'

  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w₂) :=
    ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic q₂ L₂ (↥(NumberField.PlaceDecomp.decomp E K w₂)) h21
  have hEq : n₁ • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w₂)) θ₂ 2).hom u₂ =
      n₂ • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w₂)) θ₂ 2).hom u₂ := hx'.symm.trans hx₂
  have hsub : (n₁ - n₂) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w₂)) θ₂ 2).hom u₂ = 0 := by
    simp [sub_zsmul, hEq]
  have hdvd : (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w₂) : ℤ) ∣ (n₁ - n₂) :=
    (NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass E K w₂ hsolv q₂ L₂ Φ₂ h21 h22 h23
      K₂ base₂ θ₂ hθ₂ u₂ hu₂ (n₁ - n₂)).mp hsub

  obtain ⟨k, hk⟩ := hdvd
  rw [ht₁, ht₂, ← hcard]
  have hN : (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w₂) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  refine ⟨k, ?_⟩
  have hk' : (n₁ : ℚ) - n₂ = (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w₂) : ℚ) * (k : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hk
    push_cast at this
    linarith
  rw [zsmul_eq_mul, mul_one, div_sub_div_same, hk', eq_div_iff hN, mul_comm]

end S_NumberField_IdeleLocalInv_eq_of_hasLocalInv
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_eq_of_hasLocalInv (solution)
