-- Prove2me | solution 1 for M4aHerbrand.exists_surjective_and_invariant_map_eq_finsum_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b6afd358-ad18-5f4f-bbba-1792eacddfe2

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_M4aHerbrand_exists_map_eq_groupCohomology_ideleClassGroup_of_isCyclic
import Theorems.Thm_M4aHerbrand_exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic
import Theorems.Thm_NumberField_PlaceDecomp_iSup_decomp_eq_top_of_isCyclic
import Theorems.Thm_M4aHerbrand_exists_localSum_forall_eq_finsum_groupCohomology_ideles
import Theorems.Thm_M4aHerbrand_card_nsmul_eq_zero_and_map_eq_zero_and_exists_eq_one_div_of_forall_localSum_eq_finsum
import Theorems.Thm_M4aHerbrand_exists_addOrderOf_carry_eq_card_and_span_eq_top_ideleClassGroup_of_isCyclic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_surjective_and_invariant_map_eq_finsum_of_isCyclic
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_surjective_and_invariant_map_eq_finsum_of_isCyclic.M4aHerbrand groupCohomology"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant principalIdeles IdeleClassGroup IdeleGaloisDescent exists_map_eq_groupCohomology_ideleClassGroup_of_isCyclic exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic exists_localSum_forall_eq_finsum_groupCohomology_ideles card_nsmul_eq_zero_and_map_eq_zero_and_exists_eq_one_div_of_forall_localSum_eq_finsum exists_addOrderOf_carry_eq_card_and_span_eq_top_ideleClassGroup_of_isCyclic"
namespace C6
p2m_open "M4aHerbrand"

theorem exists_pow_index_generates {G : Type*} [Group G] [Finite G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (D : Subgroup G) :
    ∃ (k : ℕ) (hkD : s ^ k ∈ D), (∀ g : D, g ∈ Subgroup.zpowers (⟨s ^ k, hkD⟩ : D)) ∧ k * Nat.card D = Nat.card G := by
  classical

  have hcomm : ∀ g h : G, g * h = h * g := by
    intro g h
    obtain ⟨i, rfl⟩ := hs g
    obtain ⟨j, rfl⟩ := hs h
    exact (Commute.zpow_zpow (Commute.refl s) i j).eq
  haveI : D.Normal := ⟨fun a ha g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
  haveI : D.FiniteIndex := Subgroup.finiteIndex_of_finite
  refine ⟨D.index, Subgroup.pow_index_mem D s, ?_, ?_⟩
  ·
    have hn : orderOf s = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hs
    have hidx : D.index ∣ orderOf s := by rw [hn]; exact Subgroup.index_dvd_card D
    have hidx0 : D.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have hord : orderOf (s ^ D.index) = Nat.card D := by
      rw [orderOf_pow_of_dvd hidx0 hidx, hn]
      have := Subgroup.card_mul_index D
      rw [← this, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hidx0)]
    have hle : Subgroup.zpowers (s ^ D.index) ≤ D := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.pow_index_mem D s
    have heq : Subgroup.zpowers (s ^ D.index) = D := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, hord]
    intro g
    have hg : (g : G) ∈ Subgroup.zpowers (s ^ D.index) := by rw [heq]; exact g.2
    obtain ⟨z, hz⟩ := hg
    refine ⟨z, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_zpow]
    exact hz
  · rw [mul_comm]
    exact Subgroup.card_mul_index D

end M4aHerbrand.C6
open M4aHerbrand.C6 in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1) :

    (∀ (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
      (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)),
      ∀ c : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
        ∃ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2),
          (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x = c) ∧
    ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ)),

      Function.Injective invG ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧

      (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
            n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by
  classical

  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  letI instF : MulDistribMulAction (F ≃ₐ[E] F) Fˣ :=
    { smul := fun g a => Units.map ((g : F ≃ₐ[E] F) : F →* F) a
      one_smul := fun a => Units.ext rfl
      mul_smul := fun g₁ g₂ a => Units.ext rfl
      smul_one := fun g => Units.ext (map_one (g : F ≃ₐ[E] F))
      smul_mul := fun g a b => Units.ext (map_mul (g : F ≃ₐ[E] F) (a : F) (b : F)) }
  have hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F) := fun g a => rfl
  obtain ⟨j, hj⟩ : ∃ j : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ),
      ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) := by
    refine ⟨M4aHerbrand.repHomOfMulEquivariant (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* (AdeleRing (𝓞 F) F))) (fun g a => ?_), fun a => rfl⟩
    apply Units.ext
    rw [hactI]
    show algebraMap F (AdeleRing (𝓞 F) F) ((g • a : Fˣ) : F) = D.act g (algebraMap F (AdeleRing (𝓞 F) F) (a : F))
    rw [hactF, D.compat]
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)),
      ∀ x : (AdeleRing (𝓞 F) F)ˣ, π₀.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F) := by
    refine ⟨M4aHerbrand.repHomOfMulEquivariant (QuotientGroup.mk' (principalIdeles (𝓞 F) F)) (fun g x => ?_), fun x => rfl⟩
    rw [hact, hactI]
    rfl

  have hπuniq : ∀ (π : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))),
      (∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) → π = π₀ := by
    intro π hπ
    refine Rep.hom_ext ?_
    ext z
    exact (hπ (Additive.toMul z)).trans (hπ₀ (Additive.toMul z)).symm

  have hS : ∀ c : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2), ∃ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2), (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π₀ 2).hom x = c :=
    fun c => M4aHerbrand.exists_map_eq_groupCohomology_ideleClassGroup_of_isCyclic E F D hactI hact π₀ hπ₀ c
  obtain ⟨Λ, hΛ⟩ := M4aHerbrand.exists_localSum_forall_eq_finsum_groupCohomology_ideles E F D hactI
  obtain ⟨hGtor, hvan, hreal⟩ :=
    M4aHerbrand.card_nsmul_eq_zero_and_map_eq_zero_and_exists_eq_one_div_of_forall_localSum_eq_finsum
      E F D hactI hact hinf hactF j hj Λ hΛ
  have hker : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2), (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π₀ 2).hom x = 0 → Λ x = 0 := by
    intro x hx
    obtain ⟨α, rfl⟩ := M4aHerbrand.exists_map_eq_of_map_eq_zero_groupCohomology_ideles_of_isCyclic E F D hactI hact hactF j hj π₀ hπ₀ x hx
    exact hvan α

  choose lift hlift using hS
  have hwd : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2), Λ (lift ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π₀ 2).hom x)) = Λ x := by
    intro x
    rw [← sub_eq_zero, ← map_sub]
    apply hker
    rw [map_sub, hlift, sub_self]
  let invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ) :=
    { toFun := fun c => Λ (lift c)
      map_zero' := by
        have h := hwd 0
        rw [map_zero] at h
        rw [h, map_zero]
      map_add' := fun c₁ c₂ => by
        have h := hwd (lift c₁ + lift c₂)
        rw [map_add, hlift, hlift] at h
        rw [h, map_add] }
  have hinvπ : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2), invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π₀ 2).hom x) = Λ x := hwd

  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := (F ≃ₐ[E] F))
  haveI : Fact ((0 : ℚ) < 1) := ⟨one_pos⟩
  haveI : Fintype (F ≃ₐ[E] F) := Fintype.ofFinite _
  have hordχ : orderOf (Multiplicative.ofAdd ((((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ∣ orderOf s := by
    rw [orderOf_ofAdd_eq_addOrderOf, AddCircle.addOrderOf_period_div Nat.card_pos,
      orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card]
  let χ : (F ≃ₐ[E] F) →* Multiplicative (AddCircle (1 : ℚ)) := monoidHomOfForallMemZpowers hs hordχ
  have hχs : χ s = Multiplicative.ofAdd ((((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ))) :=
    monoidHomOfForallMemZpowers_apply_gen hs hordχ

  let S' : Subgroup (Multiplicative (AddCircle (1 : ℚ))) := AddSubgroup.toSubgroup invG.range
  have hDw : ∀ w : HeightOneSpectrum (𝓞 F), NumberField.PlaceDecomp.decomp E F w ≤ S'.comap χ := by
    intro w
    obtain ⟨k, hkD, hkgen, hkcard⟩ := exists_pow_index_generates s hs (NumberField.PlaceDecomp.decomp E F w)
    obtain ⟨xw, hxw⟩ := hreal w
    have hk0 : (k : ℚ) ≠ 0 := by
      have : k ≠ 0 := by rintro rfl; rw [zero_mul] at hkcard; exact (Nat.card_pos (α := (F ≃ₐ[E] F))).ne' hkcard.symm
      exact_mod_cast this
    have hval : χ (s ^ k) = Multiplicative.ofAdd (invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π₀ 2).hom xw)) := by
      rw [hinvπ, hxw, map_pow, hχs, ← ofAdd_nsmul, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div]
      congr 2
      rw [← hkcard, Nat.cast_mul, div_mul_cancel_left₀ hk0, one_div]
    intro g hg
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hkgen ⟨g, hg⟩)
    have hgz : g = (s ^ k) ^ z := by
      have := congrArg Subtype.val hz
      simpa using this.symm
    rw [Subgroup.mem_comap, hgz, map_zpow, hval]
    exact S'.zpow_mem (show Multiplicative.ofAdd (invG _) ∈ S' from ⟨_, rfl⟩) z
  have h1N : ((((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ))) ∈ invG.range := by
    have htop : (⊤ : Subgroup (F ≃ₐ[E] F)) ≤ S'.comap χ := by
      rw [← NumberField.PlaceDecomp.iSup_decomp_eq_top_of_isCyclic E F]
      exact iSup_le hDw
    have hsmem := htop (Subgroup.mem_top s)
    rw [Subgroup.mem_comap, hχs] at hsmem
    exact hsmem

  have hfinG : IsOfFinOrder s := isOfFinOrder_of_finite s
  obtain ⟨a₀, hz₀, -, hord₀, hspan₀⟩ :=
    M4aHerbrand.exists_addOrderOf_carry_eq_card_and_span_eq_top_ideleClassGroup_of_isCyclic E F D hact s hs hfinG
  have hcardC : Nat.card ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) = Nat.card (F ≃ₐ[E] F) := by
    set u₀ := (H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).hom ⟨carryFun s hs hfinG a₀, hz₀⟩ with hu₀
    have htop : (AddSubgroup.zmultiples u₀ : AddSubgroup ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ Submodule.span ℤ {u₀} := by rw [hspan₀]; trivial
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hy
      exact ⟨k, (int_smul_eq_zsmul _ k u₀).symm.trans hk⟩
    simp only [Fintype.card_eq_nat_card] at hord₀
    rw [← AddSubgroup.card_top (G := ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)), ← htop, Nat.card_zmultiples, hord₀]
  haveI : Finite ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) := Nat.finite_of_card_ne_zero (by rw [hcardC]; exact (Nat.card_pos (α := (F ≃ₐ[E] F))).ne')
  have hrange : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0 := by
    intro t
    constructor
    · rintro ⟨c, rfl⟩
      show Nat.card (F ≃ₐ[E] F) • Λ (lift c) = 0
      exact hGtor _
    · intro ht

      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective t
      change Nat.card (F ≃ₐ[E] F) • ((a : ℚ) : AddCircle (1 : ℚ)) = 0 at ht
      rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at ht
      obtain ⟨m, hm⟩ := ht
      have hN : (Nat.card (F ≃ₐ[E] F) : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := (F ≃ₐ[E] F))).ne'
      have ha : (a : ℚ) = m • ((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ)) := by
        rw [zsmul_eq_mul, nsmul_eq_mul] at *
        field_simp
        linarith [hm]
      change ((a : ℚ) : AddCircle (1 : ℚ)) ∈ invG.range
      rw [ha, AddCircle.coe_zsmul]
      exact invG.range.zsmul_mem h1N m
  have hinj : Function.Injective invG := by

    haveI : Finite invG.range := Finite.of_surjective _ (AddMonoidHom.rangeRestrict_surjective invG)
    have hsub : AddSubgroup.zmultiples ((((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ))) ≤ invG.range := (AddSubgroup.zmultiples_le).mpr h1N
    have hzcard : Nat.card (AddSubgroup.zmultiples ((((1 : ℚ) / (Nat.card (F ≃ₐ[E] F) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) = Nat.card (F ≃ₐ[E] F) := by
      rw [Nat.card_zmultiples, AddCircle.addOrderOf_period_div Nat.card_pos]
    have hle1 : Nat.card (F ≃ₐ[E] F) ≤ Nat.card invG.range := by
      rw [← hzcard]
      exact Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective hsub)
    have hle2 : Nat.card invG.range ≤ Nat.card ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) :=
      Nat.card_le_card_of_surjective _ (AddMonoidHom.rangeRestrict_surjective invG)
    have hcr : Nat.card ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) = Nat.card invG.range := le_antisymm (hcardC ▸ hle1) hle2
    obtain ⟨e⟩ := Finite.card_eq.mp hcr
    have hbij : Function.Injective (AddMonoidHom.rangeRestrict invG) :=
      (Finite.injective_iff_surjective_of_equiv e).mpr (AddMonoidHom.rangeRestrict_surjective invG)
    intro a b hab
    exact hbij (Subtype.ext hab)
  refine ⟨fun π hπ c => ?_, invG, ?_, ?_, ?_⟩
  ·
    rw [hπuniq π hπ]
    exact ⟨lift c, hlift c⟩
  ·
    exact hinj
  ·
    exact hrange
  ·
    intro prG hprG π hπ x q hq L' hL'fd instSMA instMDA Φ hΦ₁ hΦ₂ hΦ₃ K₀ hK₀fd hbase θ hθ u' hu' n hn
    rw [hπuniq π hπ, hinvπ]
    exact hΛ prG hprG x q hq L' hL'fd instSMA instMDA Φ hΦ₁ hΦ₂ hΦ₃ K₀ hK₀fd hbase θ hθ u' hu' n hn

end S_M4aHerbrand_exists_surjective_and_invariant_map_eq_finsum_of_isCyclic
end P2MW
export P2MW.S_M4aHerbrand_exists_surjective_and_invariant_map_eq_finsum_of_isCyclic (solution)
