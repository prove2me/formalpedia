-- Prove2me | solution 1 for NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6a5bca15-bfa0-5e79-b1c8-4663729ca06e

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule

import Theorems.Thm_M4aHerbrand_exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero
import Theorems.Thm_NumberField_LevelArith_exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d
import Theorems.Thm_NumberField_LevelArith_exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport
import Theorems.Thm_groupCohomology_inhomogeneousCochains_d_comp_apply
import Theorems.Thm_groupCohomology_inhomogeneousCochains_d_d_apply
import Theorems.Thm_groupCohomology_map_pi_cocyclesMk_apply
import Theorems.Thm_groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq
import Theorems.Thm_groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero
import Theorems.Thm_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd
import Theorems.Thm_NumberField_LevelArith_isPGroup_levelGal_of_isPGroup_quotient
import Theorems.Thm_NumberField_SIdele_exists_hom_ideles_apply_eq
import Theorems.Thm_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d
import Theorems.Thm_groupCohomology_map_id_pi_cocyclesMk_apply
import Theorems.Thm_NumberField_LevelArith_eq_one_of_mem_infPlaceDecomp_of_isPGroup
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply
import Theorems.Thm_NumberField_PlaceDecomp_exists_forall_isLocalFundamentalClass_above
import Theorems.Thm_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Theorems.Thm_NumberField_LevelArith_isGalois_levelField
import Theorems.Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing NumberField.LevelArith.instCommGroupUnitsModPow instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

set_option maxHeartbeats 51200000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : (Fin 3 → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hf : ((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 3 4).hom f = 0)
    (f₁ : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hff₁ : ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (f₁ (fun i => levelGal L F hLF (g i))) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
          = ((sUnitsMaxRep.val S L ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (c : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hc : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom c = fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ g))

    (n : ℕ) (ζ : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hζ : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom ζ = 0)
    (ω : (Fin 1 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (e : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hT : (n : ℤ) • c = (n : ℤ) • ζ + ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 1 2).hom ω + fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (e g))

    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L)) (hv₀ : v₀ ∈ placesOverPrimesFinset ↥L S)
    (hD : n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v₀))) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F') (_ : F ≤ F')
      (b : (Fin 2 → (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin 3 → ↥L.fixingSubgroup,
        ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = ((((inhomogeneousCochains ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))).d 2 3).hom b (fun i => (g i : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by
  classical

  obtain ⟨D⟩ := M4aHerbrand.nonempty_ideleGaloisDescent ↥L ↥(levelField L F hLF)
  letI instI : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ := MulDistribMulAction.compHom _ D.unitsAct
  have hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x := fun _ _ => rfl
  obtain ⟨instC, hact⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct ↥L ↥(levelField L F hLF) D
  letI := instC

  obtain ⟨Φ, ιC, hΦinj, hΦrange, hΦρ, hΦdiag, hιC, hιCinj, hιCrange⟩ :=
    NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) D hact
  obtain ⟨ΦR, hΦR⟩ := NumberField.SIdele.exists_hom_ideles_apply_eq ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) D hactI Φ hΦρ
  obtain ⟨πR, hπR⟩ := M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply ↥L ↥(levelField L F hLF) D hactI hact
  obtain ⟨prG, hprG⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply ↥L ↥(levelField L F hLF) D hactI
  obtain ⟨q, hq, L', hL'fd, hmsa, hmda, Φv, h1, h2, h3, K₀, hK₀fd, hK₀, θ, hθ, u', hu'⟩ :=
    NumberField.PlaceDecomp.exists_forall_isLocalFundamentalClass_above ↥L ↥(levelField L F hLF)

  have hinf := NumberField.LevelArith.eq_one_of_mem_infPlaceDecomp_of_isPGroup (p := p) L h4 F hLF hG
  have hGK : IsPGroup p (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := NumberField.LevelArith.isPGroup_levelGal_of_isPGroup_quotient p L F hLF hG
  obtain ⟨invG, inv, hinjG, hinj, hrangeG, hrange, hR, hTG, hTsub⟩ :=
    M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup ↥L ↥(levelField L F hLF) D hactI hact hinf p hGK

  have hprinc : ∀ x : (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), πR.hom (ΦR.hom ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom x)) = 0 := fun x => by
    have h1 : (QuotientGroup.mk (Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x)) : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩
    calc πR.hom (ΦR.hom ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom x)) = πR.hom (Φ ((NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom x)) := by rw [hΦR]
      _ = πR.hom (Additive.ofMul (Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x))) := congrArg _ (hΦdiag x)
      _ = Additive.ofMul (QuotientGroup.mk (Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) x)) : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) := hπR _
      _ = Additive.ofMul (1 : (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) := by rw [h1]
      _ = 0 := rfl
  have hu : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom (c - ζ) = fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (f₁ g) := by
    rw [map_sub, hc, hζ, sub_zero]
  have hχ : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))).d 2 3).hom (fun g => πR.hom (ΦR.hom ((c - ζ) g))) = 0 := by
    rw [groupCohomology.inhomogeneousCochains_d_comp_apply πR 2 (fun g => ΦR.hom ((c - ζ) g)),
      groupCohomology.inhomogeneousCochains_d_comp_apply ΦR 2 (c - ζ), hu]
    funext g
    exact hprinc (f₁ g)

  have hnu : ((n : ℤ) • (c - ζ) : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))) = ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 1 2).hom ω + fun g => (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (e g) := by
    rw [smul_sub, hT]; abel
  have hnχ : ((n : ℤ) • fun g => πR.hom (ΦR.hom ((c - ζ) g))) =
      ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))).d 1 2).hom (fun g => πR.hom (ΦR.hom (ω g))) := by
    rw [groupCohomology.inhomogeneousCochains_d_comp_apply πR 1 (fun g => ΦR.hom (ω g)),
      groupCohomology.inhomogeneousCochains_d_comp_apply ΦR 1 ω]
    funext g
    have := congrFun hnu g
    simp only [Pi.smul_apply, Pi.add_apply] at this ⊢
    rw [← map_zsmul, ← map_zsmul, this, map_add, map_add, hprinc, add_zero]

  have hx₁n : (n : ℤ) • groupCohomology.π (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) 2 (groupCohomology.cocyclesMk _ hχ) = 0 :=
    groupCohomology.zsmul_pi_cocyclesMk_eq_zero_of_eq_d (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) 1 (n : ℤ) _ hχ _ hnχ
  have ht : n • invG (groupCohomology.π (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) 2 (groupCohomology.cocyclesMk _ hχ)) = 0 := by
    rw [← map_nsmul, ← natCast_zsmul, hx₁n, map_zero]
  have hN : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v₀)) := Nat.card_pos
  obtain ⟨a, ha⟩ := AddCircle.exists_eq_coe_div_of_nsmul_eq_zero_of_dvd _ n _ hN hD ht

  haveI := hq v₀; haveI := hL'fd v₀; letI := hmsa v₀; letI := hmda v₀; haveI := hK₀fd v₀
  have hT : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)), w.asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) = v₀.asIdeal →
      w ∈ {w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)) | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)} := fun w hw => by
    have : w.under (𝓞 ↥L) = v₀ := HeightOneSpectrum.ext hw
    show w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)
    rw [this]; exact hv₀
  obtain ⟨ξ, hξ, hξS, hread, hoff⟩ :=
    M4aHerbrand.exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero ↥L ↥(levelField L F hLF) D hactI prG hprG
      v₀ (q v₀) (L' v₀) (Φv v₀) (h1 v₀) (h2 v₀) (h3 v₀) (K₀ v₀) (hK₀ v₀) (θ v₀) (hθ v₀) (u' v₀) (hu' v₀) _ hT a

  have hπξ : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))).d 2 3).hom (fun g => πR.hom (ξ g)) = 0 := by
    rw [groupCohomology.inhomogeneousCochains_d_comp_apply πR 2 ξ, hξ]
    funext g; exact map_zero _
  let nf : HeightOneSpectrum (𝓞 ↥L) → ℤ := fun v => if v = v₀ then a else 0
  have hreadall : ∀ v : HeightOneSpectrum (𝓞 ↥L),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) 2).hom
          (groupCohomology.π (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) 2 (groupCohomology.cocyclesMk ξ hξ)) =
        nf v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v))) (θ v) 2).hom (u' v) := by
    intro v
    by_cases hv : v = v₀
    · subst hv
      rw [show nf v = a from if_pos rfl]
      exact hread
    · rw [show nf v = 0 from if_neg hv, zero_smul]
      have hw : (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v).asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) ≠ v₀.asIdeal := by
        rw [NumberField.PlaceAbove.comap_above]
        exact fun h => hv (HeightOneSpectrum.ext h)
      have hzero : (fun g : Fin 2 → ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) => (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).hom (ξ ((NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype ∘ g))) = 0 := by
        funext g
        calc (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).hom (ξ ((NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype ∘ g))
            = Additive.ofMul (finPart (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v) (Additive.toMul (ξ ((NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype ∘ g)))) := hprG _ _
          _ = Additive.ofMul 1 := by rw [hoff _ _ hw]
          _ = 0 := rfl
      have hd0 : (inhomogeneousCochains.d _ 2).hom
          (fun g : Fin 2 → ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) => (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).hom (ξ ((NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype ∘ g))) = 0 := by
        rw [hzero, map_zero]
      rw [groupCohomology.map_pi_cocyclesMk_apply (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) 2 ξ hξ hd0]
      exact groupCohomology.pi_cocyclesMk_eq_zero_of_eq_zero _ 2 _ hd0 hzero
  have hinvξ := hTG prG hprG πR hπR (groupCohomology.π (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) 2 (groupCohomology.cocyclesMk ξ hξ))
    q hq L' hL'fd hmsa hmda Φv h1 h2 h3 K₀ hK₀fd hK₀ θ hθ u' hu' nf hreadall
  have hsum : (∑ᶠ v : HeightOneSpectrum (𝓞 ↥L),
      ((((nf v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) =
      ((((a : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v₀)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
    rw [finsum_eq_single _ v₀ (fun v hv => by simp only [nf, if_neg hv, Int.cast_zero, zero_div, QuotientAddGroup.mk_zero])]
    simp only [nf, if_pos rfl]
  have heq : (groupCohomology.map (MonoidHom.id (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) πR 2).hom
        (groupCohomology.π (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) 2 (groupCohomology.cocyclesMk ξ hξ)) =
      groupCohomology.π (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) 2 (groupCohomology.cocyclesMk _ hχ) :=
    hinjG (by rw [hinvξ, hsum, ← ha])
  rw [groupCohomology.map_id_pi_cocyclesMk_apply πR 2 ξ hξ hπξ] at heq
  obtain ⟨ν, hν⟩ := groupCohomology.exists_eq_add_d_of_pi_cocyclesMk_eq (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) 1 _ _ hχ hπξ heq.symm
  have hkill : ∀ g : Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)), πR.hom (Φ ((c - ζ) g)) = πR.hom (ξ g) + ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))).d 1 2).hom ν g :=
    fun g => by rw [← hΦR]; exact congrFun hν g

  obtain ⟨F₂, hfd₂, hF₂, hgal₂, hFF₂, H₂⟩ :=
    NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d S hpS L F hLF hF hG
      D hactI hact πR hπR Φ hΦinj hΦrange hΦρ hΦdiag f₁ (c - ζ) hu ξ hξ hξS ν hkill
  haveI : FiniteDimensional ℚ ↥F₂ := hfd₂
  haveI := hgal₂
  obtain ⟨e₂, he₂⟩ := H₂

  haveI := NumberField.LevelArith.isGalois_levelField L F₂ (hLF.trans hFF₂)
  obtain ⟨ι₂, hι₂, φ₂, hφ₂, hφval₂⟩ :=
    NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective S L F₂ (hLF.trans hFF₂) hF₂
  have hfe₂ := fun g : Fin 3 → ↥L.fixingSubgroup =>
    (he₂ (fun i => levelGal L F₂ (hLF.trans hFF₂) (g i)) g
      (fun i x => NumberField.LevelArith.levelGal_apply_coe L F₂ (hLF.trans hFF₂) (g i) x)).trans (hff₁ g)
  obtain ⟨b, hb⟩ :=
    NumberField.LevelArith.exists_two_cochain_quotientToInvariants_sUnitsMaxRep_eq_d_of_transport
      S L F F₂ (hLF.trans hFF₂) ι₂ hι₂ φ₂ hφ₂ hφval₂ f e₂ hfe₂
  exact ⟨F₂, hF₂, hgal₂, hFF₂, b, hb⟩

end S_NumberField_LevelArith_exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp
end P2MW
export P2MW.S_NumberField_LevelArith_exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp (solution)
