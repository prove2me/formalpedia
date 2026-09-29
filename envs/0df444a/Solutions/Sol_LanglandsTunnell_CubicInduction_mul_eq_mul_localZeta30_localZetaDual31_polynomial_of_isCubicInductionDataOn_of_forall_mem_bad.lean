-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/51628060-0044-5dd4-8f1a-4a2d7b4f7e1b

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_globalZeta30_eq_mul_localZeta30_and_globalZetaDual31_eq_mul_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace"
p2m_attr_erase "instance" "NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.gl2Weyl_val FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq TestFunctionAction.coe_convolution TestFunctionAction.check_apply TestFunctionAction.measureCoeff_empty SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply"
p2m_attr_erase "simp" "GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory

namespace Ws31
namespace SepCore

open Polynomial

theorem differentiable_natCast_cpow_neg (N : ℕ) (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℂ) ^ (-s))) := by
  have h : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
  exact h.const_cpow (Or.inl (by exact_mod_cast hN.ne'))

theorem differentiable_eval_cpow (D : Polynomial ℂ) (N : ℕ) (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => D.eval ((N : ℂ) ^ (-s))) :=
  (Polynomial.differentiable D).comp (differentiable_natCast_cpow_neg N hN)

theorem eq_zero_of_forall_eval_cpow_nat (D : Polynomial ℂ) (N : ℕ) (hN : 1 < N)
    (h : ∀ n : ℕ, D.eval ((N : ℂ) ^ (-(n : ℂ))) = 0) : D = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hN).ne'
  let f : ℕ → ℂ := fun n => ((N : ℂ) ^ n)⁻¹
  have hf : ∀ n : ℕ, (N : ℂ) ^ (-(n : ℂ)) = f n := fun n => by
    simp only [f, Complex.cpow_neg, Complex.cpow_natCast]
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, inv_inj] at hab
    have hN1 : 1 < ‖(N : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast hN
    have := congrArg norm hab
    simp only [norm_pow] at this
    exact (pow_right_strictMono₀ hN1).injective this
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_)
  show IsRoot D (f n)
  rw [IsRoot, ← hf]; exact h n

theorem eq_zero_of_mul_eq_zero_of_ne_zero (E g : ℂ → ℂ) (hE : Differentiable ℂ E) (hg : Differentiable ℂ g)
    (h : ∀ s, E s * g s = 0) (s₀ : ℂ) (hs₀ : E s₀ ≠ 0) : ∀ s, g s = 0 := by
  have hga : AnalyticOnNhd ℂ g Set.univ := (hg.differentiableOn).analyticOnNhd isOpen_univ
  have hev : g =ᶠ[nhds s₀] 0 := by
    have hne : ∀ᶠ s in nhds s₀, E s ≠ 0 := (hE.continuous.continuousAt).eventually_ne hs₀
    filter_upwards [hne] with s hs
    have := h s
    simpa [hs] using this
  have := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s₀) hev
  exact fun s => this (Set.mem_univ s)

theorem eq_zero_of_eqOn_halfplane_left (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σ : ℝ)
    (h : ∀ s : ℂ, s.re < σ → F s = 0) : ∀ s, F s = 0 := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := (hF.differentiableOn).analyticOnNhd isOpen_univ
  set s₀ : ℂ := ((σ - 1 : ℝ) : ℂ) with hs₀
  have hmem : s₀.re < σ := by simp [hs₀]
  have hev : F =ᶠ[nhds s₀] 0 := by
    have hopen : IsOpen {s : ℂ | s.re < σ} := isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact h s hs
  have := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s₀) hev
  exact fun s => this (Set.mem_univ s)

theorem eq_zero_of_eqOn_halfplane_right (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → F s = 0) : ∀ s, F s = 0 := by
  have hFa : AnalyticOnNhd ℂ F Set.univ := (hF.differentiableOn).analyticOnNhd isOpen_univ
  set s₀ : ℂ := ((σ + 1 : ℝ) : ℂ) with hs₀
  have hmem : σ < s₀.re := by simp [hs₀]
  have hev : F =ᶠ[nhds s₀] 0 := by
    have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact h s hs
  have := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ s₀) hev
  exact fun s => this (Set.mem_univ s)

theorem eventually_eval_natCast_cpow_neg_ne_zero (Q : Polynomial ℂ) (hQ : Q ≠ 0) (N : ℕ) (hN : 1 < N) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Q.eval ((N : ℂ) ^ (-s)) ≠ 0 := by
  classical
  have hN0 : 0 < N := lt_trans Nat.zero_lt_one hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  refine ⟨(∑ r ∈ Q.roots.toFinset, |Real.log ‖r‖|) / Real.log (N : ℝ), fun s hs h => ?_⟩
  have hmem : ((N : ℂ) ^ (-s)) ∈ Q.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]; exact h
  have hnorm : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hN0]; simp
  have hlog : Real.log ‖(N : ℂ) ^ (-s)‖ = -s.re * Real.log (N : ℝ) := by
    rw [hnorm, Real.log_rpow (by exact_mod_cast hN0)]
  have hle : |Real.log ‖(N : ℂ) ^ (-s)‖| ≤ ∑ r ∈ Q.roots.toFinset, |Real.log ‖r‖| :=
    Finset.single_le_sum (f := fun r : ℂ => |Real.log ‖r‖|) (fun _ _ => abs_nonneg _) hmem
  rw [hlog] at hle
  have hσ0 : 0 ≤ (∑ r ∈ Q.roots.toFinset, |Real.log ‖r‖|) / Real.log (N : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hlogN.le
  have hspos : 0 < s.re := lt_of_le_of_lt hσ0 hs
  have habs : |(-s.re) * Real.log (N : ℝ)| = s.re * Real.log (N : ℝ) := by
    rw [abs_of_nonpos (by nlinarith)]; ring
  rw [habs] at hle
  have := (div_lt_iff₀ hlogN).mp hs
  linarith

theorem core (N : ℕ) (hN : 1 < N)
    (E₁ E₂ : ℂ → ℂ) (hE₁ : Differentiable ℂ E₁) (hE₂ : Differentiable ℂ E₂)
    (σR σL : ℝ) (A At Z₁ Z₂ Zd₁ Zd₂ : ℂ → ℂ)
    (hA0 : ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ A s ≠ 0)
    (hR₁ : ∀ s : ℂ, σR < s.re → E₁ s = A s * Z₁ s) (hR₂ : ∀ s : ℂ, σR < s.re → E₂ s = A s * Z₂ s)
    (hL₁ : ∀ s : ℂ, s.re < σL → E₁ s = At s * Zd₁ s) (hL₂ : ∀ s : ℂ, s.re < σL → E₂ s = At s * Zd₂ s)
    (P Q Pd Qd P' Q' Pd' Qd' : Polynomial ℂ) (hQ : Q ≠ 0) (hQ' : Q' ≠ 0) (hQd : Qd ≠ 0) (hQd' : Qd' ≠ 0)
    (hP₁ : ∀ s : ℂ, σR < s.re → Q.eval ((N : ℂ) ^ (-s)) * Z₁ s = P.eval ((N : ℂ) ^ (-s)))
    (hP₂ : ∀ s : ℂ, σR < s.re → Q'.eval ((N : ℂ) ^ (-s)) * Z₂ s = P'.eval ((N : ℂ) ^ (-s)))
    (hPd₁ : ∀ s : ℂ, s.re < σL → Qd.eval ((N : ℂ) ^ (-s)) * Zd₁ s = Pd.eval ((N : ℂ) ^ (-s)))
    (hPd₂ : ∀ s : ℂ, s.re < σL → Qd'.eval ((N : ℂ) ^ (-s)) * Zd₂ s = Pd'.eval ((N : ℂ) ^ (-s))) :
    P * Pd' * Q' * Qd = P' * Pd * Q * Qd' ∧ (P ≠ 0 → Pd ≠ 0) := by
  have hN0 : 0 < N := lt_trans Nat.zero_lt_one hN

  set X : ℂ → ℂ := fun s => (N : ℂ) ^ (-s) with hX
  have hXd : Differentiable ℂ X := differentiable_natCast_cpow_neg N hN0
  have hev : ∀ D : Polynomial ℂ, Differentiable ℂ (fun s => D.eval (X s)) := fun D =>
    (Polynomial.differentiable D).comp hXd

  have rel1 : ∀ s, E₁ s * ((Qd * Pd').eval (X s)) = E₂ s * ((Qd' * Pd).eval (X s)) := by
    have hF : Differentiable ℂ (fun s => E₁ s * ((Qd * Pd').eval (X s)) - E₂ s * ((Qd' * Pd).eval (X s))) :=
      ((hE₁.mul (hev _)).sub (hE₂.mul (hev _)))
    have h0 := eq_zero_of_eqOn_halfplane_left _ hF σL (fun s hs => by
      simp only [Polynomial.eval_mul]
      rw [hL₁ s hs, hL₂ s hs]
      have h1 := hPd₁ s hs; have h2 := hPd₂ s hs
      simp only [hX] at h1 h2 ⊢
      linear_combination (At s * Pd'.eval ((N : ℂ) ^ (-s))) * h1 - (At s * Pd.eval ((N : ℂ) ^ (-s))) * h2)
    intro s; have := h0 s; exact sub_eq_zero.mp this
  have rel2 : ∀ s, E₁ s * ((Q * P').eval (X s)) = E₂ s * ((Q' * P).eval (X s)) := by
    have hF : Differentiable ℂ (fun s => E₁ s * ((Q * P').eval (X s)) - E₂ s * ((Q' * P).eval (X s))) :=
      ((hE₁.mul (hev _)).sub (hE₂.mul (hev _)))
    have h0 := eq_zero_of_eqOn_halfplane_right _ hF σR (fun s hs => by
      simp only [Polynomial.eval_mul]
      rw [hR₁ s hs, hR₂ s hs]
      have h1 := hP₁ s hs; have h2 := hP₂ s hs
      simp only [hX] at h1 h2 ⊢
      linear_combination (A s * P'.eval ((N : ℂ) ^ (-s))) * h1 - (A s * P.eval ((N : ℂ) ^ (-s))) * h2)
    intro s; have := h0 s; exact sub_eq_zero.mp this

  set D : Polynomial ℂ := P * Pd' * Q' * Qd - P' * Pd * Q * Qd' with hD
  have keyE₁ : ∀ s, E₁ s * D.eval (X s) = 0 := by
    intro s
    have a := rel1 s; have b := rel2 s
    simp only [hD, Polynomial.eval_mul, Polynomial.eval_sub] at a b ⊢
    linear_combination (P.eval (X s) * Q'.eval (X s)) * a - (Pd.eval (X s) * Qd'.eval (X s)) * b
  have keyE₂ : ∀ s, E₂ s * D.eval (X s) = 0 := by
    intro s
    have a := rel1 s; have b := rel2 s
    simp only [hD, Polynomial.eval_mul, Polynomial.eval_sub] at a b ⊢
    linear_combination (P'.eval (X s) * Q.eval (X s)) * a - (Pd'.eval (X s) * Qd.eval (X s)) * b

  have hDzero_of : (∃ s, E₁ s ≠ 0) ∨ (∃ s, E₂ s ≠ 0) → D = 0 := by
    rintro (⟨s₀, hs₀⟩ | ⟨s₀, hs₀⟩)
    · have hz := eq_zero_of_mul_eq_zero_of_ne_zero E₁ (fun s => D.eval (X s)) hE₁ (hev D) keyE₁ s₀ hs₀
      exact eq_zero_of_forall_eval_cpow_nat D N hN (fun n => hz n)
    · have hz := eq_zero_of_mul_eq_zero_of_ne_zero E₂ (fun s => D.eval (X s)) hE₂ (hev D) keyE₂ s₀ hs₀
      exact eq_zero_of_forall_eval_cpow_nat D N hN (fun n => hz n)

  have hPzero_of : (∀ s, E₁ s = 0) → P = 0 := by
    intro h0
    by_contra hP
    obtain ⟨σ₁, hσ₁⟩ := eventually_eval_natCast_cpow_neg_ne_zero (P * Q) (mul_ne_zero hP hQ) N hN
    obtain ⟨s, hs, hAs⟩ := hA0 (max σR σ₁)
    have hsR : σR < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have h1 := hP₁ s hsR
    have hPQ := hσ₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
    rw [Polynomial.eval_mul] at hPQ
    have hE := hR₁ s hsR
    rw [h0 s] at hE

    have hZ : Z₁ s = 0 := by
      rcases mul_eq_zero.mp hE.symm with h | h
      · exact absurd h hAs
      · exact h
    rw [hZ, mul_zero] at h1
    exact hPQ (by rw [← h1, zero_mul])
  have hP'zero_of : (∀ s, E₂ s = 0) → P' = 0 := by
    intro h0
    by_contra hP
    obtain ⟨σ₁, hσ₁⟩ := eventually_eval_natCast_cpow_neg_ne_zero (P' * Q') (mul_ne_zero hP hQ') N hN
    obtain ⟨s, hs, hAs⟩ := hA0 (max σR σ₁)
    have hsR : σR < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have h1 := hP₂ s hsR
    have hPQ := hσ₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
    rw [Polynomial.eval_mul] at hPQ
    have hE := hR₂ s hsR
    rw [h0 s] at hE
    have hZ : Z₂ s = 0 := by
      rcases mul_eq_zero.mp hE.symm with h | h
      · exact absurd h hAs
      · exact h
    rw [hZ, mul_zero] at h1
    exact hPQ (by rw [← h1, zero_mul])
  refine ⟨?_, ?_⟩
  ·
    by_cases h : (∃ s, E₁ s ≠ 0) ∨ (∃ s, E₂ s ≠ 0)
    · have := hDzero_of h
      rw [hD] at this
      exact sub_eq_zero.mp this
    · simp only [not_or, not_exists, not_not] at h
      rw [hPzero_of h.1, hP'zero_of h.2]; ring
  ·
    intro hP hPd

    obtain ⟨σ₁, hσ₁⟩ := eventually_eval_natCast_cpow_neg_ne_zero (P * Q * Qd) (mul_ne_zero (mul_ne_zero hP hQ) hQd) N hN
    obtain ⟨s, hs, hAs⟩ := hA0 (max σR σ₁)
    have hsR : σR < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hPQQd := hσ₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
    rw [Polynomial.eval_mul, Polynomial.eval_mul] at hPQQd

    have hE₁s : E₁ s ≠ 0 := by
      intro h0
      have h1 := hP₁ s hsR
      have hE := hR₁ s hsR
      rw [h0] at hE
      have hZ : Z₁ s = 0 := by
        rcases mul_eq_zero.mp hE.symm with h | h
        · exact absurd h hAs
        · exact h
      rw [hZ, mul_zero] at h1
      apply hPQQd
      rw [← h1]; ring

    have hF : Differentiable ℂ (fun s => E₁ s * Qd.eval (X s)) := hE₁.mul (hev Qd)
    have hzero := eq_zero_of_eqOn_halfplane_left _ hF σL (fun s' hs' => by
      have h1 := hPd₁ s' hs'
      rw [hPd, Polynomial.eval_zero] at h1
      rw [hL₁ s' hs']
      simp only [hX] at h1 ⊢
      linear_combination (At s') * h1)
    have := hzero s
    simp only [hX] at this
    rcases mul_eq_zero.mp this with h | h
    · exact hE₁s h
    · apply hPQQd; rw [h]; ring

end Ws31.SepCore

section
open Matrix

namespace Ws31
namespace SepShift

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem integrand_shift (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℂ)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) =
      ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c))
    (a : (v.adicCompletion ℚ)ˣ) (s w : ℂ) :
    w * ((χ a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
      w * ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - c - 1) := by
  have hm : (((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)) ≠ 0 := by
    have := LanglandsTunnell.TateLocal.modulus_pos (a := (a : v.adicCompletion ℚ)) a.ne_zero
    exact_mod_cast this.ne'
  rw [h a, mul_assoc, mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hm]
  congr 2; ring

variable {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}

theorem localZeta30_shift (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℂ)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) =
      ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c))
    (s : ℂ) (g : LocalGL3 v) :
    localZeta30 v μ W χ s g = localZeta30 v μ W χ' (s - c) g := by
  unfold localZeta30
  congr 1; funext a
  exact integrand_shift v χ χ' c h a s _

theorem localZeta31_shift (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℂ)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) =
      ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c))
    (s : ℂ) (g : LocalGL3 v) :
    localZeta31 v μ ν W χ s g = localZeta31 v μ ν W χ' (s - c) g := by
  unfold localZeta31
  congr 1; funext a
  exact integrand_shift v χ χ' c h a s _

theorem isLocalZeta30ConvergentAbove_shift (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℂ)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) =
      ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c))
    (g : LocalGL3 v) (σ₀ : ℝ) (hc : IsLocalZeta30ConvergentAbove v μ W χ g σ₀) :
    IsLocalZeta30ConvergentAbove v μ W χ' g (σ₀ - c.re) := by
  intro s hs
  have h1 := hc (s + c) (by simp only [Complex.add_re]; linarith)
  have heq : (fun a : (v.adicCompletion ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + c - 1)) =
      (fun a : (v.adicCompletion ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((χ' a : ℂˣ) : ℂ) *
        ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    funext a
    rw [integrand_shift v χ χ' c h a (s + c) _]
    congr 2; ring
  rw [← heq]; exact h1

theorem isLocalZeta31ConvergentAbove_shift (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℂ)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) =
      ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c))
    (g : LocalGL3 v) (σ₀ : ℝ) (hc : IsLocalZeta31ConvergentAbove v μ ν W χ g σ₀) :
    IsLocalZeta31ConvergentAbove v μ ν W χ' g (σ₀ - c.re) := by
  intro s hs
  have h1 := hc (s + c) (by simp only [Complex.add_re]; linarith)
  have heq : (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
        ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + c - 1)) =
      (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ' p.1 : ℂˣ) : ℂ) *
        ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    funext p
    rw [integrand_shift v χ χ' c h p.1 (s + c) _]
    congr 2; ring
  rw [← heq]; exact h1

theorem inv_shift (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℂ)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) =
      ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c)) :
    ∀ a : (v.adicCompletion ℚ)ˣ, ((χ⁻¹ a : ℂˣ) : ℂ) =
      ((χ'⁻¹ a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-(-c)) := by
  intro a
  have hm : (((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)) ≠ 0 := by
    have := LanglandsTunnell.TateLocal.modulus_pos (a := (a : v.adicCompletion ℚ)) a.ne_zero
    exact_mod_cast this.ne'
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h a, neg_neg, mul_inv]
  rw [Complex.cpow_neg, inv_inv]

theorem localZetaDual31_shift (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℂ)
    (h : ∀ a : (v.adicCompletion ℚ)ˣ, ((χ a : ℂˣ) : ℂ) =
      ((χ' a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c))
    (s : ℂ) (g : LocalGL3 v) :
    localZetaDual31 v μ ν W χ (1 - s) g = localZetaDual31 v μ ν W χ' (1 - (s - c)) g := by
  unfold localZetaDual31
  rw [localZeta31_shift v μ ν (dualWhittakerFn3 W) χ⁻¹ χ'⁻¹ (-c) (inv_shift v χ χ' c h)]
  congr 1; ring

end Ws31.SepShift

end

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (c : ℂ) (hc : c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1)
    (hexp : X.form ≠ 0 ∧ ∀ v, ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        X.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (X.whittakerLoc v))
    (hbad : ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
      (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, X.whittakerLoc v (g * k) = X.whittakerLoc v g) ∧
      (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (X.whittakerLoc v), W ≠ 0 →
        X.whittakerLoc v ∈ gl3CyclicSubspace W))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (h1 : ∀ w ∈ S, w ≠ v → X.whittakerLoc w 1 = 1)
    (hadm : ∀ w ∈ S, ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
      ∃ B : Finset (LocalGL3 w → ℂ), ∀ G ∈ gl3CyclicSubspace (X.whittakerLoc w),
        (∀ k ∈ Uw, ∀ g : LocalGL3 w, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((TateGlobal.localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((TateGlobal.localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS) :
    ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ,
      (∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ c) →
      (∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧ (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal →
      IsArchCompAt ℚ σ w t e) ∧ ((χ (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) ∧ ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧
      archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0) →
      ∀ (g g' : LocalGL3 v) (σ₀ σ₁ : ℝ) (P Q Pd Qd P' Q' Pd' Qd' : Polynomial ℂ),
        Q ≠ 0 → Q' ≠ 0 → Qd ≠ 0 → Qd' ≠ 0 →
        letI := localBorel ℚ v
        (IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re → Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ s g = P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (dualWhittakerFn3 (X.whittakerLoc v)) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re → Qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (X.whittakerLoc v) χ (1 - s) g = Pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))) →
        (IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ g' σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re → Q'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ s g' = P'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
          IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (dualWhittakerFn3 (X.whittakerLoc v)) χ⁻¹ (weylPrime3 * transposeInv3 g') σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re → Qd'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              (X.whittakerLoc v) χ (1 - s) g' = Pd'.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))) →
        (P * Pd' * Q' * Qd = P' * Pd * Q * Qd' ∧ (P ≠ 0 → Pd ≠ 0)) := by
  intro χ hχ harch g g' σ₀ σ₁ P Q Pd Qd P' Q' Pd' Qd' hQ hQ' hQd hQd' hg hg'
  letI := localBorel ℚ v
  obtain ⟨hcv, hP, hcvd, hPd⟩ := hg
  obtain ⟨hcv', hP', hcvd', hPd'⟩ := hg'
  obtain ⟨gInf, σ', hσ'adm, ⟨t, e, hσ't, hpar⟩, hnz⟩ := harch

  obtain ⟨τ, hτ, hτunr, hτv, hτinf⟩ :=
    LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt
      v χ hχ e hpar
  obtain ⟨c₀, hc₀⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers v χ
      (TateGlobal.localChar τ v) (fun u hu hu' => (hτv u hu hu').symm)

  obtain ⟨y, y', A, At, σR, σL, hA0, hR, hL⟩ :=
    LanglandsTunnell.CubicInduction.exists_globalZeta30_eq_mul_localZeta30_and_globalZetaDual31_eq_mul_of_isCubicInductionDataOn
      K _hdeg ψ _hψ μ _hμ _hlev _hns D U gen S hSbad X hX hcont hW hW' hcontW hcontW' c hc hexp hbad E hE ν_mul v hv h1 hadm hcent hS hS' τ hτ hτunr e hτinf gInf ⟨σ', hσ'adm, ⟨t, hσ't⟩, hnz⟩ g g'

  obtain ⟨E₁, hE₁, -, σa, σb, hE₁R, hE₁L⟩ :=
    LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
      K _hdeg ψ _hψ μ _hμ _hlev _hns D U gen (S : Set (HeightOneSpectrum (𝓞 ℚ))) X hX hcont hW hW' hcontW hcontW' c hc y τ hτ
  obtain ⟨E₂, hE₂, -, σa', σb', hE₂R, hE₂L⟩ :=
    LanglandsTunnell.CubicInduction.exists_entire_eq_globalZeta30_eq_mul_globalZetaDual31_of_isCubicInductionDataOn
      K _hdeg ψ _hψ μ _hμ _hlev _hns D U gen (S : Set (HeightOneSpectrum (𝓞 ℚ))) X hX hcont hW hW' hcontW hcontW' c hc y' τ hτ

  have hN1 : 1 < Ideal.absNorm v.asIdeal := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega

  have hsub : Differentiable ℂ (fun s : ℂ => s - c₀) := differentiable_id.sub_const c₀
  refine Ws31.SepCore.core (Ideal.absNorm v.asIdeal) hN1
    (fun s => E₁ (s - c₀)) (fun s => E₂ (s - c₀)) (hE₁.comp hsub) (hE₂.comp hsub)
    (max σ₀ (max (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))))
    (min (1 - σ₁) (min (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re))))
    (fun s => A (s - c₀)) (fun s => c * At (s - c₀))
    (fun s => localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ s g)
    (fun s => localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (X.whittakerLoc v) χ s g')
    (fun s => localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
      (X.whittakerLoc v) χ (1 - s) g)
    (fun s => localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
      (X.whittakerLoc v) χ (1 - s) g')
    ?_ ?_ ?_ ?_ ?_ P Q Pd Qd P' Q' Pd' Qd' hQ hQ' hQd hQd' ?_ ?_ ?_ ?_
  ·
    intro σ
    obtain ⟨s₀, hs₀, hA⟩ := hA0 (σ - c₀.re)
    refine ⟨s₀ + c₀, ?_, ?_⟩
    · simp only [Complex.add_re]; linarith
    · simpa using hA
  · intro s hs
    have h1 : σa < (s - c₀).re := by simp only [Complex.sub_re]; have := le_max_left (σa + c₀.re) (σa' + c₀.re); linarith [le_max_right σ₀ (max (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))), le_max_right (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))]
    have h2 : σR < (s - c₀).re := by simp only [Complex.sub_re]; linarith [le_max_right σ₀ (max (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))), le_max_left (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))]
    beta_reduce
    rw [hE₁R _ h1, (hR _ h2).1, Ws31.SepShift.localZeta30_shift v _ (X.whittakerLoc v) χ (TateGlobal.localChar τ v) c₀ hc₀ s g]
  · intro s hs
    have h1 : σa' < (s - c₀).re := by simp only [Complex.sub_re]; have := le_max_right (σa + c₀.re) (σa' + c₀.re); linarith [le_max_right σ₀ (max (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))), le_max_right (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))]
    have h2 : σR < (s - c₀).re := by simp only [Complex.sub_re]; linarith [le_max_right σ₀ (max (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))), le_max_left (σR + c₀.re) (max (σa + c₀.re) (σa' + c₀.re))]
    beta_reduce
    rw [hE₂R _ h1, (hR _ h2).2, Ws31.SepShift.localZeta30_shift v _ (X.whittakerLoc v) χ (TateGlobal.localChar τ v) c₀ hc₀ s g']
  · intro s hs
    have h1 : (s - c₀).re < σb := by
      simp only [Complex.sub_re]
      have := min_le_right (1 - σ₁) (min (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re)))
      have := min_le_right (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re))
      have := min_le_left (σb + c₀.re) (σb' + c₀.re)
      linarith
    have h2 : (s - c₀).re < σL := by
      simp only [Complex.sub_re]
      have := min_le_right (1 - σ₁) (min (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re)))
      have := min_le_left (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re))
      linarith
    beta_reduce
    rw [hE₁L _ h1, (hL _ h2).1, Ws31.SepShift.localZetaDual31_shift v _ _ (X.whittakerLoc v) χ (TateGlobal.localChar τ v) c₀ hc₀ s g]
    ring
  · intro s hs
    have h1 : (s - c₀).re < σb' := by
      simp only [Complex.sub_re]
      have := min_le_right (1 - σ₁) (min (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re)))
      have := min_le_right (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re))
      have := min_le_right (σb + c₀.re) (σb' + c₀.re)
      linarith
    have h2 : (s - c₀).re < σL := by
      simp only [Complex.sub_re]
      have := min_le_right (1 - σ₁) (min (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re)))
      have := min_le_left (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re))
      linarith
    beta_reduce
    rw [hE₂L _ h1, (hL _ h2).2, Ws31.SepShift.localZetaDual31_shift v _ _ (X.whittakerLoc v) χ (TateGlobal.localChar τ v) c₀ hc₀ s g']
    ring
  · intro s hs; exact hP s (lt_of_le_of_lt (le_max_left _ _) hs)
  · intro s hs; exact hP' s (lt_of_le_of_lt (le_max_left _ _) hs)
  · intro s hs; exact hPd s (by simp only [Complex.sub_re, Complex.one_re]; have := min_le_left (1 - σ₁) (min (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re))); linarith)
  · intro s hs; exact hPd' s (by simp only [Complex.sub_re, Complex.one_re]; have := min_le_left (1 - σ₁) (min (σL + c₀.re) (min (σb + c₀.re) (σb' + c₀.re))); linarith)

end S_LanglandsTunnell_CubicInduction_mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_mul_eq_mul_localZeta30_localZetaDual31_polynomial_of_isCubicInductionDataOn_of_forall_mem_bad (solution)
