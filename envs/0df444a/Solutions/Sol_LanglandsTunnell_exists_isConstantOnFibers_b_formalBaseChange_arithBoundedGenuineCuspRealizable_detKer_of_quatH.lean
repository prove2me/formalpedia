-- Prove2me | solution 1 for LanglandsTunnell.exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/99e17d26-4858-58a1-a352-b3159d39efe8

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ViaGeneralCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LanglandsTunnell_C8Character
import Definitions.Def_LanglandsTunnell_GalRep
import Definitions.Def_LanglandsTunnell_Lift48
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_ArithFrobResidue
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_LanglandsTunnell_OctahedralDatum
import Definitions.Def_LanglandsTunnell_P52Interface

import Theorems.Thm_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Theorems.Thm_AutomorphicForm_exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict
import Theorems.Thm_LanglandsTunnell_exists_isArithBoundedGenuineCuspRealizable_twist_centreCut
import Theorems.Thm_AutomorphicForm_HeckeEigensystem_exists_char_twist_artinFrob_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_three_of_coversModCentre_of_pos
import Theorems.Thm_AutomorphicForm_exists_isArithBoundedGenuineCuspRealizable_formalBaseChange_of_isConstantOnFibers_of_finrank_two_or_three_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH
p2m_attr_erase "instance" "ContinuousSemialgHom.instCoeTC ContinuousSemialgHom.instContinuousSemialgHomClass IsDedekindDomain.FiniteAdeleRing.instFiniteOfFiniteDimensional_definitions ContinuousSemialgHomClass.toSemialgHomClass IsDedekindDomain.FiniteAdeleRing.instAlgebraRestrictedProductHeightOneSpectrumAdicCompletionCoeValuationSubringAdicCompletionIntegersCofinite_definitions RestrictedProduct.instSMulCoe_definitions IsDedekindDomain.FiniteAdeleRing.instIsModuleTopologyOfFiniteDimensional_definitions RestrictedProduct.instContinuousSMulCoePrincipal_definitions RestrictedProduct.instContinuousSMulCoeCofinite_definitions ContinuousSemialgHom.instCoeOutSemialgHom IsDedekindDomain.FiniteAdeleRing.ComapFiberwiseSMul.toFiberwiseSMul ContinuousSemialgHom.instFunLike RestrictedProduct.instModuleCoe_fLT IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass"
p2m_attr_erase "instance" "SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex instCountableOfNumberField_definitions LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions FrobeniusDensity.liesOver_ratBelow M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "instance" "instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.CubicInduction.countable_GL2 LanglandsTunnell.CubicInduction.countable_mirabolicIndex ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions"
p2m_attr_erase "simp" "ContinuousSemialgHom.mk.injEq ContinuousSemialgHom.coe_coe IsDedekindDomain.FiniteAdeleRing.mk_apply ContinuousSemialgHom.toLinearMap_eq_coe IsDedekindDomain.FiniteAdeleRing.mul_apply RestrictedProduct.smul_apply' ContinuousSemialgHom.mk.sizeOf_spec IsDedekindDomain.FiniteAdeleRing.baseChangeLinearEquiv_tmul RestrictedProduct.single_smul IsDedekindDomain.FiniteAdeleRing.one_apply RestrictedProduct.smul_single ContinuousSemialgHom.toRingHom_eq_coe SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.RankinSelberg.mem_primeFibre LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"
p2m_attr_erase "simp" "LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk LanglandsTunnell.CubicInduction.coe_diagUnits2 LanglandsTunnell.CubicInduction.coe_diagUnitGL2 LanglandsTunnell.CubicInduction.iotaTorusLocal_zero LanglandsTunnell.CubicInduction.upperUnipotent3_zero LanglandsTunnell.CubicInduction.radicalP21_coe LanglandsTunnell.CubicInduction.coe_iotaGL LanglandsTunnell.CubicInduction.radicalP12_coe LanglandsTunnell.CubicInduction.radicalP12_zero LanglandsTunnell.CubicInduction.radicalP21_zero"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.upperUnipotent3_coe ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq AutomorphicForm.WindingDatum.mk.injEq AutomorphicForm.WindingDatum.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply"

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain NumberField.AdelicLevel HeckeIntegralSeam
p2m_open "AutomorphicForm.SmoothCusp AutomorphicForm.HeckeEigensystem"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P2
p2m_export "LanglandsTunnell.P2" "exists_pos_pow_mem relDeg primeOver primeOver_isMaximal under_primeOver seedFrob liftOf liftTraceSeed seedFrob_mem Artin.artinFrob"
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"

open Classical in
private theorem isRelDegree_relDeg {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G) :
    IsRelDegree H σ (relDeg H σ) := by
  refine ⟨(Nat.find_spec (exists_pos_pow_mem H σ)).1, (Nat.find_spec (exists_pos_pow_mem H σ)).2, fun m hm hlt h => ?_⟩
  exact Nat.find_min (exists_pos_pow_mem H σ) hlt ⟨hm, h⟩

private theorem liftTraceSeed_a {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L))
    (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) :
    (liftTraceSeed e H).a w = (liftOf (e (seedFrob H w))).trace := rfl

end LanglandsTunnell.P2

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "Matrix FLT.ExplicitLift LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

private abbrev _root_.LanglandsTunnell.P4.Mat : Type := Lift48.Mat

p2m_export "LanglandsTunnell.P4" "Mat"
private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

private theorem mem_map_redc_K48_of_det_ne_zero :
    ∀ m : Matrix (Fin 2) (Fin 2) (ZMod 3), m.det ≠ 0 → m ∈ Lift48.K48.map (·.map redc) := by decide

private theorem lift_exists (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat), M.map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨M, hM, hMg⟩ := List.mem_map.1 (mem_map_redc_K48_of_det_ne_zero _ hdet)
  exact ⟨M, (Lift48.mem_closure_iff_mem_K48 M).2 hM, by rw [map_red_eq_map_redc]; exact hMg⟩

private theorem liftOf_spec (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    liftOf g ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ∧
      (liftOf g).map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Classical.epsilon_spec (p := fun M : Mat =>
    M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ∧ M.map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)))
    (lift_exists g)

private theorem liftOf_mem (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    liftOf g ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) := (liftOf_spec g).1

private theorem liftOf_red (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (liftOf g).map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := (liftOf_spec g).2

private theorem nodup_map_redc_K48 : (Lift48.K48.map fun k => k.map redc).Nodup := by decide

private theorem lift_unique_K48 {M N : Mat} (hM : M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat))
    (hN : N ∈ Submonoid.closure ({Slift, Tlift} : Set Mat)) (h : M.map red = N.map red) : M = N :=
  List.inj_on_of_nodup_map nodup_map_redc_K48 ((Lift48.mem_closure_iff_mem_K48 M).1 hM)
    ((Lift48.mem_closure_iff_mem_K48 N).1 hN)
    (by rwa [map_red_eq_map_redc, map_red_eq_map_redc] at h)

private theorem liftOf_mul (g h : GL (Fin 2) (ZMod 3)) : liftOf (g * h) = liftOf g * liftOf h :=
  lift_unique_K48 (liftOf_mem _) (Submonoid.mul_mem _ (liftOf_mem _) (liftOf_mem _))
    (by rw [Matrix.map_mul, liftOf_red, liftOf_red, liftOf_red, Units.val_mul])

private theorem liftOf_one : liftOf (1 : GL (Fin 2) (ZMod 3)) = 1 :=
  lift_unique_K48 (liftOf_mem _) (Submonoid.one_mem _)
    (by rw [liftOf_red, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)])

private theorem liftOf_inv_mul (g : GL (Fin 2) (ZMod 3)) : liftOf g⁻¹ * liftOf g = 1 := by
  rw [← liftOf_mul, inv_mul_cancel, liftOf_one]

private theorem liftOf_mul_inv (g : GL (Fin 2) (ZMod 3)) : liftOf g * liftOf g⁻¹ = 1 := by
  rw [← liftOf_mul, mul_inv_cancel, liftOf_one]

private theorem liftOf_pow (g : GL (Fin 2) (ZMod 3)) : ∀ n : ℕ, liftOf (g ^ n) = liftOf g ^ n
  | 0 => by rw [pow_zero, pow_zero, liftOf_one]
  | (n + 1) => by rw [pow_succ, pow_succ, liftOf_mul, liftOf_pow g n]

private theorem trace_liftOf_conj (g h : GL (Fin 2) (ZMod 3)) : (liftOf (g * h * g⁻¹)).trace = (liftOf h).trace := by
  rw [liftOf_mul, liftOf_mul, Matrix.trace_mul_cycle, liftOf_inv_mul, one_mul]

private theorem det_liftOf_conj (g h : GL (Fin 2) (ZMod 3)) : (liftOf (g * h * g⁻¹)).det = (liftOf h).det := by
  rw [liftOf_mul, liftOf_mul, det_mul, det_mul, mul_right_comm, ← det_mul, liftOf_mul_inv, det_one, one_mul]

private theorem relDeg_dvd_of_pow_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G) {m : ℕ}
    (hm : σ ^ m ∈ H) : relDeg H σ ∣ m := by
  have hn := isRelDegree_relDeg H σ
  by_contra hndvd
  have hpos : 0 < m % relDeg H σ :=
    Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
  have hlt : m % relDeg H σ < relDeg H σ := Nat.mod_lt _ hn.1
  refine hn.2.2 _ hpos hlt ?_
  have h := Nat.div_add_mod m (relDeg H σ)
  have hrew : σ ^ (m % relDeg H σ) = ((σ ^ relDeg H σ) ^ (m / relDeg H σ))⁻¹ * σ ^ m := by
    rw [← pow_mul, eq_inv_mul_iff_mul_eq, ← pow_add, h]
  rw [hrew]
  exact H.mul_mem (H.inv_mem (H.pow_mem hn.2.1 _)) hm

private theorem liftTraceSeed_b {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)} {H : Subgroup (L ≃ₐ[ℚ] L)}
    (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) :
    (liftTraceSeed e H).b w = (liftOf (e (seedFrob H w))).det := rfl

end LanglandsTunnell.P4

section
open LanglandsTunnell.Lift48 (P16 pw)
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P5
p2m_open "LanglandsTunnell"

open FLT.ExplicitLift Matrix

private theorem P16_mul_pw_seven : ∀ x ∈ P16, x * pw x 7 = 1 ∧ pw x 7 * x = 1 ∧ pw x 7 ∈ P16 := by decide

end LanglandsTunnell.P5
end

section
p2m_open "LanglandsTunnell.P4~Mat"
open LanglandsTunnell.Lift48 (K48 Mat P16 mem_closure_iff_mem_K48 pw)
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P0
p2m_open "LanglandsTunnell"

open FLT.ExplicitLift Matrix

private theorem eq_one_of_mem_K48_of_map_redc_eq_one :
    ∀ k ∈ K48, k.map redc = 1 → k = 1 := by decide

end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
open LanglandsTunnell.P0

private theorem P16_sub_K48 : ∀ p ∈ P16, p ∈ K48 := by decide

private theorem lift_unique : ∀ M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat), ∀ N ∈ P16,
    M.map red = N.map red → M = N := by
  intro M hM N hN h
  have hK : M ∈ K48 := (mem_closure_iff_mem_K48 M).1 hM
  obtain ⟨h7, h7', h7P⟩ := P16_mul_pw_seven N hN
  have hprodK : M * pw N 7 ∈ K48 :=
    (mem_closure_iff_mem_K48 _).1 (Submonoid.mul_mem _ hM ((mem_closure_iff_mem_K48 _).2 (P16_sub_K48 _ h7P)))
  have hone : (M * pw N 7).map redc = 1 := by
    rw [← map_red_eq_map_redc, Matrix.map_mul, h, ← Matrix.map_mul, h7,
      Matrix.map_one _ (map_zero red) (map_one red)]
  have h1 : M * pw N 7 = 1 := eq_one_of_mem_K48_of_map_redc_eq_one _ hprodK hone
  calc M = M * pw N 7 * N := by rw [mul_assoc, h7', mul_one]
    _ = N := by rw [h1, one_mul]

end LanglandsTunnell.P5
end

section
p2m_open "LanglandsTunnell.P4~Mat"
open LanglandsTunnell.Lift48 (Mat P16 det2 det2_eq_det mem_closure_iff_mem_K48)
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P5
p2m_open "LanglandsTunnell"

open NumberField Matrix FLT.ExplicitLift
open LanglandsTunnell.P0

private theorem nodup_P16 : P16.Nodup := by decide

private theorem P16_det2 : ∀ M ∈ P16, det2 M = 1 ∨ det2 M = -1 := by decide

private theorem det_map_red_ne_zero (M : Mat) (hM : M ∈ P16) : (M.map red).det ≠ 0 := by
  have h : (M.map red).det = red M.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, ← det2_eq_det]
  rcases P16_det2 M hM with h1 | h1
  · rw [h1, map_one]
    exact one_ne_zero
  · rw [h1, map_neg, map_one]
    decide

section Index

variable {L : Type} [Field L] [NumberField L]

private noncomputable def redUnit (M : {M : Mat // M ∈ P16}) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.1.map red) (det_map_red_ne_zero M.1 M.2)

private theorem coe_redUnit (M : {M : Mat // M ∈ P16}) :
    (redUnit M : Matrix (Fin 2) (Fin 2) (ZMod 3)) = M.1.map red := rfl

private noncomputable def toSylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Mat // M ∈ P16}) : sylowH e :=
  ⟨e.symm (redUnit M), M.1, M.2, by rw [MulEquiv.apply_symm_apply, coe_redUnit]⟩

private theorem toSylowH_bijective (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Function.Bijective (toSylowH e) := by
  constructor
  · rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    have h1 : redUnit ⟨M, hM⟩ = redUnit ⟨N, hN⟩ := e.symm.injective (congrArg Subtype.val h)
    have h2 : M.map red = N.map red := by
      rw [← coe_redUnit ⟨M, hM⟩, ← coe_redUnit ⟨N, hN⟩, h1]
    exact Subtype.ext (lift_unique M ((mem_closure_iff_mem_K48 M).2 (P16_sub_K48 M hM)) N hN h2)
  · rintro ⟨γ, M, hM, hMγ⟩
    refine ⟨⟨M, hM⟩, Subtype.ext ?_⟩
    show e.symm (redUnit ⟨M, hM⟩) = γ
    rw [MulEquiv.symm_apply_eq]
    exact Units.ext (by rw [coe_redUnit]; exact hMγ)

end Index

end LanglandsTunnell.P5
end

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P4
p2m_open "LanglandsTunnell"

open NumberField IsDedekindDomain Matrix AutomorphicForm

section Transitivity

variable (F F' K : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K]
  [NumberField K]
  [Algebra (𝓞 F) (𝓞 F')] [Algebra.IsIntegral (𝓞 F) (𝓞 F')]
  [Algebra (𝓞 F') (𝓞 K)] [Algebra.IsIntegral (𝓞 F') (𝓞 K)]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  [IsScalarTower (𝓞 F) (𝓞 F') (𝓞 K)]
  {R : Type*} [CommRing R]

omit [NumberField F] [NumberField F'] [NumberField K] in

private theorem _root_.LanglandsTunnell.P4.under_under (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (𝔓.under (𝓞 F')).under (𝓞 F) = 𝔓.under (𝓞 F) :=
  HeightOneSpectrum.ext (Ideal.under_under 𝔓.asIdeal)

p2m_export "LanglandsTunnell.P4" "under_under"
omit [NumberField K] in

private theorem inertiaDeg_under_mul (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal
      = (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' (𝔓.under (𝓞 F')).asIdeal
        * (𝔓.under (𝓞 F')).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI : (𝔓.under (𝓞 F')).asIdeal.LiesOver (𝔓.under (𝓞 F)).asIdeal :=
    ⟨congrArg HeightOneSpectrum.asIdeal (under_under F F' K 𝔓).symm⟩
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 F')).asIdeal := ⟨rfl⟩
  exact Ideal.inertiaDeg_algebra_tower _ _ _

end Transitivity

end LanglandsTunnell.P4

set_option pp.deepTerms true
set_option pp.proofs true
end

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P5
namespace OctInhabitant
p2m_open "LanglandsTunnell"

open NumberField IsDedekindDomain AutomorphicForm Matrix
open FLT.ExplicitLift LanglandsTunnell.Lift48
open FLT.TunnellOctahedralGlobalCarrier FLT.Qepw139bOctahedralDatumLinkedRecarve
open scoped MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

private def _root_.LanglandsTunnell.P5.OctInhabitant.det2 (m : M₃) : ZMod 3 := m 0 0 * m 1 1 - m 0 1 * m 1 0

p2m_export "LanglandsTunnell.P5.OctInhabitant" "det2"
private theorem _root_.LanglandsTunnell.P5.OctInhabitant.det2_eq_det (m : M₃) : det2 m = m.det := (Matrix.det_fin_two m).symm

p2m_export "LanglandsTunnell.P5.OctInhabitant" "det2_eq_det"
private theorem det2_coe_ne_zero (g : GL (Fin 2) (ZMod 3)) : det2 (g : M₃) ≠ 0 := by
  rw [det2_eq_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero

end LanglandsTunnell.P5.OctInhabitant
end

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P5
namespace OctB4
p2m_open "LanglandsTunnell"

open LanglandsTunnell.P5.OctInhabitant IntermediateField
open scoped MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

private def slP (m : M₃) : Prop := det2 m = 1
private def q8P (m : M₃) : Prop := det2 m = 1 ∧ m * m * m * m = 1
private scoped instance : DecidablePred slP := fun m => inferInstanceAs (Decidable (det2 m = 1))
private scoped instance : DecidablePred q8P := fun m => inferInstanceAs (Decidable (det2 m = 1 ∧ m * m * m * m = 1))

private def inv3 (m : M₃) : M₃ := fun i j =>
  if i = 0 then (if j = 0 then det2 m * m 1 1 else -(det2 m * m 0 1))
  else (if j = 0 then -(det2 m * m 1 0) else det2 m * m 0 0)

private theorem fact_inv3 : ∀ m : M₃, det2 m ≠ 0 → m * inv3 m = 1 := by decide
private theorem fact_q8_one : q8P 1 := by decide
set_option maxRecDepth 4000 in
private theorem fact_q8_mul : ∀ a : M₃, q8P a → ∀ b : M₃, q8P b → q8P (a * b) := by decide
private theorem fact_q8_inv : ∀ a : M₃, q8P a → q8P (inv3 a) := by decide
private theorem coe_inv_eq_inv3 (g : GL (Fin 2) (ZMod 3)) : ((g⁻¹ : GL (Fin 2) (ZMod 3)) : M₃) = inv3 (g : M₃) :=
  Units.inv_eq_of_mul_eq_one_right (fact_inv3 _ (det2_coe_ne_zero g))

private def slSub : Subgroup (GL (Fin 2) (ZMod 3)) := MonoidHom.ker Matrix.GeneralLinearGroup.det

private scoped instance slSub_normal : slSub.Normal := MonoidHom.normal_ker _

private theorem mem_slSub_iff (g : GL (Fin 2) (ZMod 3)) : g ∈ slSub ↔ slP (g : M₃) := by
  rw [slSub, MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, slP,
    det2_eq_det]

private def q8Sub : Subgroup (GL (Fin 2) (ZMod 3)) where
  carrier := {g | q8P (g : M₃)}
  one_mem' := by show q8P ((1 : GL (Fin 2) (ZMod 3)) : M₃); rw [Units.val_one]; exact fact_q8_one
  mul_mem' {a b} ha hb := by
    show q8P ((a * b : GL (Fin 2) (ZMod 3)) : M₃); rw [Units.val_mul]; exact fact_q8_mul _ ha _ hb
  inv_mem' {a} ha := by show q8P ((a⁻¹ : GL (Fin 2) (ZMod 3)) : M₃); rw [coe_inv_eq_inv3]; exact fact_q8_inv _ ha

private theorem coe_pow_four (n : GL (Fin 2) (ZMod 3)) :
    ((n ^ 4 : GL (Fin 2) (ZMod 3)) : M₃) = (n : M₃) * n * n * n := by
  rw [Units.val_pow_eq_pow_val, pow_succ, pow_succ, pow_succ, pow_one]

private theorem mem_q8Sub_iff' (g : GL (Fin 2) (ZMod 3)) : g ∈ q8Sub ↔ g ∈ slSub ∧ g ^ 4 = 1 := by
  rw [mem_slSub_iff, Units.ext_iff, coe_pow_four, Units.val_one]; exact Iff.rfl

private scoped instance q8Sub_normal : q8Sub.Normal :=
  ⟨fun n hn g => by
    rw [mem_q8Sub_iff'] at hn ⊢
    exact ⟨slSub_normal.conj_mem n hn.1 g, by rw [conj_pow, hn.2, mul_one, mul_inv_cancel]⟩⟩

private def cutEquiv (P : M₃ → Prop) :
    {g : GL (Fin 2) (ZMod 3) // P (g : M₃)} ≃ {m : M₃ // det2 m ≠ 0 ∧ P m} where
  toFun g := ⟨(g.1 : M₃), det2_coe_ne_zero g.1, g.2⟩
  invFun m := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero m.1 (by rw [← det2_eq_det]; exact m.2.1), m.2.2⟩
  left_inv g := by apply Subtype.ext; apply Units.ext; rfl
  right_inv m := rfl

private theorem fact_card_gl : Fintype.card {m : M₃ // det2 m ≠ 0 ∧ True} = 48 := by decide
private theorem fact_card_sl : Fintype.card {m : M₃ // det2 m ≠ 0 ∧ slP m} = 24 := by decide
private theorem fact_card_q8 : Fintype.card {m : M₃ // det2 m ≠ 0 ∧ q8P m} = 8 := by decide
private theorem card_gl : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Nat.card_congr ((Equiv.subtypeUnivEquiv (p := fun g : GL (Fin 2) (ZMod 3) => True) fun _ => trivial).symm),
    Nat.card_congr (cutEquiv fun _ => True), Nat.card_eq_fintype_card, fact_card_gl]

private theorem card_slSub : Nat.card slSub = 24 := by
  have h : Nat.card slSub = Nat.card {g : GL (Fin 2) (ZMod 3) // slP (g : M₃)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_slSub_iff g)
  rw [h, Nat.card_congr (cutEquiv slP), Nat.card_eq_fintype_card, fact_card_sl]

private theorem card_q8Sub : Nat.card q8Sub = 8 := by
  rw [show Nat.card q8Sub = Nat.card {g : GL (Fin 2) (ZMod 3) // q8P (g : M₃)} from rfl,
    Nat.card_congr (cutEquiv q8P), Nat.card_eq_fintype_card, fact_card_q8]

section Tower

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3))

private def galSL : Subgroup (L ≃ₐ[ℚ] L) := slSub.comap e.toMonoidHom
private def galQ8 : Subgroup (L ≃ₐ[ℚ] L) := q8Sub.comap e.toMonoidHom
private scoped instance galSL_normal : (galSL e).Normal := Subgroup.Normal.comap inferInstance _
private scoped instance galQ8_normal : (galQ8 e).Normal := Subgroup.Normal.comap inferInstance _

private theorem card_comap_equiv (H : Subgroup (GL (Fin 2) (ZMod 3))) :
    Nat.card (H.comap e.toMonoidHom) = Nat.card H := by
  rw [Subgroup.comap_equiv_eq_map_symm']
  exact Subgroup.card_map_of_injective e.symm.injective

private theorem card_galSL : Nat.card (galSL e) = 24 := by rw [galSL, card_comap_equiv, card_slSub]
private theorem card_galQ8 : Nat.card (galQ8 e) = 8 := by rw [galQ8, card_comap_equiv, card_q8Sub]
include e in
private theorem card_gal : Nat.card (L ≃ₐ[ℚ] L) = 48 := by rw [Nat.card_congr e.toEquiv, card_gl]

private def fldE : IntermediateField ℚ L := fixedField (galSL e)
private def fldLc : IntermediateField ℚ L := fixedField (galQ8 e)
private theorem finrank_fldE_top : Module.finrank (fldE e) L = 24 := by
  rw [fldE, finrank_fixedField_eq_card]; exact card_galSL e
private theorem finrank_fldLc_top : Module.finrank (fldLc e) L = 8 := by
  rw [fldLc, finrank_fixedField_eq_card]; exact card_galQ8 e
variable [IsGalois ℚ L]

private scoped instance isGalois_fldE : IsGalois ℚ (fldE e) := IsGalois.of_fixedField_normal_subgroup _
private scoped instance isGalois_fldLc : IsGalois ℚ (fldLc e) := IsGalois.of_fixedField_normal_subgroup _

include e in
private theorem finrank_L : Module.finrank ℚ L = 48 := by rw [← IsGalois.card_aut_eq_finrank]; exact card_gal e

omit [IsGalois ℚ L] in
private theorem finrank_bot_of_top (htot : Module.finrank ℚ L = 48) (F : IntermediateField ℚ L) (n k : ℕ)
    (hk : 0 < k) (hnk : n * k = 48) (h : Module.finrank F L = k) : Module.finrank ℚ F = n := by
  have hmul := Module.finrank_mul_finrank ℚ F L
  rw [h, htot, ← hnk] at hmul
  exact Nat.eq_of_mul_eq_mul_right hk hmul

private theorem finrank_fldE : Module.finrank ℚ (fldE e) = 2 :=
  finrank_bot_of_top (finrank_L e) _ 2 24 (by omega) rfl (finrank_fldE_top e)
private theorem finrank_fldLc : Module.finrank ℚ (fldLc e) = 6 :=
  finrank_bot_of_top (finrank_L e) _ 6 8 (by omega) rfl (finrank_fldLc_top e)
end Tower

end LanglandsTunnell.P5.OctB4
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4"

section
set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P2
p2m_export "LanglandsTunnell.P2" "exists_pos_pow_mem relDeg primeOver primeOver_isMaximal under_primeOver seedFrob liftOf liftTraceSeed seedFrob_mem Artin.artinFrob"
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift AutomorphicForm"
open LanglandsTunnell.P0 LanglandsTunnell.P5
open scoped Pointwise

section GalInt

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup (L ≃ₐ[ℚ] L))
  (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)))

private scoped instance isGaloisGroup_ringOfIntegers :
    IsGaloisGroup H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L)
    (FixedPoints.intermediateField H : IntermediateField ℚ L) L

end GalInt
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4"

end LanglandsTunnell.P2
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

set_option pp.deepTerms true
set_option pp.proofs true
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P0
p2m_open "LanglandsTunnell"

open Polynomial

private theorem card_le_of_forall_pow_eq {R : Type*} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ y : R, y ^ q = y) : Nat.card R ≤ q := by
  classical
  haveI := Fintype.ofFinite R
  have hdeg : (X ^ q - X : R[X]).natDegree = q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    rw [natDegree_X]
    exact hq
  have hf0 : (X ^ q - X : R[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hroots : ∀ y : R, y ∈ (X ^ q - X : R[X]).roots := fun y =>
    (mem_roots hf0).2 (by simp [h y])
  calc Nat.card R = Fintype.card R := Nat.card_eq_fintype_card
    _ ≤ (X ^ q - X : R[X]).roots.toFinset.card :=
        Finset.card_le_card fun y _ => Multiset.mem_toFinset.2 (hroots y)
    _ ≤ Multiset.card (X ^ q - X : R[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : R[X]).natDegree := card_roots' _
    _ = q := hdeg

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [Finite G] [Algebra.IsInvariant A B G]
  {C : Type*} [CommRing C] [Algebra C B] [Algebra A C] [IsScalarTower A C B]

end LanglandsTunnell.P0
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P0
p2m_open "LanglandsTunnell"

section Tower

open NumberField FrobeniusDensity MulAction
open scoped Pointwise

attribute [local instance 10000] Ideal.instMulActionElemPrimesOver

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

private theorem tower_isGaloisGroup (K : Subgroup (L ≃ₐ[ℚ] L)) : IsGaloisGroup (↥K) (𝓞 (↥(fixFld K))) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing _ _ _ (↥(fixFld K)) L

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

omit hℓ in
private theorem card_int_quot_ratPrimeIdeal : Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

private theorem finite_int_quot_ratPrimeIdeal : Finite (ℤ ⧸ ratPrimeIdeal ℓ) :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  Finite.of_equiv _ (Int.quotientSpanNatEquivZMod ℓ).toEquiv.symm

end Tower
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

end LanglandsTunnell.P0
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P0
p2m_open "LanglandsTunnell"

section BadPrimes

p2m_open "NumberField Ideal NumberField.Ideal IsDedekindDomain Ideal.IsDedekindDomain FrobeniusDensity"
open scoped Pointwise

variable (L : Type*) [Field L] [NumberField L]

private theorem tower_exists_smul_ne {g : L ≃ₐ[ℚ] L} (hg : g ≠ 1) : ∃ x : 𝓞 L, g • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 L, g • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hg (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) z
  have hx : g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x :=
    congrArg (algebraMap (𝓞 L) L) (hcon x)
  have hy' : g (algebraMap (𝓞 L) L y) = algebraMap (𝓞 L) L y :=
    congrArg (algebraMap (𝓞 L) L) (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

private theorem tower_finite_setOf_inertia_ne_bot :
    {v : HeightOneSpectrum (𝓞 L) | v.asIdeal.inertia (L ≃ₐ[ℚ] L) ≠ ⊥}.Finite := by
  classical
  choose x hx using fun g : {g : L ≃ₐ[ℚ] L // g ≠ 1} => tower_exists_smul_ne L g.2
  refine Set.Finite.subset (Set.Finite.biUnion
    (Set.finite_univ (α := {g : L ≃ₐ[ℚ] L // g ≠ 1}))
    (fun g _ => Ideal.finite_factors (I := Ideal.span {g.1 • x g - x g}) ?_)) ?_
  · rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hx g
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    obtain ⟨g, hgmem, hgne⟩ := (v.asIdeal.inertia (L ≃ₐ[ℚ] L)).bot_or_exists_ne_one.resolve_left hv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨⟨g, hgne⟩, Set.mem_univ _, ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hgmem (x ⟨g, hgne⟩)

private noncomputable def towerBadPrimes : Finset ℕ :=
  insert 0 (insert 1 (((tower_finite_setOf_inertia_ne_bot L).image
    (fun v => Nat.card (ℤ ⧸ v.asIdeal.under ℤ))).toFinset))

variable {L}

private theorem tower_inertia_eq_bot_of_notMem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓbad : ℓ ∉ towerBadPrimes L)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [hQ : Q.LiesOver (ratPrimeIdeal ℓ)] : Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  by_contra hcon
  apply hℓbad
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ?_)))
  rw [Set.Finite.mem_toFinset]
  refine ⟨⟨Q, inferInstance, hQbot⟩, hcon, ?_⟩
  change Nat.card (ℤ ⧸ Q.under ℤ) = ℓ
  rw [← hQ.over, Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

end BadPrimes
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

end LanglandsTunnell.P0
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity IsDedekindDomain Ideal.IsDedekindDomain AutomorphicForm"

section HdensDock

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]

omit [IsGalois ℚ L] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)] in
open Rat.HeightOneSpectrum in

private theorem under_eq_ratPrime_of_natCast_mem {E : IntermediateField ℚ L}
    (𝔓 : HeightOneSpectrum (𝓞 ↥E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hmem : ((ℓ : ℕ) : 𝓞 ↥E) ∈ 𝔓.asIdeal) :
    𝔓.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ := by
  set v : HeightOneSpectrum (𝓞 ℚ) := 𝔓.under (𝓞 ℚ) with hv_def

  have hmem_v : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have : algebraMap (𝓞 ℚ) (𝓞 ↥E) ((ℓ : ℕ) : 𝓞 ℚ) ∈ 𝔓.asIdeal := by
      rwa [map_natCast]
    exact this

  have hdvd : natGenerator v ∣ ℓ := by
    rw [natGenerator_dvd_iff]
    have h := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem_v
    rwa [map_natCast] at h
  have heq : natGenerator v = ℓ := (Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) hℓ).mp hdvd
  have happ : primesEquiv (R := 𝓞 ℚ) v = ⟨ℓ, hℓ⟩ := Subtype.ext heq
  rw [hv_def, ratPrime, ← happ, Equiv.symm_apply_apply]

private theorem card_quot_ratPrime (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card (𝓞 ℚ ⧸ (ratPrime ⟨ℓ, hℓ⟩).asIdeal) = ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hid : (ratPrime ⟨ℓ, hℓ⟩).asIdeal
      = (Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := by
    simp [ratPrime, Rat.HeightOneSpectrum.primesEquiv,
      IsDedekindDomain.HeightOneSpectrum.ofPrime_asIdeal]
  rw [hid]
  have hequiv := Ideal.quotientEquiv (Ideal.span {((ℓ : ℕ) : ℤ)})
    ((Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm)
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm rfl
  rw [← Nat.card_congr hequiv.toEquiv]
  exact LanglandsTunnell.P0.card_int_quot_ratPrimeIdeal

variable {e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)}

end HdensDock
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

end LanglandsTunnell.P5
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
p2m_open "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section FrobPower

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

private theorem mk_pow_smul_of_isArithFrobAt {σ : G} {Q : Ideal B} (hF : IsArithFrobAt A σ Q)
    (n : ℕ) (x : B) :
    Ideal.Quotient.mk Q (σ ^ n • x)
      = Ideal.Quotient.mk Q x ^ (Nat.card (A ⧸ Q.under A) ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hx : Ideal.Quotient.mk Q (σ • x)
        = Ideal.Quotient.mk Q x ^ Nat.card (A ⧸ Q.under A) := by
      rw [← map_pow, Ideal.Quotient.eq]
      exact hF x
    rw [pow_succ, mul_smul, ih (σ • x), hx, ← pow_mul, pow_succ']

variable [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_card_pow_eq_self_of_pow_mem {H : Subgroup G} [SMulCommClass (↥H) C B]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {n : ℕ}
    (hmem : arithFrobAt A G Q ^ n ∈ H) (y : C ⧸ Q.under C) :
    y ^ (Nat.card (A ⧸ Q.under A) ^ n) = y := by
  have hF : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hfix : (arithFrobAt A G Q ^ n) • algebraMap C B c = algebraMap C B c := by
    have h : (⟨arithFrobAt A G Q ^ n, hmem⟩ : ↥H) • algebraMap C B c = algebraMap C B c := by
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    exact h
  have hq := mk_pow_smul_of_isArithFrobAt hF n (algebraMap C B c)
  rw [hfix] at hq
  rw [← map_pow, Ideal.Quotient.eq, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow,
    ← Ideal.Quotient.eq, map_pow]
  exact hq.symm

end FrobPower
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section RouteHead

variable {L : Type} [Field L] [NumberField L]

private noncomputable def ratOf {e : (L ≃ₐ[ℚ] L) ≃* GL (Fin 2) (ZMod 3)}
    (v : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) : ℕ :=
  ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (v.under (𝓞 ℚ))).1

variable [IsGalois ℚ L]

variable [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]

end RouteHead
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

set_option pp.deepTerms true
set_option pp.proofs true
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
p2m_open "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section RelDeg

variable {G : Type*} [Group G] [Finite G]

private theorem relDeg_pos (H : Subgroup G) (σ : G) : 0 < relDeg H σ := (isRelDegree_relDeg H σ).1

private theorem relDeg_dvd_relDeg {H H' : Subgroup G} (hle : H' ≤ H) (σ : G) : relDeg H σ ∣ relDeg H' σ :=
  relDeg_dvd_of_pow_mem H σ (hle (isRelDegree_relDeg H' σ).2.1)

end RelDeg
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section PowMem

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_arithFrobAt_mem_of_card_under_eq_pow {H : Subgroup G}
    [SMulCommClass (↥H) C B] [Algebra.IsInvariant C B (↥H)]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {f : ℕ}
    (hcard : Nat.card (C ⧸ Q.under C) = Nat.card (A ⧸ Q.under A) ^ f)
    (hin : Q.inertia G = ⊥) : arithFrobAt A G Q ^ f ∈ H := by
  obtain ⟨s, hs⟩ := IsArithFrobAt.exists_of_isInvariant C (↥H) Q
  have hτ : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q

  have key : ∀ x : B, (arithFrobAt A G Q ^ f) • x - (s : G) • x ∈ Q := by
    intro x
    have h1 := mk_pow_smul_of_isArithFrobAt hτ f x
    have h2 : (s : G) • x - x ^ (Nat.card (A ⧸ Q.under A) ^ f) ∈ Q := by
      have h := hs x
      rwa [hcard] at h
    rw [← Ideal.Quotient.eq, map_pow] at h2
    rw [← Ideal.Quotient.eq, h1, h2]

  have hmem : arithFrobAt A G Q ^ f * (s : G)⁻¹ ∈ Q.inertia G := by
    intro x
    have h := key ((s : G)⁻¹ • x)
    rwa [smul_inv_smul, ← mul_smul] at h
  rw [hin, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  rw [hmem]
  exact s.2

end PowMem
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section ResidueDegree

variable {L : Type} [Field L] [NumberField L]

private theorem natCast_mem_under' (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [hQl : Q.LiesOver (ratPrimeIdeal ℓ)] :
    ((ℓ : ℕ) : 𝓞 (↥(fixFld H))) ∈ Q.under (𝓞 (↥(fixFld H))) := by
  have h1 : ((ℓ : ℕ) : ℤ) ∈ ratPrimeIdeal ℓ := Ideal.mem_span_singleton_self _
  rw [hQl.over] at h1
  have h2 : algebraMap ℤ (𝓞 L) ((ℓ : ℕ) : ℤ) ∈ Q := Ideal.mem_comap.mp h1
  rw [Ideal.mem_comap, map_natCast]
  simpa using h2

variable [IsGalois ℚ L]

private theorem inertiaDeg_eq_relDeg (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (w : HeightOneSpectrum (𝓞 (↥(fixFld H)))) (hw : w.asIdeal = Q.under (𝓞 (↥(fixFld H)))) :
    (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹_› (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  haveI hZmax : (Q.under ℤ).IsMaximal := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; infer_instance
  haveI hZfin : Finite (ℤ ⧸ Q.under ℤ) := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact finite_int_quot_ratPrimeIdeal
  haveI : Fintype (ℤ ⧸ Q.under ℤ) := Fintype.ofFinite _
  haveI hGG := tower_isGaloisGroup (L := L) H
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  have hcardZ : Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact card_int_quot_ratPrimeIdeal

  haveI hkfin : Finite ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal) := by
    rw [hw]
    exact Finite.of_injective _
      (Ideal.quotientMap_injective (I := Q) (f := algebraMap (𝓞 (↥(fixFld H))) (𝓞 L)))
  haveI : Fintype ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI hkmax : w.asIdeal.IsMaximal := w.isMaximal

  have hunder : w.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ :=
    under_eq_ratPrime_of_natCast_mem w hℓ (by rw [hw]; exact natCast_mem_under' H Q)
  have hcb : Nat.card (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) = ℓ := by
    rw [hunder]; exact card_quot_ratPrime ℓ hℓ
  haveI : (w.under (𝓞 ℚ)).asIdeal.IsMaximal := (w.under (𝓞 ℚ)).isMaximal
  haveI hoverP : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩

  have hcardf : Nat.card ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal)
      = ℓ ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
    letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
    rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal), hcb]
  have hℓ1 : 1 < ℓ := hℓ.one_lt

  have hle : (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal ≤ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
    letI := Ideal.Quotient.field w.asIdeal
    have hpow : ∀ y : (𝓞 (↥(fixFld H))) ⧸ w.asIdeal,
        y ^ (ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) = y := by
      rw [hw]
      intro y
      have h := pow_card_pow_eq_self_of_pow_mem (A := ℤ) (C := 𝓞 (↥(fixFld H))) (H := H) Q
        (isRelDegree_relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).2.1 y
      rwa [hcardZ] at h
    have h1lt : 1 < ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := Nat.one_lt_pow (relDeg_pos H _).ne' hℓ1
    have hcle := card_le_of_forall_pow_eq h1lt hpow
    rw [hcardf] at hcle
    exact (Nat.pow_le_pow_iff_right hℓ1).mp hcle

  have hge : relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) ≤ (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal := by
    have hcard' : Nat.card ((𝓞 (↥(fixFld H))) ⧸ Q.under (𝓞 (↥(fixFld H))))
        = Nat.card (ℤ ⧸ Q.under ℤ) ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
      rw [hcardZ, ← hw, hcardf]
    have hmem := pow_arithFrobAt_mem_of_card_under_eq_pow (A := ℤ) (C := 𝓞 (↥(fixFld H))) (H := H) Q hcard' hI
    have hdvd := relDeg_dvd_of_pow_mem H _ hmem
    exact Nat.le_of_dvd (Ideal.inertiaDeg'_pos (w.under (𝓞 ℚ)).asIdeal w.asIdeal) hdvd
  exact le_antisymm hle hge

private theorem inertiaDeg_eq_inertiaDeg_mul {H H' : Subgroup (L ≃ₐ[ℚ] L)} (hle : H' ≤ H) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (w : HeightOneSpectrum (𝓞 (↥(fixFld H)))) (hw : w.asIdeal = Q.under (𝓞 (↥(fixFld H))))
    (w' : HeightOneSpectrum (𝓞 (↥(fixFld H')))) (hw' : w'.asIdeal = Q.under (𝓞 (↥(fixFld H')))) :
    (w'.under (𝓞 ℚ)).asIdeal.inertiaDeg' w'.asIdeal
      = (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal
          * (relDeg H' (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) / relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) := by
  rw [inertiaDeg_eq_relDeg H hℓ Q hI w hw, inertiaDeg_eq_relDeg H' hℓ Q hI w' hw']
  exact (Nat.mul_div_cancel' (relDeg_dvd_relDeg hle _)).symm

end ResidueDegree
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

set_option pp.deepTerms true
set_option pp.proofs true
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P4
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal FrobeniusDensity AutomorphicForm IsDedekindDomain Ideal.IsDedekindDomain Matrix FLT.ExplicitLift"
p2m_open "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P0 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
open scoped Pointwise MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

section Generic

variable {L : Type} [Field L] [NumberField L]

private noncomputable def ratOfE {E : IntermediateField ℚ L} (u : HeightOneSpectrum (𝓞 ↥E)) : ℕ :=
  ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (u.under (𝓞 ℚ))).1

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

set_option pp.deepTerms true
set_option pp.proofs true
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace P4
p2m_open "LanglandsTunnell"

open NumberField IsDedekindDomain AutomorphicForm FLT.ExplicitLift EisensteinWeightOne
p2m_open "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P0"
p2m_open "FrobeniusDensity Ideal NumberField.Ideal"
open scoped MatrixGroups

local notation "ZRing" => (ℤ√(-2))

section Prelim

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  {e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)}

omit [IsGalois ℚ L] in

private theorem ratOf_prime (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) : (ratOf u).Prime :=
  ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (u.under (𝓞 ℚ))).2

omit [IsGalois ℚ L] in

private theorem under_eq_ratPrime_ratOf (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    u.under (𝓞 ℚ) = ratPrime ⟨ratOf u, ratOf_prime u⟩ := by
  rw [ratPrime]
  exact (Equiv.symm_apply_apply _ _).symm

private theorem natCast_mem_ratPrime_asIdeal (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ((ℓ : ℕ) : 𝓞 ℚ) ∈ (ratPrime ⟨ℓ, hℓ⟩).asIdeal := by
  have hid : (ratPrime ⟨ℓ, hℓ⟩).asIdeal
      = (Ideal.span {((ℓ : ℕ) : ℤ)}).comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    simp [ratPrime, Rat.HeightOneSpectrum.primesEquiv,
      IsDedekindDomain.HeightOneSpectrum.ofPrime_asIdeal]
  rw [hid, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

omit [IsGalois ℚ L] in

private theorem asIdeal_under_int (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    u.asIdeal.under ℤ = ratPrimeIdeal (ratOf u) := by
  haveI : Fact (ratOf u).Prime := ⟨ratOf_prime u⟩
  refine ((Int.ideal_span_isMaximal_of_prime (ratOf u)).eq_of_le
    (Ideal.IsPrime.under ℤ u.asIdeal).ne_top ?_).symm
  show Ideal.span {((ratOf u : ℕ) : ℤ)} ≤ u.asIdeal.under ℤ
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]

  have hmem := natCast_mem_ratPrime_asIdeal (ratOf u) (ratOf_prime u)
  rw [← under_eq_ratPrime_ratOf u] at hmem
  have hmem2 : algebraMap (𝓞 ℚ) (𝓞 (↥(fixFld (sylowH e)))) ((ratOf u : ℕ) : 𝓞 ℚ)
      ∈ u.asIdeal := hmem
  simpa using hmem2

omit [IsGalois ℚ L] in

private scoped instance _root_.LanglandsTunnell.P4.primeOver_liesOver_ratPrimeIdeal (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    (primeOver (sylowH e) u).LiesOver (ratPrimeIdeal (ratOf u)) := by
  constructor
  rw [← Ideal.under_under (A := ℤ) (B := 𝓞 (↥(fixFld (sylowH e)))) (C := 𝓞 L),
    under_primeOver, asIdeal_under_int]

p2m_export "LanglandsTunnell.P4" "primeOver_liesOver_ratPrimeIdeal"
private scoped instance primeOver_isPrime (u : HeightOneSpectrum (𝓞 (↥(fixFld (sylowH e))))) :
    (primeOver (sylowH e) u).IsPrime :=
  (primeOver_isMaximal (sylowH e) u).isPrime

end Prelim
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"

end LanglandsTunnell.P4
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"

section
set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace SeedAgreeRat
p2m_open "LanglandsTunnell"

p2m_open "NumberField Ideal NumberField.Ideal IsDedekindDomain Ideal.IsDedekindDomain AutomorphicForm Matrix FLT.ExplicitLift FrobeniusDensity"
open scoped MatrixGroups

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

omit [IsGalois ℚ L] in

private theorem asIdeal_under_int_eq_of_under_eq (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (w : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld H)))
    (hw : w.under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) :
    w.asIdeal.under ℤ = ratPrimeIdeal ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine ((Int.ideal_span_isMaximal_of_prime ℓ).eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_).symm
  show Ideal.span {((ℓ : ℕ) : ℤ)} ≤ w.asIdeal.under ℤ
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
  have hmem := LanglandsTunnell.P4.natCast_mem_ratPrime_asIdeal ℓ hℓ
  have hmem' : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by rw [hw]; exact hmem
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem'
  exact hmem'

omit [IsGalois ℚ L] in

private theorem primeOver_liesOver_ratPrimeIdeal (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (w : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld H)))
    (hw : w.under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩) :
    (LanglandsTunnell.P2.primeOver H w).LiesOver (ratPrimeIdeal ℓ) := by
  constructor
  rw [← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(LanglandsTunnell.fixFld H)) (C := 𝓞 L),
    LanglandsTunnell.P2.under_primeOver, asIdeal_under_int_eq_of_under_eq H hℓ w hw]

end LanglandsTunnell.SeedAgreeRat
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace H6Glue
p2m_open "LanglandsTunnell"

open NumberField Matrix FLT.ExplicitLift
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P0 LanglandsTunnell.Lift48"

private def P16det1 : List Mat := P16.filter fun M => det2 M = 1

private theorem length_P16det1 : P16det1.length = 8 := by decide

private theorem nodup_P16det1 : P16det1.Nodup := nodup_P16.filter _

private theorem natCard_P16det1 : Nat.card {M : Mat // M ∈ P16det1} = 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
        (fun M => (List.mem_toFinset (l := P16det1) (a := M)).symm)),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup nodup_P16det1, length_P16det1]

private theorem mem_P16det1_iff (M : Mat) : M ∈ P16det1 ↔ M ∈ P16 ∧ det2 M = 1 := by
  simp only [P16det1, List.mem_filter, decide_eq_true_eq]

private theorem red_neg_one_ne_one : red (-1 : ℤ√(-2)) ≠ (1 : ZMod 3) := by
  rw [map_neg, map_one]; decide

section Card

variable {L : Type} [Field L] [NumberField L]

private theorem esymm_redUnit_mem_detKer (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    {M : Mat} (hM : M ∈ P16) (hdet : det2 M = 1) :
    e.symm (redUnit ⟨M, hM⟩) ∈ detKer e := by
  rw [mem_detKer_iff, MulEquiv.apply_symm_apply, coe_redUnit,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← det2_eq_det, hdet, map_one]

private noncomputable def toQuatH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Mat // M ∈ P16det1}) : quatH e :=
  let hPd := (mem_P16det1_iff M.1).1 M.2
  ⟨e.symm (redUnit ⟨M.1, hPd.1⟩),
    Subgroup.mem_inf.2 ⟨(toSylowH e ⟨M.1, hPd.1⟩).2, esymm_redUnit_mem_detKer e hPd.1 hPd.2⟩⟩

private theorem val_toQuatH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Mat // M ∈ P16det1}) :
    (toQuatH e M : L ≃ₐ[ℚ] L) = e.symm (redUnit ⟨M.1, ((mem_P16det1_iff M.1).1 M.2).1⟩) := rfl

private theorem toQuatH_bijective (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Function.Bijective (toQuatH e) := by
  constructor
  ·

    rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    have hP := (mem_P16det1_iff M).1 hM
    have hQ := (mem_P16det1_iff N).1 hN

    have hval : (toQuatH e ⟨M, hM⟩ : L ≃ₐ[ℚ] L) = (toQuatH e ⟨N, hN⟩ : L ≃ₐ[ℚ] L) :=
      Subtype.ext_iff.mp h

    rw [val_toQuatH, val_toQuatH] at hval

    have hred : redUnit ⟨M, hP.1⟩ = redUnit ⟨N, hQ.1⟩ := e.symm.injective hval

    have hinj : (⟨M, hP.1⟩ : {M : Mat // M ∈ P16}) = ⟨N, hQ.1⟩ :=
      (toSylowH_bijective e).1 (Subtype.ext (congrArg e.symm hred))

    have hMN : M = N := congrArg (Subtype.val (p := fun x => x ∈ P16)) hinj
    exact Subtype.ext hMN
  ·
    rintro ⟨γ, hγ⟩
    obtain ⟨hγs, hγd⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨⟨M, hM⟩, hMγ⟩ := (toSylowH_bijective e).2 ⟨γ, hγs⟩
    have hval : e.symm (redUnit ⟨M, hM⟩) = γ := congrArg Subtype.val hMγ

    have hdet_eγ : ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)).det = red (det2 M) := by
      rw [← hval, MulEquiv.apply_symm_apply, coe_redUnit,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← det2_eq_det]
    have hred : red (det2 M) = 1 := hdet_eγ ▸ (mem_detKer_iff e γ).1 hγd
    have hdet2 : det2 M = 1 := by
      rcases P16_det2 M hM with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hred) red_neg_one_ne_one
    exact ⟨⟨M, (mem_P16det1_iff M).2 ⟨hM, hdet2⟩⟩, Subtype.ext hval⟩

private theorem natCard_quatH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card (quatH e) = 8 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (toQuatH_bijective e)), natCard_P16det1]

end Card
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"

end LanglandsTunnell.H6Glue
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld detKer mem_detKer_iff quatH quatH_le_detKer sylowH Lift48.Mat Lift48.K48 Lift48.mem_closure_iff_mem_K48 Lift48.pw_eq_pow Lift48.det2 Lift48.det2_eq_det Lift48.K48_projOrder_cases Lift48.K48_det_cases Lift48.K48_row_two_even Lift48.K48_row_four Lift48.Q8 Lift48.Q8_mul_cube Lift48.Q8_sub_P16 Lift48.isPM1_iff Lift48.isProjOrder_iff P2.relDeg P2.primeOver P2.under_primeOver P2.seedFrob P2.liftOf P2.liftTraceSeed P2.seedFrob_mem IsRelDegree exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable P2.Artin.artinFrob exists_isArithBoundedGenuineCuspRealizable_twist_centreCut"
namespace CyclicCubicAssembly
p2m_open "LanglandsTunnell"

private abbrev _pinsAt (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v)
    (NumberField.AdelicBox.adelicBox F)

private abbrev _win (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    Set (AdelicGL2 (𝓞 F) F) :=
  ⋃ x ∈ T, (· * x) '' WindowedSiegel.centreCutSiegelSet F c u d₁ d₂

private theorem _complex_of_via_bounded {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (Φ : HeckeEigensystem F (Zsqrtd (-2)))
    (h : IsArithBoundedGenuineCuspRealizableVia F pins (NumberField.StandardAddChar.stdAddChar F) iotaZsqrtdNegTwo Φ) :
    IsArithBoundedGenuineCuspRealizable F pins (NumberField.StandardAddChar.stdAddChar F) (Φ.map iotaZsqrtdNegTwo) := h

section JGlue

variable {L : Type} [Field L] [NumberField L]

private theorem _P16det1_pow_four : ∀ M ∈ LanglandsTunnell.H6Glue.P16det1, M ^ 4 = 1 := by
  decide

private theorem _detKer_eq_galSL (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    LanglandsTunnell.detKer e = LanglandsTunnell.P5.OctB4.galSL e :=
  Subgroup.ext fun _ => Iff.rfl

private theorem _quatH_le_galQ8 (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    LanglandsTunnell.quatH e ≤ LanglandsTunnell.P5.OctB4.galQ8 e := by
  intro γ hγ
  obtain ⟨M, hM⟩ := (LanglandsTunnell.H6Glue.toQuatH_bijective e).2 ⟨γ, hγ⟩
  have hval : (LanglandsTunnell.H6Glue.toQuatH e M : L ≃ₐ[ℚ] L) = γ := congrArg Subtype.val hM
  rw [LanglandsTunnell.H6Glue.val_toQuatH] at hval
  have hd : γ ∈ LanglandsTunnell.detKer e := LanglandsTunnell.quatH_le_detKer e hγ
  rw [LanglandsTunnell.detKer, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hd
  change e γ ∈ LanglandsTunnell.P5.OctB4.q8Sub
  rw [LanglandsTunnell.P5.OctB4.mem_q8Sub_iff']
  refine ⟨MonoidHom.mem_ker.2 hd, ?_⟩
  rw [← hval, MulEquiv.apply_symm_apply]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, LanglandsTunnell.P5.coe_redUnit, Units.val_one,
    ← RingHom.mapMatrix_apply, ← map_pow, _P16det1_pow_four M.1 M.2, map_one]

private theorem _quatH_eq_galQ8 (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    LanglandsTunnell.quatH e = LanglandsTunnell.P5.OctB4.galQ8 e := by
  haveI : Finite (L ≃ₐ[ℚ] L) := Finite.of_equiv _ e.toEquiv.symm
  exact Subgroup.eq_of_le_of_card_ge (_quatH_le_galQ8 e)
    (le_of_eq ((LanglandsTunnell.P5.OctB4.card_galQ8 e).trans
      (LanglandsTunnell.H6Glue.natCard_quatH e).symm))

private scoped instance _quatH_normal (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (LanglandsTunnell.quatH e).Normal := by
  rw [_quatH_eq_galQ8 e]
  exact LanglandsTunnell.P5.OctB4.galQ8_normal e

variable [IsGalois ℚ L]

private theorem _finrank_rat_fixFld_detKer
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) = 2 := by
  rw [_detKer_eq_galSL e]
  exact LanglandsTunnell.P5.OctB4.finrank_fldE e

private theorem _finrank_rat_fixFld_quatH
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) = 6 := by
  rw [_quatH_eq_galQ8 e]
  exact LanglandsTunnell.P5.OctB4.finrank_fldLc e

set_option synthInstance.maxHeartbeats 320000 in

private theorem _finrank_quatH_detKer
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) = 3 := by
  have htower := Module.finrank_mul_finrank ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
    ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
  rw [_finrank_rat_fixFld_detKer e, _finrank_rat_fixFld_quatH e] at htower
  omega

private theorem _isGalois_rat_fixFld_quatH
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    IsGalois ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) := by
  rw [_quatH_eq_galQ8 e]
  exact LanglandsTunnell.P5.OctB4.isGalois_fldLc e

private scoped instance _isGalois_quatH_detKer
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    IsGalois ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) := by
  haveI := _isGalois_rat_fixFld_quatH e
  exact IsGalois.tower_top_of_isGalois ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
    ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))

end JGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"

private theorem _ratOfE_prime {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (u : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))) :
    (LanglandsTunnell.P4.ratOfE u).Prime :=
  ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (u.under (𝓞 ℚ))).2

private theorem _under_eq_ratPrime_ratOfE {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (u : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))) :
    u.under (𝓞 ℚ) = ratPrime ⟨LanglandsTunnell.P4.ratOfE u, _ratOfE_prime e u⟩ := by
  rw [ratPrime]
  exact (Equiv.symm_apply_apply _ _).symm

private theorem _finite_setOf_ratOfE_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (ℓ : ℕ) :
    {u : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) |
      LanglandsTunnell.P4.ratOfE u = ℓ}.Finite := by
  by_cases hℓ : ℓ.Prime
  · haveI : Fact ℓ.Prime := ⟨hℓ⟩
    apply Set.Finite.of_finite_image
      (f := fun u : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) =>
        u.asIdeal)
      (hi := fun x _ y _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
    apply Set.Finite.subset
      (IsDedekindDomain.primesOver_finite (FrobeniusDensity.ratPrimeIdeal ℓ) _)
    rintro I ⟨u, hu, rfl⟩
    refine ⟨u.isPrime, ⟨?_⟩⟩
    rw [LanglandsTunnell.SeedAgreeRat.asIdeal_under_int_eq_of_under_eq (LanglandsTunnell.quatH e)
      (_ratOfE_prime e u) u (_under_eq_ratPrime_ratOfE e u), hu]
  · convert Set.finite_empty
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hℓ (h ▸ _ratOfE_prime e u)

private theorem _finite_setOf_ratOfE_mem {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (T : Finset ℕ) :
    {u : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) |
      LanglandsTunnell.P4.ratOfE u ∈ T}.Finite := by
  have hsub : {u : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) |
      LanglandsTunnell.P4.ratOfE u ∈ T} ⊆ ⋃ ℓ ∈ T, {u | LanglandsTunnell.P4.ratOfE u = ℓ} := by
    intro u hu
    simp only [Set.mem_iUnion]
    exact ⟨LanglandsTunnell.P4.ratOfE u, hu, rfl⟩
  exact Set.Finite.subset
    (Set.Finite.biUnion T.finite_toSet (fun ℓ _ => _finite_setOf_ratOfE_eq e ℓ)) hsub

private theorem _relDeg_conj {G : Type*} [Group G] [Finite G] (H : Subgroup G) [hH : H.Normal] (g σ : G) :
    LanglandsTunnell.P2.relDeg H (g * σ * g⁻¹) = LanglandsTunnell.P2.relDeg H σ := by
  apply Nat.dvd_antisymm
  · refine LanglandsTunnell.P4.relDeg_dvd_of_pow_mem H _ ?_
    rw [conj_pow]
    exact hH.conj_mem _ (LanglandsTunnell.P2.isRelDegree_relDeg H σ).2.1 g
  · refine LanglandsTunnell.P4.relDeg_dvd_of_pow_mem H _ ?_
    have h := hH.conj_mem _ (LanglandsTunnell.P2.isRelDegree_relDeg H (g * σ * g⁻¹)).2.1 g⁻¹
    rwa [conj_pow, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
      inv_mul_cancel, mul_one] at h

private theorem _seed_eq_of_under_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L)) [H.Normal]
    (w₁ w₂ : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld H)))
    (hQ : (LanglandsTunnell.P2.primeOver H w₁).under ℤ = (LanglandsTunnell.P2.primeOver H w₂).under ℤ) :
    (LanglandsTunnell.P2.liftTraceSeed e H).a w₁ = (LanglandsTunnell.P2.liftTraceSeed e H).a w₂ ∧
      (LanglandsTunnell.P2.liftTraceSeed e H).b w₁ = (LanglandsTunnell.P2.liftTraceSeed e H).b w₂ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_arithFrobAt (R := ℤ) (G := L ≃ₐ[ℚ] L)
    (Q := LanglandsTunnell.P2.primeOver H w₁) (LanglandsTunnell.P2.primeOver H w₂) hQ)
  have hsf : LanglandsTunnell.P2.seedFrob H w₂ = g * LanglandsTunnell.P2.seedFrob H w₁ * g⁻¹ := by
    unfold LanglandsTunnell.P2.seedFrob
    rw [← hg, _relDeg_conj, conj_pow]
  rw [LanglandsTunnell.P2.liftTraceSeed_a, LanglandsTunnell.P2.liftTraceSeed_a, LanglandsTunnell.P4.liftTraceSeed_b,
    LanglandsTunnell.P4.liftTraceSeed_b, hsf, map_mul, map_mul, map_inv, LanglandsTunnell.P4.trace_liftOf_conj,
    LanglandsTunnell.P4.det_liftOf_conj]
  exact ⟨rfl, rfl⟩

private theorem _isConstantOnFibers_of_agrees_seed_quatH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ₆ : HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) ℂ)
    (h₆ : Φ₆.AgreesAwayFromFinite
      ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo)) :
    Φ₆.IsConstantOnFibers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) := by
  obtain ⟨S, hS⟩ := h₆
  refine ⟨S, fun w₁ hw₁ w₂ hw₂ hunder _ => ?_⟩
  have hu : w₁.asIdeal.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
      = w₂.asIdeal.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) :=
    congrArg HeightOneSpectrum.asIdeal hunder
  have hQ : (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) w₁).under ℤ
      = (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) w₂).under ℤ := by
    rw [← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
        (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) w₁),
      LanglandsTunnell.P2.under_primeOver,
      ← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
        (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) w₂),
      LanglandsTunnell.P2.under_primeOver,
      ← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
        w₁.asIdeal,
      hu, Ideal.under_under]
  obtain ⟨ha, hb⟩ := _seed_eq_of_under_eq e (LanglandsTunnell.quatH e) w₁ w₂ hQ
  obtain ⟨ha₁, hb₁⟩ := hS w₁ hw₁
  obtain ⟨ha₂, hb₂⟩ := hS w₂ hw₂
  refine ⟨?_, ?_⟩
  · rw [ha₁, ha₂, AutomorphicForm.HeckeEigensystem.map_a, AutomorphicForm.HeckeEigensystem.map_a, ha]
  · rw [hb₁, hb₂, AutomorphicForm.HeckeEigensystem.map_b, AutomorphicForm.HeckeEigensystem.map_b, hb]

private theorem _det_eq_one_of_mem_K48 (M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))
    (hM : M ∈ LanglandsTunnell.Lift48.K48)
    (hred : (M.map FLT.ExplicitLift.red).det = 1) : M.det = 1 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hred
  rcases LanglandsTunnell.Lift48.K48_det_cases M hM with h | h
  · rwa [LanglandsTunnell.Lift48.det2_eq_det] at h
  · rw [LanglandsTunnell.Lift48.det2_eq_det] at h
    rw [h, map_neg, map_one] at hred
    exact absurd hred (by decide)

private theorem _pow_three_mem_P16det1 (M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))
    (hM : M ∈ LanglandsTunnell.Lift48.K48) (hdet : M.det = 1) :
    M ^ 3 ∈ LanglandsTunnell.H6Glue.P16det1 := by
  have hdet2 : LanglandsTunnell.Lift48.det2 M = 1 := by
    rw [LanglandsTunnell.Lift48.det2_eq_det]; exact hdet
  have hQ8sub : ∀ q ∈ LanglandsTunnell.Lift48.Q8, q ∈ LanglandsTunnell.H6Glue.P16det1 := by
    intro q hq
    have hq' := hq
    simp only [LanglandsTunnell.Lift48.Q8, List.mem_filter, decide_eq_true_eq] at hq'
    exact (LanglandsTunnell.H6Glue.mem_P16det1_iff q).2
      ⟨LanglandsTunnell.Lift48.Q8_sub_P16 q hq, hq'.2.1⟩
  rcases LanglandsTunnell.Lift48.K48_projOrder_cases M hM with h1 | h2 | h3 | h4
  · rcases (LanglandsTunnell.Lift48.isPM1_iff M).1 h1 with h | h <;> rw [h] <;> decide
  · have hq : M ∈ LanglandsTunnell.Lift48.Q8 := by
      simp only [LanglandsTunnell.Lift48.Q8, List.mem_filter, decide_eq_true_eq]
      exact ⟨hM, hdet2, (LanglandsTunnell.Lift48.K48_row_two_even M hM h2 hdet2).2⟩
    have h := (LanglandsTunnell.Lift48.Q8_mul_cube M hq).2
    rw [LanglandsTunnell.Lift48.pw_eq_pow] at h
    exact hQ8sub _ h
  · rcases ((LanglandsTunnell.Lift48.isProjOrder_iff 3 M).1 h3).1 with h | h <;> rw [h] <;> decide
  · exact absurd ((LanglandsTunnell.Lift48.K48_row_four M hM h4).1.symm.trans hdet2) (by decide)

private theorem _exists_place_over {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (v : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))) :
    ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))),
      𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) = v := by
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := 𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) v.asIdeal ⊥ (by simp)
  refine ⟨⟨Q, hQ, ?_⟩, ?_⟩
  · rintro rfl
    apply v.ne_bot
    rw [← hQv, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]
  · exact HeightOneSpectrum.ext hQv

private theorem _seed_detKer_b {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (v : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))) :
    (LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.detKer e)).b v = 1 := by
  rw [LanglandsTunnell.P4.liftTraceSeed_b]
  apply _det_eq_one_of_mem_K48 _
    ((LanglandsTunnell.Lift48.mem_closure_iff_mem_K48 _).1 (LanglandsTunnell.P4.liftOf_mem _))
  rw [LanglandsTunnell.P4.liftOf_red]
  exact (LanglandsTunnell.mem_detKer_iff e _).1 (LanglandsTunnell.P2.seedFrob_mem _ _)

private theorem _mem_quatH_of_pow_four {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {γ : L ≃ₐ[ℚ] L}
    (hγ : γ ∈ LanglandsTunnell.detKer e) (h4 : e γ ^ 4 = 1) : γ ∈ LanglandsTunnell.quatH e := by
  rw [_quatH_eq_galQ8 e]
  change e γ ∈ LanglandsTunnell.P5.OctB4.q8Sub
  rw [LanglandsTunnell.P5.OctB4.mem_q8Sub_iff']
  refine ⟨?_, h4⟩
  rw [LanglandsTunnell.detKer, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hγ
  exact MonoidHom.mem_ker.2 hγ

private theorem _pow_eq_one_of_liftOf (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {n : ℕ}
    (h : LanglandsTunnell.P2.liftOf g ^ n = 1) : g ^ n = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← LanglandsTunnell.P4.liftOf_red g,
    ← RingHom.mapMatrix_apply, ← map_pow, h, map_one]

private theorem _det_liftOf_eq_one {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {γ : L ≃ₐ[ℚ] L}
    (hγ : γ ∈ LanglandsTunnell.detKer e) : (LanglandsTunnell.P2.liftOf (e γ)).det = 1 := by
  apply _det_eq_one_of_mem_K48 _
    ((LanglandsTunnell.Lift48.mem_closure_iff_mem_K48 _).1 (LanglandsTunnell.P4.liftOf_mem _))
  rw [LanglandsTunnell.P4.liftOf_red]
  exact (LanglandsTunnell.mem_detKer_iff e _).1 hγ

private theorem _pow_relDeg_mul_three_mem_quatH {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (σ : L ≃ₐ[ℚ] L) :
    σ ^ (LanglandsTunnell.P2.relDeg (LanglandsTunnell.detKer e) σ * 3) ∈ LanglandsTunnell.quatH e := by
  have hmem : σ ^ LanglandsTunnell.P2.relDeg (LanglandsTunnell.detKer e) σ ∈ LanglandsTunnell.detKer e :=
    (LanglandsTunnell.P2.isRelDegree_relDeg (LanglandsTunnell.detKer e) σ).2.1
  rw [pow_mul]
  refine _mem_quatH_of_pow_four e (Subgroup.pow_mem _ hmem 3) ?_
  rw [map_pow, ← pow_mul]
  apply _pow_eq_one_of_liftOf
  have h3 := _pow_three_mem_P16det1 _
    ((LanglandsTunnell.Lift48.mem_closure_iff_mem_K48 _).1 (LanglandsTunnell.P4.liftOf_mem _))
    (_det_liftOf_eq_one e hmem)
  have h4 := _P16det1_pow_four _ h3
  rw [← pow_mul] at h4
  exact h4

private theorem _agrees_trans {F : Type} [Field F] [NumberField F] {R : Type*} [CommRing R]
    {Φ₁ Φ₂ Φ₃ : HeckeEigensystem F R} (h : Φ₁.AgreesAwayFromFinite Φ₂)
    (h' : Φ₂.AgreesAwayFromFinite Φ₃) : Φ₁.AgreesAwayFromFinite Φ₃ := by
  classical
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, hT⟩ := h'
  refine ⟨S ∪ T, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  exact ⟨(hS v hv.1).1.trans (hT v hv.2).1, (hS v hv.1).2.trans (hT v hv.2).2⟩

private theorem _agrees_map {F : Type} [Field F] [NumberField F]
    {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    {Φ₁ Φ₂ : HeckeEigensystem F R} (h : Φ₁.AgreesAwayFromFinite Φ₂) :
    (Φ₁.map f).AgreesAwayFromFinite (Φ₂.map f) := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨congrArg f (hS v hv).1, congrArg f (hS v hv).2⟩⟩

private theorem _seed_quatH_b {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))) :
    (LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).b 𝔓 = 1 := by
  rw [LanglandsTunnell.P4.liftTraceSeed_b]
  apply _det_eq_one_of_mem_K48 _
    ((LanglandsTunnell.Lift48.mem_closure_iff_mem_K48 _).1 (LanglandsTunnell.P4.liftOf_mem _))
  rw [LanglandsTunnell.P4.liftOf_red]
  exact (LanglandsTunnell.mem_detKer_iff e _).1
    (LanglandsTunnell.quatH_le_detKer e (LanglandsTunnell.P2.seedFrob_mem _ _))

private theorem _b_cube_of_agrees_seed_quatH {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ₂₀ : HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) ℂ)
    (hBC : AgreesAwayFromFinite
      (formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) Φ₂₀)
      ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))),
      ∀ v ∉ S, Φ₂₀.b v ^ 3 = 1 := by
  classical
  obtain ⟨S₂, hS₂⟩ := hBC
  refine ⟨S₂.image (fun 𝔓 => 𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))))
      ∪ (_finite_setOf_ratOfE_mem e (LanglandsTunnell.P0.towerBadPrimes L)).toFinset.image
          (fun 𝔓 => 𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))),
    fun v hv => ?_⟩
  simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hv
  obtain ⟨hv₂, hv₄⟩ := hv
  obtain ⟨𝔓, h𝔓v⟩ := _exists_place_over e v
  have h𝔓 : 𝔓 ∉ (_finite_setOf_ratOfE_mem e (LanglandsTunnell.P0.towerBadPrimes L)).toFinset :=
    fun h => hv₄ 𝔓 h h𝔓v

  have hBCb := (hS₂ 𝔓 (fun h => hv₂ 𝔓 h h𝔓v)).2
  rw [formalBaseChange_b, AutomorphicForm.HeckeEigensystem.map_b, _seed_quatH_b, map_one, h𝔓v] at hBCb

  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h𝔓
  have hℓ : (LanglandsTunnell.P4.ratOfE 𝔓).Prime := _ratOfE_prime e 𝔓
  haveI hQℓ := LanglandsTunnell.SeedAgreeRat.primeOver_liesOver_ratPrimeIdeal
    (LanglandsTunnell.quatH e) hℓ 𝔓 (_under_eq_ratPrime_ratOfE e 𝔓)
  have hI : (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓).inertia (L ≃ₐ[ℚ] L) = ⊥ :=
    LanglandsTunnell.P0.tower_inertia_eq_bot_of_notMem hℓ h𝔓 _
  have hle : LanglandsTunnell.quatH e ≤ LanglandsTunnell.detKer e := inf_le_right
  have hw' : 𝔓.asIdeal = (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓).under
      (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) :=
    (LanglandsTunnell.P2.under_primeOver (LanglandsTunnell.quatH e) 𝔓).symm
  have hw : (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal
      = (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓).under
          (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) := by
    show 𝔓.asIdeal.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) = _
    rw [hw', Ideal.under_under]
  have h1 := LanglandsTunnell.P4.inertiaDeg_eq_inertiaDeg_mul hle hℓ _ hI _ hw 𝔓 hw'
  have h2 := LanglandsTunnell.P4.inertiaDeg_under_mul ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
    ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) 𝔓
  have h3 := LanglandsTunnell.P4.under_under ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
    ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) 𝔓
  have hrel := LanglandsTunnell.P4.inertiaDeg_eq_relDeg (LanglandsTunnell.detKer e) hℓ _ hI _ hw
  rw [h3] at h1 hrel
  have hpos : 0 < (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg'
      (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal := by
    rw [hrel]
    exact LanglandsTunnell.P4.relDeg_pos _ _
  have hk := Nat.eq_of_mul_eq_mul_left hpos (h2.symm.trans h1)
  rw [h𝔓v] at hk
  set n := LanglandsTunnell.P2.relDeg (LanglandsTunnell.detKer e)
    (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓)) with hn
  set m := LanglandsTunnell.P2.relDeg (LanglandsTunnell.quatH e)
    (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓)) with hm
  have hnpos : 0 < n := LanglandsTunnell.P4.relDeg_pos _ _
  have hdvd : n ∣ m := LanglandsTunnell.P4.relDeg_dvd_relDeg (LanglandsTunnell.quatH_le_detKer e) _
  have hkn : m / n * n = m := Nat.div_mul_cancel hdvd
  have hm3 : m ∣ n * 3 := LanglandsTunnell.P4.relDeg_dvd_of_pow_mem _ _ (_pow_relDeg_mul_three_mem_quatH e _)
  have hk3 : m / n ∣ 3 := by
    have : m / n * n ∣ 3 * n := by rw [hkn, mul_comm]; exact hm3
    exact Nat.dvd_of_mul_dvd_mul_right hnpos this
  rw [hk] at hBCb
  rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hk3) with h1 | h3
  ·
    rw [h1, pow_one] at hBCb
    simp [hBCb]
  ·
    rw [h3] at hBCb
    exact hBCb

private theorem _satakePow_smul (c s t : ℂ) (n : ℕ) :
    AutomorphicForm.satakePow n (c * s) (c ^ 2 * t) = c ^ n * AutomorphicForm.satakePow n s t ∧
      AutomorphicForm.satakePow (n + 1) (c * s) (c ^ 2 * t)
        = c ^ (n + 1) * AutomorphicForm.satakePow (n + 1) s t := by
  induction n with
  | zero =>
    exact ⟨by simp [AutomorphicForm.satakePow_zero], by simp [AutomorphicForm.satakePow_one]⟩
  | succ n ih =>
    obtain ⟨h₀, h₁⟩ := ih
    refine ⟨h₁, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, AutomorphicForm.satakePow_add_two,
      AutomorphicForm.satakePow_add_two, h₀, h₁]
    ring

private theorem _finite_setOf_under_eq {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (v : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))) :
    {𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) |
      𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) = v}.Finite := by
  apply Set.Finite.of_finite_image
    (f := fun 𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) => 𝔓.asIdeal)
    (hi := fun x _ y _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
  apply Set.Finite.subset
    (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))))
  rintro I ⟨𝔓, h𝔓, rfl⟩
  exact ⟨𝔓.isPrime, ⟨(congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h𝔓).symm⟩⟩

private theorem _finite_setOf_under_mem {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))))) :
    {𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) |
      𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) ∈ S}.Finite := by
  have hsub : {𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) |
      𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) ∈ S} ⊆
      ⋃ v ∈ S, {𝔓 | 𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) = v} := by
    intro 𝔓 h𝔓
    simp only [Set.mem_iUnion]
    exact ⟨_, h𝔓, rfl⟩
  exact Set.Finite.subset
    (Set.Finite.biUnion S.finite_toSet (fun v _ => _finite_setOf_under_eq e v)) hsub

private theorem _selection {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ₂₀ Φ' : HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) ℂ)
    (c : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) → ℂ)
    (hBC : AgreesAwayFromFinite
      (formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) Φ₂₀)
      ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo))
    (hc : ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))),
      ∀ v ∉ S, c v = Φ₂₀.b v)
    (htw : ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))),
      ∀ v ∉ S, Φ'.a v = c v * Φ₂₀.a v ∧ Φ'.b v = c v ^ 2 * Φ₂₀.b v) :
    (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))),
        ∀ v ∉ S, Φ'.b v =
          ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.detKer e)).map iotaZsqrtdNegTwo).b v) ∧
      (formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) Φ').AgreesAwayFromFinite
        ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo) := by
  classical
  obtain ⟨S₃, hS₃⟩ := _b_cube_of_agrees_seed_quatH e Φ₂₀ hBC
  obtain ⟨Sc, hSc⟩ := hc
  obtain ⟨St, hSt⟩ := htw

  have hloc : ∀ v, v ∉ S₃ ∪ Sc ∪ St →
      Φ'.a v = Φ₂₀.b v * Φ₂₀.a v ∧ Φ'.b v = Φ₂₀.b v ^ 2 * Φ₂₀.b v ∧ Φ₂₀.b v ^ 3 = 1 := by
    intro v hv
    have hv₃ : v ∉ S₃ := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hvc : v ∉ Sc := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvt : v ∉ St := fun h => hv (Finset.mem_union_right _ h)
    obtain ⟨ha, hb⟩ := hSt v hvt
    rw [hSc v hvc] at ha hb
    exact ⟨ha, hb, hS₃ v hv₃⟩
  refine ⟨⟨S₃ ∪ Sc ∪ St, fun v hv => ?_⟩, ?_⟩
  ·
    obtain ⟨-, hb, h3⟩ := hloc v hv
    rw [hb, AutomorphicForm.HeckeEigensystem.map_b, _seed_detKer_b, map_one]
    linear_combination h3
  ·
    obtain ⟨S₂, hS₂⟩ := hBC
    refine ⟨S₂ ∪ (_finite_setOf_under_mem e (S₃ ∪ Sc ∪ St)).toFinset, fun 𝔓 h𝔓 => ?_⟩
    have h𝔓₂ : 𝔓 ∉ S₂ := fun h => h𝔓 (Finset.mem_union_left _ h)
    have h𝔓T : 𝔓 ∉ (_finite_setOf_under_mem e (S₃ ∪ Sc ∪ St)).toFinset :=
      fun h => h𝔓 (Finset.mem_union_right _ h)
    have h𝔓v : 𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) ∉ S₃ ∪ Sc ∪ St := by
      intro h
      apply h𝔓T
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact h
    obtain ⟨ha, hb, -⟩ := hloc _ h𝔓v
    obtain ⟨hBCa, hBCb⟩ := hS₂ 𝔓 h𝔓₂

    have hbf := hBCb
    rw [formalBaseChange_b, AutomorphicForm.HeckeEigensystem.map_b, _seed_quatH_b, map_one] at hbf
    rw [formalBaseChange_a] at hBCa
    refine ⟨?_, ?_⟩
    · rw [formalBaseChange_a, ha, hb]
      have hsm := (_satakePow_smul
        (Φ₂₀.b (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))))
        (Φ₂₀.a (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))))
        (Φ₂₀.b (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))))
        ((𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal.inertiaDeg'
          𝔓.asIdeal)).1
      rw [hsm, hbf, one_mul]
      exact hBCa
    · rw [formalBaseChange_b, hb, AutomorphicForm.HeckeEigensystem.map_b, _seed_quatH_b, map_one]
      have h33 : (Φ₂₀.b (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))) ^ 2 *
            Φ₂₀.b (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))))) ^
            ((𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal.inertiaDeg'
              𝔓.asIdeal)
          = (Φ₂₀.b (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))) ^
            ((𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal.inertiaDeg'
              𝔓.asIdeal)) ^ 3 := by ring
      rw [h33, hbf, one_pow]

private theorem _agrees_trans' {F : Type} [Field F] [NumberField F] {R : Type*} [CommRing R]
    {Φ₁ Φ₂ Φ₃ : HeckeEigensystem F R} (h : Φ₁.AgreesAwayFromFinite Φ₂)
    (h' : Φ₂.AgreesAwayFromFinite Φ₃) : Φ₁.AgreesAwayFromFinite Φ₃ := by
  classical
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, hT⟩ := h'
  refine ⟨S ∪ T, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  exact ⟨(hS v hv.1).1.trans (hT v hv.2).1, (hS v hv.1).2.trans (hT v hv.2).2⟩

private theorem _agrees_symm' {F : Type} [Field F] [NumberField F] {R : Type*} [CommRing R]
    {Φ₁ Φ₂ : HeckeEigensystem F R} (h : Φ₁.AgreesAwayFromFinite Φ₂) : Φ₂.AgreesAwayFromFinite Φ₁ := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1.symm, (hS v hv).2.symm⟩⟩

private theorem _sigma_transport (K : Type) [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (Φ : HeckeEigensystem K ℂ) (hΦ : IsArithBoundedGenuineCuspRealizable K (_pinsAt K (_win K c u d₁ d₂ T)) (StandardAddChar.stdAddChar K) Φ) :
    ∃ Φ' : HeckeEigensystem K ℂ,
      IsArithBoundedGenuineCuspRealizable K (_pinsAt K (_win K c u d₁ d₂ T)) (StandardAddChar.stdAddChar K) Φ' ∧
      ∀ v w : HeightOneSpectrum (𝓞 K),
        w.asIdeal = v.asIdeal.comap (galRestrict ℤ ℚ K (𝓞 K) σ) → Φ'.a w = Φ.a v ∧ Φ'.b w = Φ.b v :=
  AutomorphicForm.exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict K σ c u d₁ d₂ T hc hd₁ hd Φ hΦ

private theorem _cubic_fibre (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (hdeg : Module.finrank K M = 3)
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (cM uM d₁M d₂M : ℝ) (TM : Finset (AdelicGL2 (𝓞 M) M))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : SiegelCovering.CoversModCentre K (_win K cK uK d₁K d₂K TK))
    (hdM : d₁M < d₂M)
    (hcovM : SiegelCovering.CoversModCentre M (_win M cM uM d₁M d₂M TM))
    (Φc Φc' : HeckeEigensystem K ℂ) (ΦM : HeckeEigensystem M ℂ)
    (hΦc : IsArithBoundedGenuineCuspRealizable K (_pinsAt K (_win K cK uK d₁K d₂K TK)) (StandardAddChar.stdAddChar K) Φc)
    (hΦc' : IsArithBoundedGenuineCuspRealizable K (_pinsAt K (_win K cK uK d₁K d₂K TK)) (StandardAddChar.stdAddChar K) Φc')
    (hΦM : IsArithBoundedGenuineCuspRealizable M (_pinsAt M (_win M cM uM d₁M d₂M TM)) (StandardAddChar.stdAddChar M) ΦM)
    (hBC : (formalBaseChange K M Φc).AgreesAwayFromFinite ΦM)
    (hBC' : (formalBaseChange K M Φc').AgreesAwayFromFinite ΦM) :
    ∃ χ : (M ≃ₐ[K] M) →* ℂˣ,
      (∃ S : Finset (HeightOneSpectrum (𝓞 K)),
        ∀ v ∉ S,
          (Φc'.a v = (χ (LanglandsTunnell.P2.Artin.artinFrob K M v) : ℂ) * Φc.a v ∧
            Φc'.b v = (χ (LanglandsTunnell.P2.Artin.artinFrob K M v) : ℂ) ^ 2 * Φc.b v)) :=
  AutomorphicForm.HeckeEigensystem.exists_char_twist_artinFrob_of_formalBaseChange_agreesAwayFromFinite_of_finrank_eq_three_of_coversModCentre_of_pos K M hdeg cK uK d₁K d₂K TK cM uM d₁M d₂M TM hcK hd₁K hdK hcovK hdM hcovM Φc Φc' ΦM hΦc hΦc' hΦM hBC hBC'

private theorem _inertiaDeg_eq_relDeg_div {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (𝔓 : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hQℚ : 𝔓.under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨ℓ, hℓ⟩)
    (hbad : ℓ ∉ LanglandsTunnell.P0.towerBadPrimes L) :
    (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal.inertiaDeg' 𝔓.asIdeal
      = LanglandsTunnell.P2.relDeg (LanglandsTunnell.quatH e)
          (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓))
        / LanglandsTunnell.P2.relDeg (LanglandsTunnell.detKer e)
          (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓)) := by
  haveI hQℓ := LanglandsTunnell.SeedAgreeRat.primeOver_liesOver_ratPrimeIdeal (LanglandsTunnell.quatH e) hℓ 𝔓 hQℚ
  have hI : (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓).inertia (L ≃ₐ[ℚ] L) = ⊥ :=
    LanglandsTunnell.P0.tower_inertia_eq_bot_of_notMem hℓ hbad _
  have hle : LanglandsTunnell.quatH e ≤ LanglandsTunnell.detKer e := inf_le_right
  have hw' : 𝔓.asIdeal = (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓).under
      (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) :=
    (LanglandsTunnell.P2.under_primeOver (LanglandsTunnell.quatH e) 𝔓).symm
  have hw : (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal
      = (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓).under
          (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) := by
    show 𝔓.asIdeal.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) = _
    rw [hw', Ideal.under_under]
  have h1 := LanglandsTunnell.P4.inertiaDeg_eq_inertiaDeg_mul hle hℓ _ hI _ hw 𝔓 hw'
  have h2 := LanglandsTunnell.P4.inertiaDeg_under_mul ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
    ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) 𝔓
  have h3 := LanglandsTunnell.P4.under_under ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
    ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) 𝔓
  have hrel := LanglandsTunnell.P4.inertiaDeg_eq_relDeg (LanglandsTunnell.detKer e) hℓ _ hI _ hw
  rw [h3] at h1 hrel
  have hpos : 0 < (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg'
      (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal := by
    rw [hrel]
    exact LanglandsTunnell.P4.relDeg_pos _ _
  have hk := Nat.eq_of_mul_eq_mul_left hpos (h2.symm.trans h1)
  exact hk

private theorem _bc_of_conj {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (σ : ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) ≃ₐ[ℚ]
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
    (Φ Φ' : HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) ℂ)
    (hBC : (formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) Φ).AgreesAwayFromFinite
      ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo))
    (hconj : ∀ v w : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))),
      w.asIdeal = v.asIdeal.comap (galRestrict ℤ ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) σ) → Φ'.a w = Φ.a v ∧ Φ'.b w = Φ.b v) :
    (formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) Φ').AgreesAwayFromFinite
      ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo) := by
  classical
  obtain ⟨S₂, hS₂⟩ := hBC

  let vOf : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) →
      HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) :=
    fun w => HeightOneSpectrum.comap
      ((galRestrict ℤ ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) σ).symm :
          𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) →+*
            𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
      (galRestrict ℤ ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) σ).symm.surjective w
  have hvw : ∀ w, w.asIdeal = (vOf w).asIdeal.comap
      (galRestrict ℤ ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) σ) := by
    intro w
    ext x
    simp [vOf, Ideal.mem_comap]
  have hinj : Function.Injective vOf := fun w₁ w₂ h => by
    apply HeightOneSpectrum.ext
    rw [hvw w₁, hvw w₂, h]

  have hfix : ∀ x : 𝓞 ℚ,
      galRestrict ℤ ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
          (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) σ
        (algebraMap (𝓞 ℚ) (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) x)
      = algebraMap (𝓞 ℚ) (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) x := by
    intro x
    have h : algebraMap (𝓞 ℚ) (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
          (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x))
        = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) :=
      RingHom.congr_fun (Subsingleton.elim
        ((algebraMap (𝓞 ℚ) (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).comp
          (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ))
        (Int.castRingHom (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))))) (Rat.ringOfIntegersEquiv x)
    rw [RingEquiv.symm_apply_apply] at h
    rw [h]
    exact map_intCast _ _
  have hunder : ∀ w, (vOf w).under (𝓞 ℚ) = w.under (𝓞 ℚ) := by
    intro w
    apply HeightOneSpectrum.ext
    show (vOf w).asIdeal.comap (algebraMap (𝓞 ℚ) _) = w.asIdeal.comap (algebraMap (𝓞 ℚ) _)
    conv_rhs => rw [hvw w]
    ext x
    simp only [Ideal.mem_comap]
    rw [hfix x]

  have hWfin : (vOf ⁻¹' ↑(S₂.image
      (fun 𝔔 => 𝔔.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))))).Finite :=
    Set.Finite.preimage hinj.injOn (Finset.finite_toSet _)
  refine ⟨(_finite_setOf_under_mem e hWfin.toFinset).toFinset
      ∪ (_finite_setOf_ratOfE_mem e (LanglandsTunnell.P0.towerBadPrimes L)).toFinset, fun 𝔓 h𝔓 => ?_⟩
  have h𝔓W : 𝔓 ∉ (_finite_setOf_under_mem e hWfin.toFinset).toFinset :=
    fun h => h𝔓 (Finset.mem_union_left _ h)
  have h𝔓bad : LanglandsTunnell.P4.ratOfE 𝔓 ∉ LanglandsTunnell.P0.towerBadPrimes L := by
    intro h
    apply h𝔓
    apply Finset.mem_union_right
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact h
  have hvX : vOf (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))) ∉ S₂.image
      (fun 𝔔 => 𝔔.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))) := by
    intro h
    apply h𝔓W
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe]
    exact h

  obtain ⟨𝔔, h𝔔⟩ := _exists_place_over e (vOf (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))))
  have h𝔔S : 𝔔 ∉ S₂ := fun h => hvX (Finset.mem_image.2 ⟨𝔔, h, h𝔔⟩)
  obtain ⟨hQa, hQb⟩ := hS₂ 𝔔 h𝔔S
  rw [formalBaseChange_a, h𝔔] at hQa
  rw [formalBaseChange_b, h𝔔] at hQb

  have hℓ := _ratOfE_prime e 𝔓
  have h𝔓ℚ := _under_eq_ratPrime_ratOfE e 𝔓
  have h𝔔ℚ : 𝔔.under (𝓞 ℚ) = AutomorphicForm.ratPrime ⟨LanglandsTunnell.P4.ratOfE 𝔓, hℓ⟩ := by
    rw [← LanglandsTunnell.P4.under_under ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) 𝔔, h𝔔, hunder,
      LanglandsTunnell.P4.under_under ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) 𝔓]
    exact h𝔓ℚ
  have hQ𝔓 := LanglandsTunnell.SeedAgreeRat.primeOver_liesOver_ratPrimeIdeal (LanglandsTunnell.quatH e) hℓ 𝔓 h𝔓ℚ
  have hQ𝔔 := LanglandsTunnell.SeedAgreeRat.primeOver_liesOver_ratPrimeIdeal (LanglandsTunnell.quatH e) hℓ 𝔔 h𝔔ℚ
  have hQ : (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔔).under ℤ
      = (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓).under ℤ := hQ𝔔.over.symm.trans hQ𝔓.over

  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_arithFrobAt (R := ℤ) (G := L ≃ₐ[ℚ] L)
    (Q := LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔔)
    (LanglandsTunnell.P2.primeOver (LanglandsTunnell.quatH e) 𝔓) hQ)
  have hf : (vOf (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))))).asIdeal.inertiaDeg' 𝔔.asIdeal
      = (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))).asIdeal.inertiaDeg' 𝔓.asIdeal := by
    have h₁ := _inertiaDeg_eq_relDeg_div e 𝔔 hℓ h𝔔ℚ h𝔓bad
    have h₂ := _inertiaDeg_eq_relDeg_div e 𝔓 hℓ h𝔓ℚ h𝔓bad
    rw [h𝔔] at h₁
    rw [h₁, h₂, ← hc, _relDeg_conj, _relDeg_conj]
  obtain ⟨ha', hb'⟩ := hconj _ _ (hvw (𝔓.under (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))))
  have hseed := _seed_eq_of_under_eq e (LanglandsTunnell.quatH e) 𝔔 𝔓 hQ
  refine ⟨?_, ?_⟩
  · rw [formalBaseChange_a, ha', hb', ← hf, hQa, AutomorphicForm.HeckeEigensystem.map_a,
      AutomorphicForm.HeckeEigensystem.map_a, hseed.1]
  · rw [formalBaseChange_b, hb', ← hf, hQb, AutomorphicForm.HeckeEigensystem.map_b,
      AutomorphicForm.HeckeEigensystem.map_b, hseed.2]

private theorem _isGalois_rat_fixFld_detKer {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    IsGalois ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) := by
  rw [_detKer_eq_galSL e]
  exact LanglandsTunnell.P5.OctB4.isGalois_fldE e

private theorem _isConstantOnFibers_descended {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (c₂ u₂ d₂₁ d₂₂ : ℝ)
    (T₂ : Finset (AdelicGL2 (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))))
    (hc₂ : 0 < c₂) (hd₂₁ : 0 < d₂₁) (hd₂ : d₂₁ < d₂₂)
    (hcov₂ : SiegelCovering.CoversModCentre ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      (_win ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) c₂ u₂ d₂₁ d₂₂ T₂))
    (c₆ u₆ d₆₁ d₆₂ : ℝ)
    (T₆ : Finset (AdelicGL2 (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))))
    (hd₆ : d₆₁ < d₆₂)
    (hcov₆ : SiegelCovering.CoversModCentre ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      (_win ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) c₆ u₆ d₆₁ d₆₂ T₆))
    (Φ₆ : HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) ℂ)
    (hΦ₆ : IsArithBoundedGenuineCuspRealizable ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      (_pinsAt ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
        (_win ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) c₆ u₆ d₆₁ d₆₂ T₆))
      (StandardAddChar.stdAddChar ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) Φ₆)
    (h₆ : Φ₆.AgreesAwayFromFinite
      ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo))
    (Φ : HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) ℂ)
    (hΦ : IsArithBoundedGenuineCuspRealizable ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      (_pinsAt ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        (_win ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) c₂ u₂ d₂₁ d₂₂ T₂))
      (StandardAddChar.stdAddChar ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) Φ)
    (hBC : (formalBaseChange ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) Φ).AgreesAwayFromFinite
      ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.quatH e)).map iotaZsqrtdNegTwo))
    (hb : ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))),
      ∀ v ∉ S, Φ.b v =
        ((LanglandsTunnell.P2.liftTraceSeed e (LanglandsTunnell.detKer e)).map iotaZsqrtdNegTwo).b v) :
    Φ.IsConstantOnFibers ℚ := by
  classical
  haveI := _isGalois_rat_fixFld_detKer e
  obtain ⟨Sb, hSb⟩ := hb
  have hb1 : ∀ v ∉ Sb, Φ.b v = 1 := fun v hv => by
    rw [hSb v hv, AutomorphicForm.HeckeEigensystem.map_b, _seed_detKer_b, map_one]

  have key : ∀ σ : ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) ≃ₐ[ℚ]
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)),
      ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))),
        ∀ v w : HeightOneSpectrum (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))),
          w ∉ S → v ∉ S →
          w.asIdeal = v.asIdeal.comap (galRestrict ℤ ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
            (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))) σ) →
          Φ.a w = Φ.a v ∧ Φ.b w = Φ.b v := by
    intro σ
    obtain ⟨Φ', hΦ', hconj⟩ :=
      _sigma_transport ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) σ c₂ u₂ d₂₁ d₂₂ T₂ hc₂ hd₂₁ hd₂ Φ hΦ
    have hBC' := _bc_of_conj e σ Φ Φ' hBC hconj
    obtain ⟨χ, Sχ, hχ⟩ := _cubic_fibre ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) (_finrank_quatH_detKer e)
      c₂ u₂ d₂₁ d₂₂ T₂ c₆ u₆ d₆₁ d₆₂ T₆ hc₂ hd₂₁ hd₂ hcov₂ hd₆ hcov₆ Φ Φ' Φ₆ hΦ hΦ' hΦ₆
      (_agrees_trans' hBC (_agrees_symm' h₆)) (_agrees_trans' hBC' (_agrees_symm' h₆))
    refine ⟨Sχ ∪ Sb, fun v w hw hv hvw => ?_⟩
    have hwχ : w ∉ Sχ := fun h => hw (Finset.mem_union_left _ h)
    have hwb : w ∉ Sb := fun h => hw (Finset.mem_union_right _ h)
    have hvb : v ∉ Sb := fun h => hv (Finset.mem_union_right _ h)
    obtain ⟨ha', hb'⟩ := hconj v w hvw
    obtain ⟨hχa, hχb⟩ := hχ w hwχ
    have hbw := hb1 w hwb
    have hbv := hb1 v hvb

    have hcard : Nat.card (↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) ≃ₐ[
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))]
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))) = 3 := by
      rw [IsGalois.card_aut_eq_finrank]
      exact _finrank_quatH_detKer e
    have hg : LanglandsTunnell.P2.Artin.artinFrob ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) w ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := LanglandsTunnell.P2.Artin.artinFrob
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)) ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) w)
      rwa [hcard] at h
    have hχ3 : ((χ (LanglandsTunnell.P2.Artin.artinFrob ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) w) : ℂˣ) : ℂ) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one]

    have hχ2 : ((χ (LanglandsTunnell.P2.Artin.artinFrob ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) w) : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [hbw, mul_one] at hχb
      rw [← hχb, hb', hbv]
    have hχ1 : ((χ (LanglandsTunnell.P2.Artin.artinFrob ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) w) : ℂˣ) : ℂ) = 1 := by
      linear_combination hχ3 - (χ (LanglandsTunnell.P2.Artin.artinFrob
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
        ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) w) : ℂ) * hχ2
    constructor
    · linear_combination ha' - hχa - Φ.a w * hχ1
    · rw [hbw, hbv]

  choose S hS using key
  refine ⟨Finset.univ.biUnion S, fun w₁ hw₁ w₂ hw₂ hunder _ => ?_⟩
  have hZ : w₁.asIdeal.under ℤ = w₂.asIdeal.under ℤ := by
    have h : w₁.asIdeal.under (𝓞 ℚ) = w₂.asIdeal.under (𝓞 ℚ) := congrArg HeightOneSpectrum.asIdeal hunder
    have h₁ : (w₁.asIdeal.under (𝓞 ℚ)).under ℤ = w₁.asIdeal.under ℤ := by rw [Ideal.under_under]
    have h₂ : (w₂.asIdeal.under (𝓞 ℚ)).under ℤ = w₂.asIdeal.under ℤ := by rw [Ideal.under_under]
    rw [← h₁, h, h₂]
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq ℤ ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e))
    (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.detKer e)))
    (p := w₁.asIdeal.under ℤ) ⟨w₁.isPrime, ⟨rfl⟩⟩ ⟨w₂.isPrime, ⟨hZ⟩⟩
  have h₁ : w₁ ∉ S σ := fun h => hw₁ (Finset.mem_biUnion.2 ⟨σ, Finset.mem_univ _, h⟩)
  have h₂ : w₂ ∉ S σ := fun h => hw₂ (Finset.mem_biUnion.2 ⟨σ, Finset.mem_univ _, h⟩)
  obtain ⟨ha, hb⟩ := hS σ w₁ w₂ h₂ h₁ hσ.symm
  exact ⟨ha.symm, hb.symm⟩

end LanglandsTunnell.CyclicCubicAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.CyclicCubicAssembly"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P5.OctB4 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell.P4"

open IsDedekindDomain NumberField MeasureTheory Matrix in
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox in
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering in
open NumberField.SiegelVolume in
open HeckeIntegralSeam in
private theorem _twist_by_character
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂)
    (Φ : HeckeEigensystem F ℂ)
    (hΦ :
      IsArithBoundedGenuineCuspRealizable F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
          (NumberField.StandardAddChar.stdAddChar F) Φ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (𝔣 : Ideal (𝓞 F)) (hmod : HeckeCharacter.AdmitsModulus F η 𝔣) :
    ∃ Φ' : HeckeEigensystem F ℂ, ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ v ∉ S,
        Φ'.a v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) * Φ.a v ∧
        Φ'.b v = ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) ^ 2 * Φ.b v) ∧
      IsArithBoundedGenuineCuspRealizable F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
          (NumberField.StandardAddChar.stdAddChar F) Φ' :=
  LanglandsTunnell.exists_isArithBoundedGenuineCuspRealizable_twist_centreCut F c u d₁ d₂ T hc hd₁ hd Φ hΦ η hη 𝔣 hmod

open NumberField NumberField.AdelicLevel NumberField.AdelicBox in
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering in
private theorem _cyclic_descent
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3)
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (hdL : d₁L < d₂L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (ΦL : HeckeEigensystem L ℂ)
    (hΦL : IsArithBoundedGenuineCuspRealizable L
      (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)) (NumberField.StandardAddChar.stdAddChar L) ΦL)
    (hinv : ΦL.IsConstantOnFibers K) :
    ∃ Φ : HeckeEigensystem K ℂ,
      IsArithBoundedGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) Φ ∧
      HeckeEigensystem.AgreesAwayFromFinite (formalBaseChange K L Φ) ΦL :=
  AutomorphicForm.exists_isArithBoundedGenuineCuspRealizable_formalBaseChange_of_isConstantOnFibers_of_finrank_two_or_three_of_coversModCentre
    K L hdeg cK uK d₁K d₂K TK cL uL d₁L d₂L TL hcK hd₁K hdK hcovK hdL hcovL ΦL hΦL.isArithGenuineCuspRealizable hinv

open LanglandsTunnell.CyclicCubicAssembly _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH.LanglandsTunnell IsDedekindDomain MeasureTheory Matrix in
open NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering in
open NumberField.SiegelVolume in
theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (c₆ u₆ d₆₁ d₆₂ : ℝ) (T₆ : Finset (AdelicGL2 (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e))))
    (c₂ u₂ d₂₁ d₂₂ : ℝ) (T₂ : Finset (AdelicGL2 (𝓞 ↥(fixFld (detKer e))) ↥(fixFld (detKer e))))
    (Φ₆ : HeckeEigensystem ↥(fixFld (quatH e)) (Zsqrtd (-2)))
    (h₆ : Φ₆.AgreesAwayFromFinite (P2.liftTraceSeed e (quatH e)))
    (hc₆ : IsArithBoundedGenuineCuspRealizableVia ↥(fixFld (quatH e))
      (productionPinsOf ↥(fixFld (quatH e))
        (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂)
        (fun N => levelOne (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) N ⊓
          finiteAdelicGL2Subgroup ↥(fixFld (quatH e)))
        (fun v => heckeGen (𝓞 ↥(fixFld (quatH e))) ↥(fixFld (quatH e)) v) (adelicBox ↥(fixFld (quatH e))))
      (StandardAddChar.stdAddChar ↥(fixFld (quatH e))) iotaZsqrtdNegTwo Φ₆)
    (hd₆ : d₆₁ < d₆₂)
    (hcov₆ : CoversModCentre ↥(fixFld (quatH e))
      (⋃ x ∈ T₆, (· * x) '' centreCutSiegelSet ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂))
    (hc₂ : 0 < c₂) (hd₂₁ : 0 < d₂₁) (hd₂ : d₂₁ < d₂₂)
    (hcov₂ : CoversModCentre ↥(fixFld (detKer e))
      (⋃ x ∈ T₂, (· * x) '' centreCutSiegelSet ↥(fixFld (detKer e)) c₂ u₂ d₂₁ d₂₂)) :
    ∃ Φ₂ : HeckeEigensystem ↥(fixFld (detKer e)) ℂ,
      IsArithBoundedGenuineCuspRealizable ↥(fixFld (detKer e))
        (productionPinsOf ↥(fixFld (detKer e))
          (⋃ x ∈ T₂, (· * x) '' centreCutSiegelSet ↥(fixFld (detKer e)) c₂ u₂ d₂₁ d₂₂)
          (fun N => levelOne (𝓞 ↥(fixFld (detKer e))) ↥(fixFld (detKer e)) N ⊓
            finiteAdelicGL2Subgroup ↥(fixFld (detKer e)))
          (fun v => heckeGen (𝓞 ↥(fixFld (detKer e))) ↥(fixFld (detKer e)) v) (adelicBox ↥(fixFld (detKer e))))
        (StandardAddChar.stdAddChar ↥(fixFld (detKer e))) Φ₂ ∧
      Φ₂.IsConstantOnFibers ℚ ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (detKer e)))), ∀ v ∉ S,
        Φ₂.b v = ((P2.liftTraceSeed e (detKer e)).map iotaZsqrtdNegTwo).b v) ∧
      (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) Φ₂).AgreesAwayFromFinite
        ((P2.liftTraceSeed e (quatH e)).map iotaZsqrtdNegTwo) := by
  classical
  have hc₆ℂ : IsArithBoundedGenuineCuspRealizable ↥(fixFld (quatH e))
      (_pinsAt ↥(fixFld (quatH e)) (_win ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂ T₆)) (StandardAddChar.stdAddChar ↥(fixFld (quatH e)))
      (Φ₆.map iotaZsqrtdNegTwo) :=
    _complex_of_via_bounded (_pinsAt ↥(fixFld (quatH e)) (_win ↥(fixFld (quatH e)) c₆ u₆ d₆₁ d₆₂ T₆)) Φ₆ hc₆
  have h₆ℂ : (Φ₆.map iotaZsqrtdNegTwo).AgreesAwayFromFinite
      ((P2.liftTraceSeed e (quatH e)).map iotaZsqrtdNegTwo) := _agrees_map iotaZsqrtdNegTwo h₆
  have hfc : (Φ₆.map iotaZsqrtdNegTwo).IsConstantOnFibers ↥(fixFld (detKer e)) :=
    _isConstantOnFibers_of_agrees_seed_quatH e (Φ₆.map iotaZsqrtdNegTwo) h₆ℂ
  have hdeg : Module.finrank ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) = 2 ∨
      Module.finrank ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) = 3 := Or.inr (_finrank_quatH_detKer e)

  obtain ⟨Φ₂₀, hΦ₂₀, hBC₀⟩ :=
    _cyclic_descent
      ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) hdeg
      c₂ u₂ d₂₁ d₂₂ T₂ c₆ u₆ d₆₁ d₆₂ T₆ hc₂ hd₂₁ hd₂ hcov₂ hd₆ hcov₆
      (Φ₆.map iotaZsqrtdNegTwo) hc₆ℂ hfc
  have hBCseed : (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) Φ₂₀).AgreesAwayFromFinite
      ((P2.liftTraceSeed e (quatH e)).map iotaZsqrtdNegTwo) := _agrees_trans hBC₀ h₆ℂ

  obtain ⟨η, hηfin, ⟨𝔣, -, hmod⟩, Sη, hη⟩ :=
    exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
      ↥(fixFld (detKer e)) _ Φ₂₀ hΦ₂₀.isArithGenuineCuspRealizable 3 (by norm_num) (_b_cube_of_agrees_seed_quatH e Φ₂₀ hBCseed)
  obtain ⟨Φ', S', htw, hΦ'⟩ :=
    _twist_by_character ↥(fixFld (detKer e)) c₂ u₂ d₂₁ d₂₂ T₂ hc₂ hd₂₁ hd₂ Φ₂₀ hΦ₂₀ η hηfin 𝔣 hmod
  obtain ⟨hb, hBC'⟩ := _selection e Φ₂₀ Φ'
    (fun v => ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ↥(fixFld (detKer e))) ↥(fixFld (detKer e)) v)) :
      ℂˣ) : ℂ))
    hBCseed ⟨Sη, hη⟩ ⟨S', htw⟩
  refine ⟨Φ', hΦ', ?_, hb, hBC'⟩
  exact _isConstantOnFibers_descended e c₂ u₂ d₂₁ d₂₂ T₂ hc₂ hd₂₁ hd₂ hcov₂ c₆ u₆ d₆₁ d₆₂ T₆ hd₆ hcov₆
    (Φ₆.map iotaZsqrtdNegTwo) hc₆ℂ h₆ℂ Φ' hΦ' hBC' hb

end
end S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH
end P2MW
export P2MW.S_LanglandsTunnell_exists_isConstantOnFibers_b_formalBaseChange_arithBoundedGenuineCuspRealizable_detKer_of_quatH (solution)
