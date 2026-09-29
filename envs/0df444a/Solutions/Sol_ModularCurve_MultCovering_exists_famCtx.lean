-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_famCtx
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8d07562d-736d-5364-9e7f-e7efc227baa7

import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_ModularCurve_exists_ratFamily_isEmbBasis
import Theorems.Thm_Module_exists_basis_padicValRat_apply_nonneg_iff_pair
import Theorems.Thm_ModularCurve_exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap_algebraMap
import Theorems.Thm_ModularCurve_MultCovering_nonempty_annCtx
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_MultCovering_nonempty_chartCtx
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_padicValRat_coeff_frickeInvolutionFull_nonneg
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal
import Theorems.Thm_ModularCurve_MultCovering_FamData_t_zeroChart_of_orth
import Theorems.Thm_ModularCurve_MultCovering_FamData_one_le_hasseExp_of_orth
import Theorems.Thm_ModularCurve_MultCovering_FamData_inf_h0_of_one_le_hasseExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_famCtx
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.LevelOnePhi.instAddCommGroup ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve.MultCovering"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "MultCovering.FamCtx embDegree embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization exists_ratFamily_isEmbBasis exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg linearIndependent_coeffMap_algebraMap PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "FamData zeroSeries hasseContent hasseExp goodFamilyZero ssPolyBar ssPolyBarZero FamCtx FamCtx.t_zeroChart FamData.t_eq jBar mAnnuli ChartCtx infChart zeroChart ssValue AnnCtx nonempty_annCtx nonempty_chartCtx eq_mAnnuli_add_one_of_isEmbBasis infChart_residue_eq_ssPolyBar_mul_of_orthogonal FamData.t_zeroChart_of_orth FamData.one_le_hasseExp_of_orth FamData.inf_h0_of_one_le_hasseExp"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

section
variable (p : ℕ) [Fact p.Prime]

abbrev bc (g : ↥(modularFunctionFieldFull (1 * p))) : ↥(modularFunctionFieldBar (1 * p)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) g.2⟩

theorem coe_bc (g : ↥(modularFunctionFieldFull (1 * p))) :
    ((bc p g : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ) := rfl

theorem coeff_bc (g : ↥(modularFunctionFieldFull (1 * p))) (n : ℤ) :
    ((bc p g : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)).coeff n
      = algebraMap ℚ (AlgebraicClosure ℚ) ((g : LaurentSeries ℚ).coeff n) := by
  rw [coe_bc, coeffEmb_coeff]

theorem bc_injective : Function.Injective (bc p) := by
  intro g h hgh
  apply Subtype.ext
  ext n
  have := congrArg (fun x : ↥(modularFunctionFieldBar (1 * p)) => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n) hgh
  simp only [coeff_bc] at this
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective this

theorem bc_add (g h : ↥(modularFunctionFieldFull (1 * p))) : bc p (g + h) = bc p g + bc p h := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) ((g + h : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) = _
  rw [IntermediateField.coe_add, map_add]
  rfl

theorem bc_smul (c : ℚ) (g : ↥(modularFunctionFieldFull (1 * p))) :
    bc p (c • g) = algebraMap ℚ (AlgebraicClosure ℚ) c • bc p g := by
  apply Subtype.ext
  ext n
  have hL : (((c • g : ↥(modularFunctionFieldFull (1 * p))) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff n
      = c * (g : LaurentSeries ℚ).coeff n := by
    have : (((c • g : ↥(modularFunctionFieldFull (1 * p))) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ)
        = c • (g : LaurentSeries ℚ) := rfl
    rw [this]
    first
      | rw [HahnSeries.coeff_smul, smul_eq_mul]
      | rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  have hR : (((algebraMap ℚ (AlgebraicClosure ℚ) c • bc p g : ↥(modularFunctionFieldBar (1 * p))) :
      ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)).coeff n
      = algebraMap ℚ (AlgebraicClosure ℚ) c * ((bc p g : ↥(modularFunctionFieldBar (1 * p))) :
          LaurentSeries (AlgebraicClosure ℚ)).coeff n := by
    rw [Algebra.smul_def, IntermediateField.coe_mul]
    have : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) c) :
        ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) c) := rfl
    rw [this, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  rw [hR, coeff_bc, coeff_bc, hL, map_mul]

theorem bc_one : bc p 1 = 1 := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) ((1 : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) = _
  rw [OneMemClass.coe_one, map_one]
  rfl

def bcAdd : ↥(modularFunctionFieldFull (1 * p)) →+ ↥(modularFunctionFieldBar (1 * p)) where
  toFun := bc p
  map_zero' := by
    apply Subtype.ext
    show coeffEmb (AlgebraicClosure ℚ) ((0 : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) = _
    rw [ZeroMemClass.coe_zero, map_zero]
    rfl
  map_add' := bc_add p

theorem bcAdd_apply (g : ↥(modularFunctionFieldFull (1 * p))) : bcAdd p g = bc p g := rfl

theorem linearIndependent_bc {ι : Type*} (g : ι → ↥(modularFunctionFieldFull (1 * p)))
    (hg : LinearIndependent ℚ g) : LinearIndependent (AlgebraicClosure ℚ) (fun i => bc p (g i)) := by
  let val : ↥(modularFunctionFieldFull (1 * p)) →ₗ[ℚ] LaurentSeries ℚ :=
    (AddMonoidHom.mk' (fun x : ↥(modularFunctionFieldFull (1 * p)) => (x : LaurentSeries ℚ))
      (fun _ _ => rfl)).toRatLinearMap
  have hval : ∀ x, val x = (x : LaurentSeries ℚ) := fun _ => rfl
  have h1 : LinearIndependent ℚ (fun i => ((g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ)) := by
    have h := hg.map' val (LinearMap.ker_eq_bot.mpr (fun x y hxy => Subtype.ext (by simpa [hval] using hxy)))
    simpa [Function.comp_def, hval] using h
  have h2 := ModularCurve.linearIndependent_coeffMap_algebraMap (L := AlgebraicClosure ℚ) _ h1
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi

  have hsm : ∀ (a : AlgebraicClosure ℚ) (y : LaurentSeries (AlgebraicClosure ℚ)),
      a • y = (HahnSeries.single (0 : ℤ) a : LaurentSeries (AlgebraicClosure ℚ)) * y := fun a y => by
    rw [← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]
  have h0 : ∑ j ∈ s, c j • ((bc p (g j) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
    have h := congrArg (fun x : ↥(modularFunctionFieldBar (1 * p)) => (x : LaurentSeries (AlgebraicClosure ℚ))) hc
    simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [IntermediateField.coe_smul, hsm, Algebra.smul_def, algebraMap_laurentSeries_eq_single]
  exact (linearIndependent_iff'.mp h2) s c h0 i hi

theorem linearIndependent_of_bc {ι : Type*} (g : ι → ↥(modularFunctionFieldFull (1 * p)))
    (hg : LinearIndependent (AlgebraicClosure ℚ) (fun i => bc p (g i))) : LinearIndependent ℚ g := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  have h0 : ∑ j ∈ s, algebraMap ℚ (AlgebraicClosure ℚ) (c j) • bc p (g j) = 0 := by
    have h := congrArg (bcAdd p) hc
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [bcAdd_apply, bc_smul]
  have h := (linearIndependent_iff'.mp hg) s (fun j => algebraMap ℚ (AlgebraicClosure ℚ) (c j)) h0 i hi
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by rw [h, map_zero])

theorem mem_span_of_bc_mem_span {ι : Type*} [Fintype ι] (g : ι → ↥(modularFunctionFieldFull (1 * p)))
    (hg : LinearIndependent ℚ g) (x : ↥(modularFunctionFieldFull (1 * p)))
    (hx : bc p x ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range fun i => bc p (g i))) :
    x ∈ Submodule.span ℚ (Set.range g) := by
  classical
  by_contra hxn

  have hli : LinearIndependent ℚ (fun o : Option ι => o.casesOn' x g) :=
    (linearIndependent_option' (v := g) (x := x)).mpr ⟨hg, hxn⟩

  have hli' := linearIndependent_bc p _ hli
  have hx' : bc p x ∉ Submodule.span (AlgebraicClosure ℚ) (Set.range fun i => bc p (g i)) := by
    have h := (linearIndependent_option' (K := AlgebraicClosure ℚ) (v := fun i => bc p (g i)) (x := bc p x)).mp
      (by
        convert hli' using 1 <;> first | rfl | (funext o; cases o <;> rfl))
    exact h.2
  exact hx' hx

theorem forall_ord_nonneg_of_mem_riemannRochSpace (f : ↥(modularFunctionFieldBar (1 * p)))
    (hf : f ∈ riemannRochSpace (embDivisor (1 * p))) :
    ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ≠ cuspInftyBar (1 * p) → 0 ≤ W.ord f := by
  intro W hW
  rw [AlgebraicCurve.mem_riemannRochSpace_iff] at hf
  rcases hf W with h0 | h
  · rw [h0]
    simp [AlgebraicCurve.Place.ord_zero]
  · have : embDivisor (1 * p) W = 0 := by
      simp [embDivisor, Finsupp.single_apply, Ne.symm hW, hW]
    rw [this, neg_zero] at h
    exact h

end

def HSUBStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ g : ↥(modularFunctionFieldFull (1 * p)), bc p g ∈ riemannRochSpace (embDivisor (1 * p)) →
    (∀ m : ℤ, 0 ≤ padicValRat p ((g : LaurentSeries ℚ).coeff m)) →
    ∀ m : ℤ, 0 ≤ padicValRat p (((frickeInvolutionFull (1 * p) g : ↥(modularFunctionFieldFull (1 * p))) :
      LaurentSeries ℚ).coeff m)

def INFStatement (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (r : ℕ) : Prop :=
  ∀ (D : FamData p r), (∀ l : Fin r, (l : ℕ) = 0 → D.tRat l = 1) → (∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1) →
    IsEmbBasis (1 * p) D.t →
    (∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i)) →
    (∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i)) →
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
    ∃ hint : ∀ l, (⟨coeffEmb (AlgebraicClosure ℚ) ↑(D.tRat l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (D.tRat l).2⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ (infChart Γ).integers,
      (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) ↑(D.tRat l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (D.tRat l).2⟩ : ↥(modularFunctionFieldBar (1 * p))), hint l⟩ = 1) ∧
      ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          (P l).natDegree + 1 ≤ mAnnuli p ∧
          (infChart Γ).residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) ↑(D.tRat l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (D.tRat l).2⟩ : ↥(modularFunctionFieldBar (1 * p))), hint l⟩
            = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
        Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
          = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p)

def ZEROStatement (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (r : ℕ) : Prop :=
  ∀ (D : FamData p r), (∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1) → IsEmbBasis (1 * p) D.t →
    (∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i)) →
    (∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i)) →
    (∀ l : Fin r, (l : ℕ) = 0 → hasseExp D l = 0) →
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
      (_ : AnnCtx Γ), (∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) →
    ∃ (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers)
      (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)),
      (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
      LinearIndependent (IsLocalRing.ResidueField ↥A) P ∧
      (∀ Q : Polynomial (IsLocalRing.ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
        Q ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P)) ∧
      (∀ l : Fin r, (l : ℕ) = 0 →
        P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
      ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ * ssPolyBarZero Γ
        = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)

theorem hasseExp_eq_of_orth (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r) (e : Fin r → ℕ)
    (hne : ∀ l, D.tRat l ≠ 0)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -(e i : ℤ) ≤ padicValRat p (c i)) :
    ∀ l, hasseExp D l = e l := by
  classical
  intro l
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  set z : LaurentSeries ℚ := zeroSeries D l with hz
  have hzdef : z = ((frickeInvolutionFull (1 * p) (D.tRat l) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) := rfl

  have hsingle : ∀ x : ℚ, (((∑ i, (Pi.single l x : Fin r → ℚ) i • frickeInvolutionFull (1 * p) (D.tRat i) :
      ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ)) = x • z := by
    intro x
    rw [Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul]) (fun h => (h (Finset.mem_univ l)).elim),
      Pi.single_eq_same]
    rfl
  have htest : ∀ x : ℚ, (∀ m : ℤ, 0 ≤ padicValRat p (x * z.coeff m)) ↔ (x = 0 ∨ -(e l : ℤ) ≤ padicValRat p x) := by
    intro x
    have h := horthZero (Pi.single l x)
    rw [hsingle] at h
    simp only [HahnSeries.coeff_smul, smul_eq_mul] at h
    rw [h]
    constructor
    · intro hi
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (by simpa [Pi.single_eq_same] using hi l)
    · rintro (rfl | hx) i
      · simp [Pi.single_apply]
      · by_cases hi : i = l
        · subst hi; simpa [Pi.single_eq_same] using hx
        · rw [Pi.single_eq_of_ne hi, padicValRat.zero]; exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le _)

  have hge : ∀ k : ℤ, z.coeff k ≠ 0 → (e l : ℤ) ≤ padicValRat p (z.coeff k) := by
    intro k hk
    have hx : ((p : ℚ) ^ (e l))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hp)
    have := ((htest ((p : ℚ) ^ (e l))⁻¹).mpr (Or.inr ?_)) k
    · rw [padicValRat.mul hx hk, padicValRat.inv, padicValRat.pow _, padicValRat.self (Fact.out : p.Prime).one_lt] at this
      push_cast at this; linarith
    · rw [padicValRat.inv, padicValRat.pow _, padicValRat.self (Fact.out : p.Prime).one_lt]; push_cast; linarith

  have heq : ∃ k : ℤ, z.coeff k ≠ 0 ∧ padicValRat p (z.coeff k) = e l := by
    by_contra hcon
    push_neg at hcon
    have hx : ((p : ℚ) ^ (e l + 1))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hp)
    have hall : ∀ m : ℤ, 0 ≤ padicValRat p (((p : ℚ) ^ (e l + 1))⁻¹ * z.coeff m) := by
      intro m
      by_cases hm : z.coeff m = 0
      · rw [hm, mul_zero, padicValRat.zero]
      · have h1 := hge m hm
        have h2 : padicValRat p (z.coeff m) ≠ e l := hcon m hm
        rw [padicValRat.mul hx hm, padicValRat.inv, padicValRat.pow _, padicValRat.self (Fact.out : p.Prime).one_lt]
        push_cast
        have : (e l : ℤ) + 1 ≤ padicValRat p (z.coeff m) := by omega
        linarith
    rcases (htest _).mp hall with h0 | hv
    · exact hx h0
    · rw [padicValRat.inv, padicValRat.pow _, padicValRat.self (Fact.out : p.Prime).one_lt] at hv
      push_cast at hv; linarith

  have hcond : ∃ n : ℤ, (∀ k : ℤ, z.coeff k ≠ 0 → n ≤ padicValRat p (z.coeff k)) ∧
      (∃ k : ℤ, z.coeff k ≠ 0 ∧ padicValRat p (z.coeff k) = n) := ⟨e l, hge, heq⟩
  have huniq : ∀ n : ℤ, ((∀ k : ℤ, z.coeff k ≠ 0 → n ≤ padicValRat p (z.coeff k)) ∧
      (∃ k : ℤ, z.coeff k ≠ 0 ∧ padicValRat p (z.coeff k) = n)) → n = e l := by
    rintro n ⟨hn1, k, hk, hkn⟩
    obtain ⟨k', hk', hk'n⟩ := heq
    have a1 := hn1 k' hk'
    have a2 := hge k hk
    rw [hk'n] at a1; rw [hkn] at a2
    exact le_antisymm a1 a2
  have hc : hasseContent D l = e l := by
    unfold hasseContent
    rw [dif_pos hcond]
    exact huniq _ hcond.choose_spec
  unfold hasseExp
  rw [hc]
  exact Int.toNat_natCast _

def coeffFn (p : ℕ) [Fact p.Prime] (m : ℤ) : ↥(modularFunctionFieldFull (1 * p)) →ₗ[ℚ] ℚ where
  toFun x := (x : LaurentSeries ℚ).coeff m
  map_add' x y := by
    show ((x + y : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m = _
    rw [IntermediateField.coe_add, HahnSeries.coeff_add]
  map_smul' c x := by
    show ((c • x : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m = c • (x : LaurentSeries ℚ).coeff m
    have hcx : (((c • x : ↥(modularFunctionFieldFull (1 * p))) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ)
        = c • (x : LaurentSeries ℚ) := rfl
    rw [hcx]
    first
      | rw [HahnSeries.coeff_smul]
      | rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, smul_eq_mul]

@[scoped simp] theorem coeffFn_apply (p : ℕ) [Fact p.Prime] (m : ℤ) (x : ↥(modularFunctionFieldFull (1 * p))) :
    coeffFn p m x = (x : LaurentSeries ℚ).coeff m := rfl

theorem one_mem_riemannRochSpace_embDivisor (p : ℕ) [Fact p.Prime] :
    (1 : ↥(modularFunctionFieldBar (1 * p))) ∈ riemannRochSpace (embDivisor (1 * p)) := by
  classical
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  rw [Place.ord_one]
  have h0 : 0 ≤ embDivisor (1 * p) v := by
    show 0 ≤ ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) v
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs <;> simp
  omega

theorem bc_mem_span_of_mem_span (p : ℕ) [Fact p.Prime] {ι : Type*} (g : ι → ↥(modularFunctionFieldFull (1 * p)))
    (x : ↥(modularFunctionFieldFull (1 * p))) (hx : x ∈ Submodule.span ℚ (Set.range g)) :
    bc p x ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range fun i => bc p (g i)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero =>
    have h0 : bc p 0 = 0 := by rw [← bcAdd_apply, map_zero]
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [bc_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [bc_smul]
    exact Submodule.smul_mem _ _ hx

theorem exists_famCtx_of (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ}
    (hHSUB : HSUBStatement p) (hINF : INFStatement p hp5 r) (hZERO : ZEROStatement p hp5 r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Nonempty (FamCtx p r) := by
  classical

  obtain ⟨g, hg⟩ := ModularCurve.exists_ratFamily_isEmbBasis p s hs
  have hgQ : LinearIndependent ℚ g := linearIndependent_of_bc p g hg.1

  let M : Submodule ℚ ↥(modularFunctionFieldFull (1 * p)) := Submodule.span ℚ (Set.range g)
  haveI : FiniteDimensional ℚ ↥M := FiniteDimensional.span_of_finite ℚ (Set.finite_range g)
  let wF : ↥(modularFunctionFieldFull (1 * p)) →ₗ[ℚ] ↥(modularFunctionFieldFull (1 * p)) :=
    (frickeInvolutionFull (1 * p)).toLinearMap
  let a  : ℤ → ↥M →ₗ[ℚ] ℚ := fun m => (coeffFn p m).comp M.subtype
  let a' : ℤ → ↥M →ₗ[ℚ] ℚ := fun m => (coeffFn p m).comp (wF.comp M.subtype)
  have ha : ∀ m (x : ↥M), a m x = ((x : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := fun _ _ => rfl
  have ha' : ∀ m (x : ↥M), a' m x = ((frickeInvolutionFull (1 * p) (x : ↥(modularFunctionFieldFull (1 * p))) :
      ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := fun _ _ => rfl

  have hMW : ∀ x : ↥M, bc p (x : ↥(modularFunctionFieldFull (1 * p))) ∈ riemannRochSpace (embDivisor (1 * p)) := by
    intro x
    rw [← hg.2]
    exact bc_mem_span_of_mem_span p g x x.2

  have hinj' : ∀ x : ↥M, (∀ m, a' m x = 0) → x = 0 := by
    intro x hx
    have h1 : ((frickeInvolutionFull (1 * p) (x : ↥(modularFunctionFieldFull (1 * p))) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) = 0 := by
      ext m
      have := hx m
      rw [ha'] at this
      simpa using this
    have h2 : frickeInvolutionFull (1 * p) (x : ↥(modularFunctionFieldFull (1 * p))) = 0 := by
      apply Subtype.ext
      rw [h1]
      rfl
    have h3 : (x : ↥(modularFunctionFieldFull (1 * p))) = 0 :=
      (map_eq_zero_iff _ (frickeInvolutionFull (1 * p)).injective).mp h2
    exact Subtype.ext h3
  have hbd : ∀ x : ↥M, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a m x) := by
    intro x
    exact ModularCurve.exists_forall_padicValRat_pow_mul_coeff_nonneg_of_forall_ord_nonneg p (1 * p)
      (x : ↥(modularFunctionFieldFull (1 * p))) (forall_ord_nonneg_of_mem_riemannRochSpace p _ (hMW x))
  have hsub : ∀ x : ↥M, (∀ m, 0 ≤ padicValRat p (a m x)) → ∀ m, 0 ≤ padicValRat p (a' m x) := by
    intro x hx
    exact hHSUB (x : ↥(modularFunctionFieldFull (1 * p))) (hMW x) hx
  have hbd' : ∀ x : ↥M, ∃ N : ℕ, ∀ m, 0 ≤ padicValRat p ((p : ℚ) ^ N * a' m x) := by
    intro x
    obtain ⟨N, hN⟩ := hbd x
    refine ⟨N, fun m => ?_⟩
    have hy : ∀ m, 0 ≤ padicValRat p (a m (((p : ℚ) ^ N) • x)) := fun m => by
      rw [map_smul, smul_eq_mul]; exact hN m
    have h := hsub _ hy m
    rwa [map_smul, smul_eq_mul] at h

  have h1M : (1 : ↥(modularFunctionFieldFull (1 * p))) ∈ M := by
    apply mem_span_of_bc_mem_span p g hgQ
    rw [bc_one, hg.2]
    exact one_mem_riemannRochSpace_embDivisor p
  let u : ↥M := ⟨1, h1M⟩
  have hu : ∀ m, 0 ≤ padicValRat p (a m u) := by
    intro m
    rw [ha]
    show 0 ≤ padicValRat p (((1 : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m)
    rw [OneMemClass.coe_one]
    by_cases hm : m = 0
    · subst hm; simp
    · simp [hm]
  have hprim : ∃ m, a' m u ≠ 0 ∧ padicValRat p (a' m u) = 0 := by
    have h1 : a' 0 u = 1 := by
      rw [ha']
      show ((frickeInvolutionFull (1 * p) (1 : ↥(modularFunctionFieldFull (1 * p))) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff 0 = 1
      rw [map_one, OneMemClass.coe_one]
      simp
    exact ⟨0, by rw [h1]; exact one_ne_zero, by rw [h1]; exact padicValRat.one⟩

  obtain ⟨n, b, e, i₀, hb0, he0, horth, horth'⟩ :=
    Module.exists_basis_padicValRat_apply_nonneg_iff_pair p a a' hinj' hbd hbd' hsub u hu hprim

  have hnr : n = r := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℚ ↥M = r := by
      show Module.finrank ℚ ↥(Submodule.span ℚ (Set.range g)) = r
      rw [finrank_span_eq_card hgQ, Fintype.card_fin]
    rw [h2, Fintype.card_fin] at h1
    exact h1.symm
  subst hnr
  have hn0 : 0 < n := Fin.pos i₀
  let σ : Equiv.Perm (Fin n) := Equiv.swap ⟨0, hn0⟩ i₀
  let b' : Fin n → ↥M := fun l => b (σ l)
  let e' : Fin n → ℕ := fun l => e (σ l)
  have hb'0 : ∀ l : Fin n, (l : ℕ) = 0 → b' l = u := by
    intro l hl
    have : l = ⟨0, hn0⟩ := Fin.ext hl
    subst this
    show b (Equiv.swap ⟨0, hn0⟩ i₀ ⟨0, hn0⟩) = u
    rw [Equiv.swap_apply_left, hb0]
  have he'0 : ∀ l : Fin n, (l : ℕ) = 0 → e' l = 0 := by
    intro l hl
    have : l = ⟨0, hn0⟩ := Fin.ext hl
    subst this
    show e (Equiv.swap ⟨0, hn0⟩ i₀ ⟨0, hn0⟩) = 0
    rw [Equiv.swap_apply_left, he0]

  let D : FamData p n :=
    { t := fun l => bc p (b' l : ↥(modularFunctionFieldFull (1 * p)))
      tRat := fun l => (b' l : ↥(modularFunctionFieldFull (1 * p)))
      t_eq := fun _ => rfl }

  have horthInf : ∀ c : Fin n → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i) := by
    intro c
    have hre : (∑ i, c i • ((b' i : ↥M) : ↥(modularFunctionFieldFull (1 * p))))
        = ∑ j, c (σ.symm j) • ((b j : ↥M) : ↥(modularFunctionFieldFull (1 * p))) :=
      Fintype.sum_equiv σ _ _ (fun i => by simp only [b', Equiv.symm_apply_apply])
    have key : ∀ m, a m (∑ j, c (σ.symm j) • b j) =
        ((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := by
      intro m
      rw [ha, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hre]
    constructor
    · intro h i
      have h' := (horth (fun j => c (σ.symm j))).mp (fun m => by rw [key m]; exact h m) (σ i)
      simpa only [Equiv.symm_apply_apply] using h'
    · intro h m
      rw [← key m]
      exact (horth (fun j => c (σ.symm j))).mpr (fun j => h (σ.symm j)) m
  have horthZero : ∀ c : Fin n → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -(e' i : ℤ) ≤ padicValRat p (c i) := by
    intro c
    have hre : (∑ i, c i • frickeInvolutionFull (1 * p) ((b' i : ↥M) : ↥(modularFunctionFieldFull (1 * p))))
        = ∑ j, c (σ.symm j) • frickeInvolutionFull (1 * p) ((b j : ↥M) : ↥(modularFunctionFieldFull (1 * p))) :=
      Fintype.sum_equiv σ _ _ (fun i => by simp only [b', Equiv.symm_apply_apply])
    have key : ∀ m, a' m (∑ j, c (σ.symm j) • b j) =
        ((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := by
      intro m
      have hw : ∀ (q : ℚ) (y : ↥(modularFunctionFieldFull (1 * p))), frickeInvolutionFull (1 * p) (q • y) = q • frickeInvolutionFull (1 * p) y :=
        fun q y => by rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      rw [ha', Submodule.coe_sum, map_sum]
      simp only [Submodule.coe_smul, hw]
      rw [← hre]
    constructor
    · intro h i
      have h' := (horth' (fun j => c (σ.symm j))).mp (fun m => by rw [key m]; exact h m) (σ i)
      simpa only [e', Equiv.symm_apply_apply] using h'
    · intro h m
      rw [← key m]
      exact (horth' (fun j => c (σ.symm j))).mpr (fun j => by simpa only [e', Equiv.apply_symm_apply] using h (σ.symm j)) m

  have hne : ∀ l, D.tRat l ≠ 0 := by
    intro l h
    exact b.ne_zero (σ l) (Subtype.ext h)
  have hexp : ∀ l, hasseExp D l = e' l := hasseExp_eq_of_orth p D e' hne horthZero
  have horthZeroD : ∀ c : Fin n → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i) := by
    intro c; rw [horthZero c]; simp only [hexp]
  have hexp0 : ∀ l : Fin n, (l : ℕ) = 0 → hasseExp D l = 0 := fun l hl => by rw [hexp, he'0 l hl]

  have hzero : ∀ l : Fin n, (l : ℕ) = 0 → D.t l = 1 := by
    intro l hl
    show bc p (b' l : ↥(modularFunctionFieldFull (1 * p))) = 1
    rw [hb'0 l hl]
    exact bc_one p
  have hbasis : IsEmbBasis (1 * p) D.t := by
    have hli : LinearIndependent ℚ (fun i => ((b' i : ↥M) : ↥(modularFunctionFieldFull (1 * p)))) := by
      have h1 : LinearIndependent ℚ b' := by
        have h := (b.reindex σ.symm).linearIndependent
        convert h using 1 <;> first | rfl | (funext i; simp only [b', Module.Basis.reindex_apply, Equiv.symm_symm])
      exact h1.map' M.subtype (Submodule.ker_subtype M)
    have hliD : LinearIndependent (AlgebraicClosure ℚ) D.t := linearIndependent_bc p _ hli
    refine ⟨hliD, ?_⟩
    have hle : Submodule.span (AlgebraicClosure ℚ) (Set.range D.t) ≤ riemannRochSpace (embDivisor (1 * p)) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hMW (b' i))
    haveI : FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace (embDivisor (1 * p)) :
        Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) := by
      rw [← hg.2]; exact FiniteDimensional.span_of_finite _ (Set.finite_range _)
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hliD]
    have h2 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (embDivisor (1 * p)) :
        Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) = n := by
      rw [← hg.2, finrank_span_eq_card hg.1, Fintype.card_fin]
    rw [h2, Fintype.card_fin]
  have hzRat : ∀ l : Fin n, (l : ℕ) = 0 → D.tRat l = 1 := by
    intro l hl
    show ((b' l : ↥M) : ↥(modularFunctionFieldFull (1 * p))) = 1
    rw [hb'0 l hl]

  refine ⟨{ toFamData := D, t_basis := hbasis, t_zero := hzero,
            t_inf := fun A hA _ _ Γ => hINF D hzRat hzero hbasis horthInf horthZeroD A hA Γ,
            t_zeroChart := fun A hA _ _ Γ hw1 => ?_ }⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  exact hZERO D hzero hbasis horthInf horthZeroD hexp0 A hA Γ (Classical.choice (nonempty_annCtx p hp5 A Γ)) hw1

theorem hsubStatement (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : HSUBStatement p := by
  classical
  obtain ⟨A₀, hA₀⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  haveI : CharP (IsLocalRing.ResidueField ↥A₀) p := ValuationSubring.residueField_charP_of_liesOverPrime A₀ Fact.out hA₀
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A₀) := ValuationSubring.isAlgClosed_residueField A₀
  obtain ⟨Γ₀⟩ := nonempty_chartCtx p hp5 A₀ hA₀
  intro g hgW hint m
  exact ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg
    Γ₀.R g (forall_ord_nonneg_of_mem_riemannRochSpace p _ hgW) hint m

theorem infStatement (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) : INFStatement p hp5 r := by
  intro D hz hzero hbasis horthInf horthZero A hA _ _ Γ
  have hge1 := FamData.one_le_hasseExp_of_orth p D hzero hbasis horthInf horthZero A hA Γ
  have h0 := FamData.inf_h0_of_one_le_hasseExp p D hbasis horthZero hge1
  have hW : ∀ l : Fin r, (⟨coeffEmb (AlgebraicClosure ℚ) ↑(D.tRat l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (D.tRat l).2⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ riemannRochSpace (embDivisor (1 * p)) := by
    intro l
    rw [← D.t_eq l, ← hbasis.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  exact infChart_residue_eq_ssPolyBar_mul_of_orthogonal p hp5 (eq_mAnnuli_add_one_of_isEmbBasis p hp5 s hs)
    D.tRat hz hW horthInf h0 A hA Γ

theorem exists_famCtx_main (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Nonempty (FamCtx p r) := by
  refine exists_famCtx_of p hp5 (hsubStatement p hp5) (infStatement p hp5 s hs) ?_ s hs
  intro D hzero hbasis horthInf horthZero hexp0 A hA _ _ Γ Δ hw1
  exact FamData.t_zeroChart_of_orth p hp5 D hzero hbasis horthInf horthZero hexp0 A hA Γ Δ hw1

end ModularCurve.MultCovering
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve.MultCovering"
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve"

p2m_open "ModularCurve~jBar" in open _root_.P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve.MultCovering in
set_option maxHeartbeats 3200000 in

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Nonempty (ModularCurve.MultCovering.FamCtx p r) :=
  ModularCurve.MultCovering.exists_famCtx_main p hp5 s hs

end
p2m_reactivate "P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve P2MW.S_ModularCurve_MultCovering_exists_famCtx.ModularCurve.MultCovering"

end S_ModularCurve_MultCovering_exists_famCtx
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_famCtx (solution)
