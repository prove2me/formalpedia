-- Prove2me | solution 1 for ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e0922665-bc40-5c90-abd4-40b324478a0c

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_exists_chartData_of_lineResidues
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_MultCovering_cuspInftyBar_not_mem_zeroChart_dom
import Theorems.Thm_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
import Theorems.Thm_ModularCurve_exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_MultCovering_nonempty_annCtx
import Theorems.Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ValuationSubring.instIsAlgClosedResidueField ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁"
p2m_attr_erase "instance" "instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ValuationSubring.reduceAt_coe"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of"
p2m_attr_erase "simp" "AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent.ModularCurve.MultCovering"
open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet jqModC modularFunctionFieldC jqModC_mem charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC frickeInvolutionBar jWidth_of_ne exists_chartData_of_lineResidues eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap ord_charLGeomPlaceEquiv_placeInfty_jqModC zero_mem_ssJSet_iff ofNat1728_mem_ssJSet_iff MultCovering.nonempty_annCtx"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "hasseExp goodFamilyZero ssPolyBarZero FamCtx jBar mAnnuli ChartCtx infChart zeroChart chart ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq cuspInftyBar_not_mem_zeroChart_dom cuspInftyBar_mem_infChart_dom mem_zeroChart_nodes_iff zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes nonempty_annCtx mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge"
namespace P2Mcdw
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

section LineAlgebraWide

variable {k : Type} [Field k] {r : ℕ} (R : Fin r → k[X])

theorem minor_eq_of_forall (f g : k[X] →ₗ[k] k) (h : ∀ a b, f (R a) * g (R b) = f (R b) * g (R a))
    {u v : k[X]} (hu : u ∈ Submodule.span k (Set.range R)) (hv : v ∈ Submodule.span k (Set.range R)) :
    f u * g v = f v * g u := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hu
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hv
  simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  first
  | linear_combination (c j * d i) * h j i
  | linear_combination (c j * d i) * h i j
  | linear_combination (c i * d j) * h i j
  | linear_combination (c i * d j) * h j i

theorem exists_eval_ne_zero' {D : k[X]} (hD : D ∈ Submodule.span k (Set.range R)) (x₀ : k)
    (hDx : D.eval x₀ ≠ 0) : ∃ l, (R l).eval x₀ ≠ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hD
  apply hDx
  rw [← hc, eval_finset_sum]
  simp [eval_smul, hall]

theorem exists_rootMultiplicity_eq_one' {D D' : k[X]} {a : k} (hDa : D = (X - C a) * D')
    (hD : D ∈ Submodule.span k (Set.range R)) (hD' : D' ∈ Submodule.span k (Set.range R))
    (x₀ : k) (hDx : D.eval x₀ ≠ 0) (c : Fin r) (hc : (R c).eval x₀ ≠ 0) :
    ∃ l, (R l * C ((R c).eval x₀) - R c * C ((R l).eval x₀)).rootMultiplicity x₀ = 1 := by
  set φ : k[X] → k[X] := fun Q => Q * C ((R c).eval x₀) - R c * C (Q.eval x₀) with hφ
  have hφsum : ∀ w : Fin r → k, φ (∑ l, w l • R l) = ∑ l, w l • φ (R l) := by
    intro w
    simp only [hφ, smul_eq_C_mul, Finset.sum_mul, eval_finset_sum, eval_C_mul, map_sum, map_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, mul_sub]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hroot : ∀ Q, (φ Q).IsRoot x₀ := by
    intro Q
    simp only [hφ, IsRoot, eval_sub, eval_mul, eval_C]
    ring
  by_contra hall
  push_neg at hall
  have hdvd : ∀ l, (X - C x₀) ^ 2 ∣ φ (R l) := by
    intro l
    by_cases h0 : φ (R l) = 0
    · rw [h0]; exact dvd_zero _
    · rw [← le_rootMultiplicity_iff h0]
      have hpos : 0 < (φ (R l)).rootMultiplicity x₀ := (rootMultiplicity_pos h0).mpr (hroot (R l))
      have hne : (φ (R l)).rootMultiplicity x₀ ≠ 1 := hall l
      omega

  have hT : D + (a - x₀) • D' ∈ Submodule.span k (Set.range R) :=
    Submodule.add_mem _ hD (Submodule.smul_mem _ _ hD')
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hT
  have hTeq : D + (a - x₀) • D' = D' * (X - C x₀) := by
    rw [hDa, smul_eq_C_mul, map_sub]; ring
  have hD'x : D'.eval x₀ ≠ 0 := by
    intro h0; apply hDx; rw [hDa, eval_mul, h0, mul_zero]
  have hdvd' : (X - C x₀) ^ 2 ∣ φ (D' * (X - C x₀)) := by
    have h' : (X - C x₀) ^ 2 ∣ φ (∑ l, w l • R l) := by
      rw [hφsum]
      exact Finset.dvd_sum fun l _ => by rw [smul_eq_C_mul]; exact (hdvd l).mul_left _
    rwa [hw, hTeq] at h'
  have hφT : φ (D' * (X - C x₀)) = C ((R c).eval x₀) * D' * (X - C x₀) := by
    simp only [hφ, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, map_zero]
    ring
  rw [hφT] at hdvd'
  have hne0 : C ((R c).eval x₀) * D' * (X - C x₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by rwa [Ne, C_eq_zero]) (fun h => hD'x (by rw [h, eval_zero]))) (X_sub_C_ne_zero x₀)
  have hne1 : C ((R c).eval x₀) * D' ≠ 0 :=
    mul_ne_zero (by rwa [Ne, C_eq_zero]) (fun h => hD'x (by rw [h, eval_zero]))
  have h2 := (le_rootMultiplicity_iff hne0).mpr hdvd'
  rw [rootMultiplicity_mul hne0, rootMultiplicity_mul hne1, rootMultiplicity_C, rootMultiplicity_X_sub_C_self,
    rootMultiplicity_eq_zero (fun h : IsRoot D' x₀ => hD'x h)] at h2
  omega

theorem exists_eval_minor_ne' {D D' : k[X]} {a : k} (hDa : D = (X - C a) * D')
    (hD : D ∈ Submodule.span k (Set.range R)) (hD' : D' ∈ Submodule.span k (Set.range R))
    (x₀ y₀ : k) (hDx : D.eval x₀ ≠ 0) (hDy : D.eval y₀ ≠ 0) (hxy : x₀ ≠ y₀) :
    ∃ a b, (R a).eval x₀ * (R b).eval y₀ ≠ (R b).eval x₀ * (R a).eval y₀ := by
  by_contra hall
  push_neg at hall
  have key := minor_eq_of_forall R (leval x₀) (leval y₀)
    (fun a b => by simpa only [leval_apply] using hall a b) hD hD'
  simp only [leval_apply] at key
  have hD'x : D'.eval x₀ ≠ 0 := by intro h0; apply hDx; rw [hDa, eval_mul, h0, mul_zero]
  have hD'y : D'.eval y₀ ≠ 0 := by intro h0; apply hDy; rw [hDa, eval_mul, h0, mul_zero]
  rw [hDa, eval_mul, eval_mul, eval_sub, eval_sub, eval_X, eval_X, eval_C, eval_C] at key

  have : (x₀ - y₀) * (D'.eval x₀ * D'.eval y₀) = 0 := by linear_combination key
  rcases mul_eq_zero.mp this with h | h
  · exact hxy (sub_eq_zero.mp h)
  · rcases mul_eq_zero.mp h with h | h
    · exact hD'x h
    · exact hD'y h

theorem exists_natDegree_eq' {D : k[X]} (hD : D ∈ Submodule.span k (Set.range R)) (hD0 : D ≠ 0)
    (hle : ∀ l, (R l).natDegree ≤ D.natDegree) : ∃ l, (R l).natDegree = D.natDegree := by
  by_contra hall
  push_neg at hall
  have hlt : ∀ l, R l ∈ degreeLT k D.natDegree := by
    intro l
    rw [mem_degreeLT]
    by_cases h0 : R l = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0]
      exact_mod_cast lt_of_le_of_ne (hle l) (hall l)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hD
  have hmem : (∑ l, c l • R l) ∈ degreeLT k D.natDegree :=
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hlt l)
  rw [hc, mem_degreeLT, degree_eq_natDegree hD0] at hmem
  exact lt_irrefl _ hmem

theorem exists_eval_coeff_minor_ne' {D D' : k[X]} {a : k} (hDa : D = (X - C a) * D')
    (hD : D ∈ Submodule.span k (Set.range R)) (hD' : D' ∈ Submodule.span k (Set.range R))
    (cI : Fin r) (hN : (R cI).natDegree = D.natDegree) (hlc : (R cI).leadingCoeff ≠ 0)
    (hdeg' : D'.natDegree + 1 = D.natDegree)
    (x₀ : k) (hDx : D.eval x₀ ≠ 0) :
    ∃ a b, (R a).eval x₀ * ((R b).coeff (R cI).natDegree / (R cI).leadingCoeff)
      ≠ (R b).eval x₀ * ((R a).coeff (R cI).natDegree / (R cI).leadingCoeff) := by
  rw [hN]
  by_contra hall
  push_neg at hall
  have hall' : ∀ a b, (R a).eval x₀ * (R b).coeff D.natDegree = (R b).eval x₀ * (R a).coeff D.natDegree := by
    intro a b
    have h := hall a b
    field_simp at h
    first
    | linear_combination h
    | linear_combination -h
    | (have h2 : ((R a).eval x₀ * (R b).coeff D.natDegree - (R b).eval x₀ * (R a).coeff D.natDegree)
          / (R cI).leadingCoeff = 0 := by rw [sub_div, mul_div_assoc, mul_div_assoc, hall a b, sub_self]
       rcases div_eq_zero_iff.mp h2 with h3 | h3
       · exact sub_eq_zero.mp h3
       · exact absurd h3 hlc)
  have key := minor_eq_of_forall R (leval x₀) (lcoeff k D.natDegree)
    (fun a b => by simpa only [leval_apply, lcoeff_apply] using hall' a b) hD hD'
  simp only [leval_apply, lcoeff_apply] at key
  have hD'x : D'.eval x₀ ≠ 0 := by intro h0; apply hDx; rw [hDa, eval_mul, h0, mul_zero]
  have hD0 : D ≠ 0 := fun h => hDx (by rw [h, eval_zero])
  have hcD' : D'.coeff D.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hcD : D.coeff D.natDegree ≠ 0 := by
    rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hD0
  rw [hcD', mul_zero] at key
  exact mul_ne_zero hD'x hcD key.symm

theorem exists_nextToTop' {D D' : k[X]}
    (hD' : D' ∈ Submodule.span k (Set.range R)) (hD'0 : D' ≠ 0)
    (cI : Fin r) (hN : (R cI).natDegree = D.natDegree) (hcI0 : R cI ≠ 0)
    (hle : ∀ l, (R l).natDegree ≤ D.natDegree) (hdeg' : D'.natDegree + 1 = D.natDegree) :
    ∃ l, (R l - C ((R l).coeff (R cI).natDegree / (R cI).leadingCoeff) * R cI).natDegree + 1 = (R cI).natDegree ∧
      R l - C ((R l).coeff (R cI).natDegree / (R cI).leadingCoeff) * R cI ≠ 0 := by
  rw [hN]
  set N := D.natDegree with hNdef
  set lc := (R cI).leadingCoeff with hlcdef
  have hlc : lc ≠ 0 := leadingCoeff_ne_zero.mpr hcI0
  set ψ : k[X] → k[X] := fun Q => Q - C (Q.coeff N / lc) * R cI with hψ
  have htop : (R cI).coeff N = lc := by rw [hlcdef, ← coeff_natDegree, hN]
  have hψdeg : ∀ Q, Q.natDegree ≤ N → (ψ Q).degree < N := by
    intro Q hQ
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    simp only [hψ, coeff_sub, coeff_C_mul]
    rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h; rw [htop, div_mul_cancel₀ _ hlc, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ h),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_eq hN) h), mul_zero, sub_self]
  have hψsum : ∀ w : Fin r → k, ψ (∑ l, w l • R l) = ∑ l, w l • ψ (R l) := by
    intro w
    simp only [hψ, smul_eq_C_mul, finset_sum_coeff, coeff_C_mul, Finset.sum_div, map_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib, mul_sub, mul_div_assoc, map_mul, mul_assoc]
  by_contra hall
  push_neg at hall
  have hlt : ∀ l, ψ (R l) ∈ degreeLT k (N - 1) := by
    intro l
    rw [mem_degreeLT]
    by_cases h0 : ψ (R l) = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · have hd : (ψ (R l)).degree < N := hψdeg (R l) (hle l)
      rw [degree_eq_natDegree h0] at hd ⊢
      have hd' : (ψ (R l)).natDegree < N := by exact_mod_cast hd
      have hne : (ψ (R l)).natDegree + 1 ≠ N := fun h => h0 (hall l h)
      exact_mod_cast (show (ψ (R l)).natDegree < N - 1 by omega)
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hD'
  have hmem : ψ D' ∈ degreeLT k (N - 1) := by
    rw [← hw, hψsum]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hlt l)
  have hψD' : ψ D' = D' := by
    simp only [hψ]
    rw [coeff_eq_zero_of_natDegree_lt (by omega : D'.natDegree < N), zero_div, map_zero, zero_mul, sub_zero]
  rw [hψD', mem_degreeLT, degree_eq_natDegree hD'0] at hmem
  have : D'.natDegree < N - 1 := by exact_mod_cast hmem
  omega

end LineAlgebraWide

section PerA

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem redFst_eq_placeInfty_of_isCuspidal [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : Γ.P.IsCuspidal W) :
    Γ.P.redFst W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
  rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A) (Γ.P.redFst W) with ⟨c, hc⟩ | h
  · exact absurd hc (Γ.supply.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal hW c)
  · exact h

include Γ in

theorem placeInfty_ne_charLGeomPlaceOfPoint [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] (a : (IsLocalRing.ResidueField ↥A)) :
    charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) ≠ charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a := by
  intro h
  have hc : Γ.P.IsCuspidal (cuspInftyBar (1 * p)) := (Γ.supply.isInftySide_cuspInftyBar).1
  exact Γ.supply.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal hc a
    ((redFst_eq_placeInfty_of_isCuspidal Γ _ hc).trans h)

noncomputable def cusp0 (p : ℕ) [Fact p.Prime] : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) :=
  (frickeInvolutionBar (1 * p))⁻¹ • cuspInftyBar (1 * p)

theorem smul_cusp0 : frickeInvolutionBar (1 * p) • cusp0 p = cuspInftyBar (1 * p) := smul_inv_smul _ _

theorem cusp0_mem_dom : cusp0 p ∈ (zeroChart Γ).dom := by
  show frickeInvolutionBar (1 * p) • cusp0 p ∈ (infChart Γ).dom
  rw [smul_cusp0]
  exact cuspInftyBar_mem_infChart_dom Γ

theorem placeMap_cusp0 [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] :
    (zeroChart Γ).placeMap (cusp0 p) = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
  show Γ.P.redFst (frickeInvolutionBar (1 * p) • cusp0 p) = _
  rw [smul_cusp0]
  exact redFst_eq_placeInfty_of_isCuspidal Γ _ (Γ.supply.isInftySide_cuspInftyBar).1

theorem t_mem_place {r : ℕ} (Φ : FamCtx p r) (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hP : P ≠ cuspInftyBar (1 * p)) (l : Fin r) :
    Φ.t l ∈ P.toValuationSubring := by
  classical
  obtain ⟨-, hb⟩ := Φ.t_basis
  have ht : Φ.t l ∈ riemannRochSpace (embDivisor (1 * p)) := by
    rw [← hb]; exact Submodule.subset_span ⟨l, rfl⟩
  rcases (mem_riemannRochSpace_iff.mp ht) P with h0 | hord
  · rw [h0]; exact zero_mem _
  · have hD : embDivisor (1 * p) P = 0 := by
      unfold embDivisor
      rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hP), smul_zero]
    rw [hD, neg_zero] at hord
    by_cases h0 : Φ.t l = 0
    · rw [h0]; exact zero_mem _
    · exact P.mem_of_ord_nonneg h0 hord

theorem goodFamilyZero_mem_place {r : ℕ} (Φ : FamCtx p r) (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hP : P ≠ cuspInftyBar (1 * p))
    (l : Fin r) : goodFamilyZero Φ.toFamData l ∈ P.toValuationSubring := by
  unfold goodFamilyZero
  refine mul_mem ?_ (t_mem_place Φ P hP l)
  rw [← _root_.map_inv₀]
  have hne : ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  exact P.mem_of_ord_nonneg ((_root_.map_ne_zero _).mpr hne) (le_of_eq (Place.ord_algebraMap P _).symm)

noncomputable def ssPolZ : Polynomial (IsLocalRing.ResidueField ↥A) := ∏ e : Fin (mAnnuli p), (X - C (ssValue Γ e ^ p))

theorem ssPolZ_monic : (ssPolZ Γ).Monic := by
  unfold ssPolZ; exact monic_prod_of_monic _ _ fun e _ => monic_X_sub_C _

theorem ssPolZ_natDegree : (ssPolZ Γ).natDegree = mAnnuli p := by
  unfold ssPolZ
  rw [natDegree_prod_of_monic _ _ fun e _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem ssPolZ_eval (x : (IsLocalRing.ResidueField ↥A)) : (ssPolZ Γ).eval x = ∏ e : Fin (mAnnuli p), (x - ssValue Γ e ^ p) := by
  unfold ssPolZ; rw [eval_prod]; simp only [eval_sub, eval_X, eval_C]

theorem aeval_ssPolZ : aeval (jBar (IsLocalRing.ResidueField ↥A)) (ssPolZ Γ) = ssPolyBarZero Γ := by
  unfold ssPolZ ssPolyBarZero
  rw [_root_.map_prod]
  simp only [_root_.map_sub, aeval_X, aeval_C]

theorem eval_ne_zero_of_placeMap_eq {P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))} (hP : P ∈ (zeroChart Γ).dom) {x₀ : (IsLocalRing.ResidueField ↥A)}
    (hx : (zeroChart Γ).placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀) : (ssPolZ Γ).eval x₀ ≠ 0 := by
  rw [ssPolZ_eval, Finset.prod_ne_zero_iff]
  intro e _ he
  apply (zeroChart Γ).placeMap_not_mem_nodes P hP
  rw [hx, mem_zeroChart_nodes_iff]
  exact ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, by rw [sub_eq_zero.mp he]⟩

end PerA

theorem mapDomain_filter_apply_congr {α β M : Type*} [AddCommMonoid M] (g : α → β) (E : α →₀ M) (b : β)
    (P Q : α → Prop) {decP : DecidablePred P} {decQ : DecidablePred Q} (hPQ : ∀ a, g a = b → (P a ↔ Q a)) :
    Finsupp.mapDomain g (E.filter P) b = Finsupp.mapDomain g (E.filter Q) b := by
  classical
  refine Finsupp.induction_linear E ?_ (fun f₁ f₂ h₁ h₂ => ?_) (fun a n => ?_)
  · simp only [Finsupp.filter_zero, Finsupp.mapDomain_zero]
  · simp only [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply, h₁, h₂]
  · have key := hPQ a
    by_cases hP : P a <;> by_cases hQ : Q a <;> by_cases hg : g a = b <;>
      simp_all [Finsupp.mapDomain_single, Finsupp.single_apply]

section WideTools

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ord_pt_jBar_sub (x c : (IsLocalRing.ResidueField ↥A)) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = if c = x then 1 else 0 :=
  ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (IsLocalRing.ResidueField ↥A) x c

theorem aeval_jBar_eq_zero {Q : Polynomial (IsLocalRing.ResidueField ↥A)} (h : aeval (jBar (IsLocalRing.ResidueField ↥A)) Q = 0) : Q = 0 := by
  by_contra hQ
  have e : aeval (jqModC (IsLocalRing.ResidueField ↥A)) Q = (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val (aeval (jBar (IsLocalRing.ResidueField ↥A)) Q) :=
    Polynomial.aeval_algHom_apply (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val (jBar (IsLocalRing.ResidueField ↥A)) Q
  rw [h, _root_.map_zero] at e
  exact ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField ↥A) ⟨Q, hQ, e⟩

theorem aeval_jBar_injective' {Q₁ Q₂ : Polynomial (IsLocalRing.ResidueField ↥A)} (h : aeval (jBar (IsLocalRing.ResidueField ↥A)) Q₁ = aeval (jBar (IsLocalRing.ResidueField ↥A)) Q₂) :
    Q₁ = Q₂ :=
  sub_eq_zero.mp (aeval_jBar_eq_zero (by rw [_root_.map_sub, h, sub_self]))

theorem ord_placeInfty_jBar_sub [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] (c : (IsLocalRing.ResidueField ↥A)) :
    (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = -1 := by
  set v := charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) with hv
  have hJ : v.ord (jBar (IsLocalRing.ResidueField ↥A)) = -1 := ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC (IsLocalRing.ResidueField ↥A)
  by_cases hc : c = 0
  · rw [hc, _root_.map_zero, sub_zero]; exact hJ
  have hC0 : algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hCord : v.ord (algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = 0 := Place.ord_algebraMap v c
  have hnC : v.ord (-algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = 0 := by
    rw [← _root_.map_neg]; exact Place.ord_algebraMap v (-c)
  have hJ0 : jBar (IsLocalRing.ResidueField ↥A) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hJ; norm_num at hJ
  have hsub0 : jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c ≠ 0 := by
    intro h0
    have : v.ord (jBar (IsLocalRing.ResidueField ↥A)) = 0 := by rw [sub_eq_zero.mp h0]; exact hCord
    rw [hJ] at this; norm_num at this

  have h1 := Place.min_ord_le_ord_add v hJ0 ((neg_ne_zero).mpr hC0) (by rw [← sub_eq_add_neg]; exact hsub0)
  rw [← sub_eq_add_neg, hJ, hnC] at h1

  have h2 := Place.min_ord_le_ord_add v hsub0 hC0 (by rw [sub_add_cancel]; exact hJ0)
  rw [sub_add_cancel, hJ, hCord] at h2
  omega

include Γ in

theorem exists_ssValue_ne [IsAlgClosed (IsLocalRing.ResidueField ↥A)] (hp13 : 13 ≤ p) :
    ∃ e : Fin (mAnnuli p), ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728 := by
  classical
  by_contra hall
  push_neg at hall
  have hinj := ssValue_injective Γ
  set f0 : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun e => ssValue Γ e = 0) with hf0
  set f1 : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun e => ssValue Γ e = 1728) with hf1
  have hcov : (Finset.univ : Finset (Fin (mAnnuli p))) ⊆ f0 ∪ f1 := by
    intro e _
    rw [Finset.mem_union, hf0, hf1, Finset.mem_filter, Finset.mem_filter]
    by_cases h0 : ssValue Γ e = 0
    · exact Or.inl ⟨Finset.mem_univ _, h0⟩
    · exact Or.inr ⟨Finset.mem_univ _, hall e h0⟩
  have h0card : f0.card ≤ (if p % 3 = 2 then 1 else 0) := by
    split_ifs with h3
    · refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      rw [hf0, Finset.mem_filter] at ha hb
      exact hinj (ha.2.trans hb.2.symm)
    · rw [Nat.le_zero, Finset.card_eq_zero, hf0, Finset.filter_eq_empty_iff]
      intro e _ he
      have hmem : (0 : (IsLocalRing.ResidueField ↥A)) ∈ ssJSet p (IsLocalRing.ResidueField ↥A) := by rw [← he]; exact ssValue_mem_ssJSet Γ e
      exact h3 ((ModularCurve.zero_mem_ssJSet_iff p (by omega) (IsLocalRing.ResidueField ↥A)).mp hmem)
  have h1card : f1.card ≤ (if p % 4 = 3 then 1 else 0) := by
    split_ifs with h4
    · refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      rw [hf1, Finset.mem_filter] at ha hb
      exact hinj (ha.2.trans hb.2.symm)
    · rw [Nat.le_zero, Finset.card_eq_zero, hf1, Finset.filter_eq_empty_iff]
      intro e _ he
      have hmem : (1728 : (IsLocalRing.ResidueField ↥A)) ∈ ssJSet p (IsLocalRing.ResidueField ↥A) := by rw [← he]; exact ssValue_mem_ssJSet Γ e
      exact h4 ((ModularCurve.ofNat1728_mem_ssJSet_iff p (by omega) (IsLocalRing.ResidueField ↥A)).mp hmem)
  have hle : mAnnuli p ≤ f0.card + f1.card := by
    calc mAnnuli p = (Finset.univ : Finset (Fin (mAnnuli p))).card := by simp
      _ ≤ (f0 ∪ f1).card := Finset.card_le_card hcov
      _ ≤ f0.card + f1.card := Finset.card_union_le _ _
  have hp12 : 1 ≤ p / 12 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hfin : mAnnuli p ≤ (if p % 3 = 2 then 1 else 0) + (if p % 4 = 3 then 1 else 0) :=
    hle.trans (add_le_add h0card h1card)
  unfold mAnnuli at hfin
  split_ifs at hfin <;> omega

noncomputable def polD (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) : Polynomial (IsLocalRing.ResidueField ↥A) := ∏ a ∈ S₀, (X - C a) ^ m a

noncomputable def polD' (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) (a₁ : (IsLocalRing.ResidueField ↥A)) : Polynomial (IsLocalRing.ResidueField ↥A) :=
  (X - C a₁) ^ (m a₁ - 1) * ∏ a ∈ S₀.erase a₁, (X - C a) ^ m a

theorem polD_monic (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) : (polD S₀ m).Monic := by
  unfold polD; exact monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow _

theorem polD'_monic (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) (a₁ : (IsLocalRing.ResidueField ↥A)) : (polD' S₀ m a₁).Monic := by
  unfold polD'; exact ((monic_X_sub_C a₁).pow _).mul (monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow _)

theorem polD_natDegree (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) : (polD S₀ m).natDegree = ∑ a ∈ S₀, m a := by
  unfold polD
  rw [natDegree_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow _]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one]

theorem polD_eval (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) (x : (IsLocalRing.ResidueField ↥A)) :
    (polD S₀ m).eval x = ∏ a ∈ S₀, (x - a) ^ m a := by
  unfold polD; rw [eval_prod]; simp only [eval_pow, eval_sub, eval_X, eval_C]

theorem polD_eval_ne_zero (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) {x : (IsLocalRing.ResidueField ↥A)} (hx : x ∉ S₀) :
    (polD S₀ m).eval x ≠ 0 := by
  rw [polD_eval, Finset.prod_ne_zero_iff]
  intro a ha
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hx (h ▸ ha)))

theorem polD_eq_mul (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) {a₁ : (IsLocalRing.ResidueField ↥A)} (ha₁ : a₁ ∈ S₀) (hm : 1 ≤ m a₁) :
    polD S₀ m = (X - C a₁) * polD' S₀ m a₁ := by
  unfold polD polD'
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]
  exact (Finset.mul_prod_erase S₀ (fun a => (X - C a) ^ m a) ha₁).symm

theorem aeval_polD (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (m : (IsLocalRing.ResidueField ↥A) → ℕ) :
    aeval (jBar (IsLocalRing.ResidueField ↥A)) (polD S₀ m) = ∏ a ∈ S₀, (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) a) ^ m a := by
  unfold polD
  rw [_root_.map_prod]
  simp only [_root_.map_pow, _root_.map_sub, aeval_X, aeval_C]

end WideTools

set_option maxHeartbeats 6400000 in
theorem zeroChart_chartData_wide (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∃ (hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (zeroChart Γ).dom, P.IsRational ∧ ((zeroChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)), hint _⟩
          ≠ 0) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ (zeroChart Γ).integers) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((zeroChart Γ).placeMap P))
            * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
              ∈ (zeroChart Γ).integers,
        ((zeroChart Γ).placeMap P).ord ((zeroChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (zeroChart Γ).placeMap P ≠ (zeroChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
                ∈ (zeroChart Γ).integers)
          (hmQ : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap Q)))⁻¹
                ∈ (zeroChart Γ).integers),
        ∃ i j, ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP i⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP j⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ i⟩)) := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  obtain ⟨Δ⟩ := ModularCurve.MultCovering.nonempty_annCtx p (by omega) A Γ
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  have hFrat : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), P.IsRational := fun P =>
    (Place.isRational_iff_deg_eq_one P).mpr (deg_eq_one_modularFunctionFieldBar (1 * p) P)
  have hunit : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ ≠ 0 := fun l => hLI.ne_zero l

  obtain ⟨hint', hZ3⟩ := zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes p A hA Γ Φ
  have hZ3' : ∀ (l : Fin r) (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)), v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) :=
    fun l v hv => hZ3 l v hv
  have hnodeInf : charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) ∉ (zeroChart Γ).nodes := by
    intro h
    obtain ⟨a, -, ha⟩ := (mem_zeroChart_nodes_iff Γ _).mp h
    exact placeInfty_ne_charLGeomPlaceOfPoint Γ (a ^ p) ha.symm

  have hreg : ∀ P ∈ (zeroChart Γ).dom, ∀ l, goodFamilyZero Φ.toFamData l ∈ P.toValuationSubring :=
    fun P hP l => goodFamilyZero_mem_place Φ P
      (fun h => cuspInftyBar_not_mem_zeroChart_dom Γ (by rw [← h]; exact hP)) l

  obtain ⟨S₀, hS₀⟩ : ∃ S : Finset (IsLocalRing.ResidueField ↥A), S = Finset.univ.image (fun e : Fin (mAnnuli p) => ssValue Γ e ^ p) :=
    ⟨_, rfl⟩
  have hS₀node : ∀ x : (IsLocalRing.ResidueField ↥A), x ∈ S₀ ↔ charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x ∈ (zeroChart Γ).nodes := by
    intro x
    rw [mem_zeroChart_nodes_iff, hS₀, Finset.mem_image]
    constructor
    · rintro ⟨e, -, rfl⟩
      exact ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, rfl⟩
    · rintro ⟨a, ha, hax⟩
      obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
      exact ⟨e, Finset.mem_univ _, by rw [he]; exact charLGeomPlaceOfPoint_injective (IsLocalRing.ResidueField ↥A) hax⟩
  obtain ⟨m, hm1, hmord⟩ : ∃ m : (IsLocalRing.ResidueField ↥A) → ℕ, (∀ a, 1 ≤ m a) ∧
      ∀ a l, -((m a : ℕ) : ℤ) ≤ (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
    refine ⟨fun a => max 1 (Finset.univ.sup fun l : Fin r => (-(charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)).toNat),
      fun a => le_max_left _ _, fun a l => ?_⟩
    have h1 : (-(charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)).toNat
        ≤ max 1 (Finset.univ.sup fun l : Fin r => (-(charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)).toNat) :=
      le_max_of_le_right (Finset.le_sup
        (f := fun l : Fin r => (-(charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)).toNat) (Finset.mem_univ l))
    have h2 : -((charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
        ≤ ((max 1 (Finset.univ.sup fun l : Fin r => (-(charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)).toNat) : ℕ) : ℤ) :=
      (Int.self_le_toNat _).trans (by exact_mod_cast h1)
    beta_reduce
    omega
  obtain ⟨D, hDdef⟩ : ∃ D : Polynomial (IsLocalRing.ResidueField ↥A), D = polD S₀ m := ⟨_, rfl⟩
  have hDmon : D.Monic := by rw [hDdef]; exact polD_monic S₀ m
  have hD0 : D ≠ 0 := hDmon.ne_zero
  have hDdeg : D.natDegree = ∑ a ∈ S₀, m a := by rw [hDdef, polD_natDegree]
  have hDaeval : aeval (jBar (IsLocalRing.ResidueField ↥A)) D = ∏ a ∈ S₀, (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) a) ^ m a := by rw [hDdef, aeval_polD]
  have hDx : ∀ P ∈ (zeroChart Γ).dom, ∀ x₀ : (IsLocalRing.ResidueField ↥A), (zeroChart Γ).placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      D.eval x₀ ≠ 0 := by
    intro P hP x₀ hx
    rw [hDdef]
    refine polD_eval_ne_zero S₀ m (fun hmem => ?_)
    exact (zeroChart Γ).placeMap_not_mem_nodes P hP (hx ▸ (hS₀node x₀).mp hmem)

  have hpres : ∀ l, ∃ Q : Polynomial (IsLocalRing.ResidueField ↥A), (Q ≠ 0 → Q.natDegree ≤ 0 + ∑ a ∈ S₀, m a) ∧
      (∏ a ∈ S₀, ((⟨jqModC (IsLocalRing.ResidueField ↥A), jqModC_mem (IsLocalRing.ResidueField ↥A) 1⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) a) ^ m a) * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩
        = Polynomial.aeval (⟨jqModC (IsLocalRing.ResidueField ↥A), jqModC_mem (IsLocalRing.ResidueField ↥A) 1⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) Q := by
    intro l
    refine ModularCurve.exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord S₀ m 0 ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)
      (fun b hb => hZ3' l _ (fun hn => hb ((hS₀node b).mpr hn))) (fun a _ => hmord a l) ?_
    rw [Nat.cast_zero, neg_zero]
    exact hZ3' l _ hnodeInf
  choose R hRdeg hReq using hpres
  have hR' : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ * aeval (jBar (IsLocalRing.ResidueField ↥A)) D = aeval (jBar (IsLocalRing.ResidueField ↥A)) (R l) := by
    intro l; rw [hDaeval]; exact (mul_comm _ _).trans (hReq l)
  have hR0 : ∀ l, R l ≠ 0 := by
    intro l h0
    have h := hR' l
    rw [h0, _root_.map_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact hunit l h
    · exact hD0 (aeval_jBar_eq_zero h)
  have hRle : ∀ l, (R l).natDegree ≤ D.natDegree := fun l => by
    rw [hDdeg, ← zero_add (∑ a ∈ S₀, m a)]; exact hRdeg l (hR0 l)

  have hexp : ∀ (c : Fin r → (IsLocalRing.ResidueField ↥A)) (G : Polynomial (IsLocalRing.ResidueField ↥A)),
      (∑ l, c l • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) * aeval (jBar (IsLocalRing.ResidueField ↥A)) D = aeval (jBar (IsLocalRing.ResidueField ↥A)) G →
        G ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range R) := by
    intro c G hG
    have hsum : aeval (jBar (IsLocalRing.ResidueField ↥A)) (∑ l, c l • R l) = aeval (jBar (IsLocalRing.ResidueField ↥A)) G := by
      rw [← hG, Finset.sum_mul, _root_.map_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [smul_eq_C_mul, _root_.map_mul, aeval_C, ← hR' l, Algebra.smul_def, mul_assoc]
    rw [← aeval_jBar_injective' hsum]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

  have h1span : (1 : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) :=
    mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge p (by omega) A hA Γ Δ Φ hint hLI 1
      (fun v _ => by rw [Place.ord_one])
      (fun e => by rw [Place.ord_one]; exact neg_nonpos.mpr (Int.natCast_nonneg _))
  obtain ⟨c1, hc1⟩ := (Submodule.mem_span_range_iff_exists_fun (IsLocalRing.ResidueField ↥A)).mp h1span
  have hDspan : D ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range R) := hexp c1 D (by rw [hc1, one_mul])
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hc1
    · exact h
  obtain ⟨l₀, -⟩ : ∃ l₀ : Fin r, True := ⟨⟨0, hr⟩, trivial⟩

  obtain ⟨e₁, he₁0, he₁1728⟩ := exists_ssValue_ne Γ hp13
  obtain ⟨a₁, ha₁def⟩ : ∃ a : (IsLocalRing.ResidueField ↥A), a = ssValue Γ e₁ ^ p := ⟨_, rfl⟩
  have ha₁ : a₁ ∈ S₀ := by rw [hS₀, Finset.mem_image]; exact ⟨e₁, Finset.mem_univ _, ha₁def.symm⟩
  have ha₁node : charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a₁ ∈ (zeroChart Γ).nodes := (hS₀node a₁).mp ha₁
  obtain ⟨D', hD'def⟩ : ∃ D' : Polynomial (IsLocalRing.ResidueField ↥A), D' = polD' S₀ m a₁ := ⟨_, rfl⟩
  have hDa : D = (X - C a₁) * D' := by rw [hDdef, hD'def]; exact polD_eq_mul S₀ m ha₁ (hm1 a₁)
  have hD'0 : D' ≠ 0 := by rw [hD'def]; exact (polD'_monic S₀ m a₁).ne_zero
  have hdeg' : D'.natDegree + 1 = D.natDegree := by
    rw [hDa, natDegree_mul (X_sub_C_ne_zero a₁) hD'0, natDegree_X_sub_C]; omega
  obtain ⟨g, hgdef⟩ : ∃ g : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1), g = (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) a₁)⁻¹ := ⟨_, rfl⟩
  have hJa0 : jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) a₁ ≠ 0 := by
    intro h0
    have : aeval (jBar (IsLocalRing.ResidueField ↥A)) (X - C a₁) = 0 := by rw [_root_.map_sub, aeval_X, aeval_C, h0]
    exact X_sub_C_ne_zero a₁ (aeval_jBar_eq_zero this)
  have hordg : ∀ x : (IsLocalRing.ResidueField ↥A), (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord g = -(if a₁ = x then 1 else 0) := by
    intro x
    rw [hgdef, Place.ord_inv, ord_pt_jBar_sub]
  have hgspan : g ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
    refine mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge p (by omega) A hA Γ Δ Φ hint hLI g ?_ ?_
    · intro v hv
      rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A) v with ⟨x, rfl⟩ | rfl
      · rw [hordg]
        by_cases hx : a₁ = x
        · exact absurd (hx ▸ ha₁node) hv
        · simp only [if_neg hx, neg_zero, le_refl]
      · rw [hgdef, Place.ord_inv, ord_placeInfty_jBar_sub]; norm_num
    · intro e
      show _ ≤ (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p)).ord g
      rw [hordg]
      by_cases hx : a₁ = ssValue Γ e ^ p
      · rw [if_pos hx]
        have hee : ssValue Γ e₁ = ssValue Γ e := by
          have hx' : ssValue Γ e₁ ^ p = ssValue Γ e ^ p := by rw [← ha₁def]; exact hx
          have h0 : (ssValue Γ e₁ - ssValue Γ e) ^ p = 0 := by rw [sub_pow_char, hx', sub_self]
          exact sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp h0)
        rw [← hee, jWidth_of_ne he₁0 he₁1728]; norm_num
      · rw [if_neg hx, neg_zero]; exact neg_nonpos.mpr (Int.natCast_nonneg _)
  obtain ⟨cg, hcg⟩ := (Submodule.mem_span_range_iff_exists_fun (IsLocalRing.ResidueField ↥A)).mp hgspan
  have hD'span : D' ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range R) := by
    refine hexp cg D' ?_
    rw [hcg, hgdef]
    have : aeval (jBar (IsLocalRing.ResidueField ↥A)) D = (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) a₁) * aeval (jBar (IsLocalRing.ResidueField ↥A)) D' := by
      rw [hDa, _root_.map_mul, _root_.map_sub, aeval_X, aeval_C]
    rw [this, ← mul_assoc, inv_mul_cancel₀ hJa0, one_mul]

  have hc_ex : ∀ x₀ : (IsLocalRing.ResidueField ↥A), ∃ l : Fin r, (D.eval x₀ ≠ 0 → (R l).eval x₀ ≠ 0) := by
    intro x₀
    by_cases hx : D.eval x₀ ≠ 0
    · obtain ⟨l, hl⟩ := exists_eval_ne_zero' R hDspan x₀ hx
      exact ⟨l, fun _ => hl⟩
    · exact ⟨l₀, fun h => absurd h hx⟩
  choose cFun hcFun using hc_ex
  have hi_ex : ∀ x₀ : (IsLocalRing.ResidueField ↥A), ∃ l : Fin r, (D.eval x₀ ≠ 0 →
      (R l * C ((R (cFun x₀)).eval x₀) - R (cFun x₀) * C ((R l).eval x₀)).rootMultiplicity x₀ = 1) := by
    intro x₀
    by_cases hx : D.eval x₀ ≠ 0
    · obtain ⟨l, hl⟩ := exists_rootMultiplicity_eq_one' R hDa hDspan hD'span x₀ hx (cFun x₀) (hcFun x₀ hx)
      exact ⟨l, fun _ => hl⟩
    · exact ⟨l₀, fun h => absurd h hx⟩
  choose iFun hiFun using hi_ex
  obtain ⟨cI, hcI⟩ := exists_natDegree_eq' R hDspan hD0 hRle
  obtain ⟨iInf, hiInf, hiInf0⟩ := exists_nextToTop' R hD'span hD'0 cI hcI (hR0 cI) hRle hdeg'
  have hcInf : ∀ l, (R l).natDegree ≤ (R cI).natDegree := fun l => by rw [hcI]; exact hRle l
  have hpole : ∀ l, -(((R cI).natDegree - D.natDegree : ℕ) : ℤ) ≤ (cusp0 p).ord (goodFamilyZero Φ.toFamData l) :=
    fun l => (neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      (Place.ord_nonneg_of_mem _ (hreg _ (cusp0_mem_dom Γ) l))

  obtain ⟨cQ, iQ, h1, h2, h3, h4, h5, h6, -⟩ :=
    ModularCurve.exists_chartData_of_lineResidues hFrat (zeroChart Γ) (goodFamilyZero Φ.toFamData) hint hunit
      D R hD0 hR' (cusp0 p) (cusp0_mem_dom Γ) (placeMap_cusp0 Γ)
      (fun P hP _ l => hreg P hP l)
      (by
        intro P hP
        rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A)
            ((zeroChart Γ).placeMap P) with ⟨x₀, hx⟩ | h
        · exact Or.inl ⟨x₀, hx, hDx P hP x₀ hx⟩
        · exact Or.inr h)
      (by
        intro f hf hres E hE
        refine (mapDomain_filter_apply_congr (zeroChart Γ).placeMap E _ _ (fun W => W ∈ (zeroChart Γ).dom)
          (decQ := Classical.decPred _) (fun a ha => ⟨fun h => h.1, fun h => ⟨h, ha⟩⟩)).trans ?_
        exact (zeroChart Γ).mapDomain_placeMap ⟨f, hf⟩ hres _
          (fun P hP => by simp only [Finsupp.filter_apply, if_pos hP, hE])
          (fun P hP => by simp only [Finsupp.filter_apply, if_neg hP]) _ hnodeInf)
      cFun iFun Finset.univ
      (fun P hP x₀ hx => hcFun x₀ (hDx P hP x₀ hx))
      (fun P hP x₀ hx => hiFun x₀ (hDx P hP x₀ hx))
      (fun P hP Q hQ x₀ y₀ hx hy hxy =>
        exists_eval_minor_ne' R hDa hDspan hD'span x₀ y₀ (hDx P hP x₀ hx) (hDx Q hQ y₀ hy) hxy)
      (fun P hP x₀ hx => ⟨cFun x₀, Finset.mem_univ _, hcFun x₀ (hDx P hP x₀ hx)⟩)
      cI iInf hcInf (le_of_eq hcI.symm) (Finset.mem_univ _) hpole hiInf hiInf0
      (fun P hP x₀ hx => exists_eval_coeff_minor_ne' R hDa hDspan hD'span cI hcI
        (leadingCoeff_ne_zero.mpr (hR0 cI)) hdeg' x₀ (hDx P hP x₀ hx))
  exact ⟨hint, cQ, iQ, h1, h2, h3, h4, h5, h6⟩

end ModularCurve.MultCovering.P2Mcdw

open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent.ModularCurve.MultCovering in
theorem solution (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∃ (hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (zeroChart Γ).dom, P.IsRational ∧ ((zeroChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)), hint _⟩
          ≠ 0) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ (zeroChart Γ).integers) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((zeroChart Γ).placeMap P))
            * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
              ∈ (zeroChart Γ).integers,
        ((zeroChart Γ).placeMap P).ord ((zeroChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (zeroChart Γ).placeMap P ≠ (zeroChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
                ∈ (zeroChart Γ).integers)
          (hmQ : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap Q)))⁻¹
                ∈ (zeroChart Γ).integers),
        ∃ i j, ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP i⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP j⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ i⟩)) :=
  ModularCurve.MultCovering.P2Mcdw.zeroChart_chartData_wide p hp13 A hA Γ Φ hint hLI

end S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent
end P2MW
export P2MW.S_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent (solution)
