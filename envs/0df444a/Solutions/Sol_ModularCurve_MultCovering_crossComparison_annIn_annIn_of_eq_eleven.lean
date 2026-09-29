-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_annIn_annIn_of_eq_eleven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e1440d49-e909-52be-9cab-9a3a0d441a76

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_exists_famCtx_orth_linearIndependent_zeroChart_residue
import Theorems.Thm_ModularCurve_MultCovering_compConst_eq_compConst
import Theorems.Thm_ModularCurve_MultCovering_nonempty_chartCtx
import Theorems.Thm_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered
import Theorems.Thm_ModularCurve_MultCovering_forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_outer_of_lt_hasseExp
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates_of_eq_eleven
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_eq_eleven
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁"
p2m_attr_erase "instance" "instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.LevelOnePhi.instAddCommGroup ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_eq_eleven.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_eq_eleven.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar ssJSet deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue MultCovering.compConst_eq_compConst MultCovering.nonempty_chartCtx MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer_of_lt_hasseExp zero_mem_ssJSet_iff ofNat1728_mem_ssJSet_iff MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue exists_ssValue_eq nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_famCtx_orth_linearIndependent_zeroChart_residue compConst_eq_compConst nonempty_chartCtx exists_famCtx_toFamData_eq_of_bifiltered forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer_of_lt_hasseExp exists_unimodular_famData_wideCertificates_of_eq_eleven"
p2m_open "ModularCurve.MultCovering ModularCurve"

open AlgebraicCurve IsLocalRing

section GenericHelpers

theorem evalAt_mul_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_algebraMap_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

theorem chart_isUnit_of_residue_ne_zero_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

theorem vs_inv_mem_of_isUnit_D {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

theorem chart_residue_inv_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

theorem ord_eq_zero_of_evalAt_ne_zero_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h' | h'
    · simp [h']
    · exact h'
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne h0 (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem abv_lt_one_of_mem_maximalIdeal_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {m : ↥A} (hm : m ∈ IsLocalRing.maximalIdeal ↥A) : μ (m : AlgebraicClosure ℚ) < 1 := by
  have hle : μ (m : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 m.2
  refine lt_of_le_of_ne hle fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have hm0 : (m : AlgebraicClosure ℚ) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hinv : (m : AlgebraicClosure ℚ)⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0)⟩

theorem isRational_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (h : v.deg = 1) :
    v.IsRational := by
  intro x
  have h1 : Module.finrank K v.ResidueField = 1 := h
  have htop : (⊥ : Subalgebra K v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by rw [htop]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

theorem isRational_modularFunctionFieldBar {p : ℕ} [Fact p.Prime] (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :
    v.IsRational :=
  isRational_of_deg_eq_one v (ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * p) v)

theorem minor_mulVec_D {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) (i j : Fin r) :
    M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i
      = ∑ p : Fin r × Fin r, M i p.1 * M j p.2 * (x p.1 * y p.2 - x p.2 * y p.1) := by
  have hswap : ∑ p : Fin r × Fin r, M j p.1 * x p.1 * (M i p.2 * y p.2)
      = ∑ p : Fin r × Fin r, M j p.2 * x p.2 * (M i p.1 * y p.1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end GenericHelpers

section MoreHelpers

theorem evalAt_sub_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_add_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem mem_maximalIdeal_of_abv_lt_one_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : μ x < 1) : (⟨x, hx⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h0
    have : (u : ↥A) = 0 := by rw [hu]; exact Subtype.ext h0
    exact u.ne_zero this
  have hinv : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = x⁻¹ := by
    have h1 := congrArg (fun t : ↥A => (t : AlgebraicClosure ℚ)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hxinv : μ x⁻¹ ≤ 1 := (hμA _).1 (hinv ▸ ((u⁻¹ : (↥A)ˣ) : ↥A).2)
  rw [map_inv₀] at hxinv
  have : 1 < (μ x)⁻¹ := (one_lt_inv₀ (μ.pos hx0)).2 h
  linarith

theorem chart_residue_algebraMap_eq_zero_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (h : algebraMap L F a ∈ C.integers) : C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have e1 : (⟨algebraMap L F a, h⟩ : C.integers) = ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ := rfl
  rw [e1, C.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]

end MoreHelpers

section FamilyFacts
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)

theorem goodFamily_ne_zero' (i : Fin r) : goodFamily Φ i ≠ 0 := Φ.t_basis.1.ne_zero i

theorem goodFamily_mem_riemannRochSpace' (i : Fin r) : goodFamily Φ i ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← Φ.t_basis.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem goodFamilyZero_eq_inv_mul' (l : Fin r) :
    goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * goodFamily Φ l := rfl

theorem goodFamily_mem_of_ne_cuspInftyBar'
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hw : w ≠ cuspInftyBar (1 * p)) (i : Fin r) :
    0 ≤ w.ord (goodFamily Φ i) ∧ goodFamily Φ i ∈ w.toValuationSubring := by
  have h0 : goodFamily Φ i ≠ 0 := goodFamily_ne_zero' Φ i
  have hmem := (mem_riemannRochSpace_iff.mp (goodFamily_mem_riemannRochSpace' Φ i)) w
  have hD : (embDivisor (1 * p)) w = 0 := by simp [embDivisor, hw]
  rcases hmem with h' | h'
  · exact absurd h' h0
  · rw [hD, neg_zero] at h'
    exact ⟨h', w.mem_of_ord_nonneg h0 h'⟩

end FamilyFacts

section CtxFacts
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
  (Γ : ChartCtx p A) (Δ : AnnCtx Γ)

theorem modulus_dvd' (e : Fin (mAnnuli p)) : ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    (p : AlgebraicClosure ℚ) ^ modulusExp = ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * a := by
  have hw : jWidth (ssValue Γ e) ≤ 3 := by
    unfold jWidth; split_ifs <;> norm_num
  refine ⟨(p : AlgebraicClosure ℚ) ^ (3 - jWidth (ssValue Γ e)), pow_mem (natCast_mem A p) _, ?_⟩
  have hm : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  rw [hm, ← pow_add, show modulusExp = 3 from rfl, Nat.add_sub_cancel' hw]

end CtxFacts

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar ssJSet deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue MultCovering.compConst_eq_compConst MultCovering.nonempty_chartCtx MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer_of_lt_hasseExp zero_mem_ssJSet_iff ofNat1728_mem_ssJSet_iff MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue exists_ssValue_eq nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_famCtx_orth_linearIndependent_zeroChart_residue compConst_eq_compConst nonempty_chartCtx exists_famCtx_toFamData_eq_of_bifiltered forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer_of_lt_hasseExp exists_unimodular_famData_wideCertificates_of_eq_eleven"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

theorem annOut_wide' (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
        μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  intro μ hμA
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := Δ.exists_mem_dom_abv_evalAt_param_ne e μ hμA
  refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
  have key : ∀ Q ∈ (Δ.annIn e).dom,
      μ (Q.evalAt (Δ.annOut e).param) * μ (Q.evalAt (Δ.annIn e).param)
        = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) := by
    intro Q hQ
    obtain ⟨hrat, hzin, -, hz0, -⟩ := (Δ.annIn e).mem_dom Q hQ
    obtain ⟨-, hzout, -⟩ := (Δ.annOut e).mem_dom Q (hdom ▸ hQ)
    rw [← map_mul, ← evalAt_mul_D Q hrat hzout hzin, htwo, evalAt_algebraMap_D]
  intro heq
  apply hne
  have h1 := key Q₁ hQ₁
  have h2 := key Q₂ hQ₂
  rw [heq] at h1
  have h12 := h1.trans h2.symm
  have hne0 : μ (Q₂.evalAt (Δ.annOut e).param) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (μ.pos hmod0).ne' h2.symm
  exact mul_left_cancel₀ hne0 h12

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar ssJSet deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue MultCovering.compConst_eq_compConst MultCovering.nonempty_chartCtx MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer_of_lt_hasseExp zero_mem_ssJSet_iff ofNat1728_mem_ssJSet_iff MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue exists_ssValue_eq nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_famCtx_orth_linearIndependent_zeroChart_residue compConst_eq_compConst nonempty_chartCtx exists_famCtx_toFamData_eq_of_bifiltered forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer_of_lt_hasseExp exists_unimodular_famData_wideCertificates_of_eq_eleven"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

section P2Helpers

theorem abv_sub_eq_max_of_ne_D {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {a b : K} (h : μ a ≠ μ b) : μ (a - b) = max (μ a) (μ b) := by
  have hsub : ∀ u v : K, μ (u - v) ≤ max (μ u) (μ v) := by
    intro u v; rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ v]; exact hμ _ _
  refine le_antisymm (hsub a b) ?_
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [max_eq_right hlt.le]
    have h1 := hμ (b - a) a
    rw [sub_add_cancel] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · rw [← neg_sub, AbsoluteValue.map_neg] at h2; exact h2
    · exact absurd h2 (not_le.2 hlt)
  · rw [max_eq_left hlt.le]
    have h1 := hμ (a - b) b
    rw [sub_add_cancel] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 hlt)

theorem abv_sub_le_max_D {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (a b : K) : μ (a - b) ≤ max (μ a) (μ b) := by
  rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ b]; exact hμ _ _

theorem abv_eq_one_of_isUnit_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (hu : IsUnit (⟨x, hx⟩ : ↥A)) : μ x = 1 := by
  refine le_antisymm ((hμA x).1 hx) ?_
  have hinv : x⁻¹ ∈ A := vs_inv_mem_of_isUnit_D hx hu
  have hx0 : x ≠ 0 := by
    intro h0; obtain ⟨u, hu'⟩ := hu
    have : (u : ↥A) = 0 := by rw [hu']; exact Subtype.ext h0
    exact u.ne_zero this
  have h1 : μ x⁻¹ ≤ 1 := (hμA _).1 hinv
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (μ.pos hx0)).1 h1

theorem isUnit_of_abv_eq_one_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : μ x = 1) : IsUnit (⟨x, hx⟩ : ↥A) := by
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hinv : x⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem abv_lt_one_of_residue_eq_zero_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : IsLocalRing.residue ↥A ⟨x, hx⟩ = 0) : μ x < 1 :=
  abv_lt_one_of_mem_maximalIdeal_D μ hμA ((IsLocalRing.residue_eq_zero_iff _).1 h)

theorem evalAt_eq_zero_of_ord_ne_zero_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (h : v.ord f ≠ 0) : v.evalAt f = 0 := by
  by_contra hne
  exact h (ord_eq_zero_of_evalAt_ne_zero_D v hf hne)

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

theorem nodeTgt_isRational_D (Γ : ChartCtx p A) (ε : Fin (mAnnuli p)) : (nodeTgt Γ ε).IsRational := by
  apply isRational_of_deg_eq_one
  exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ ε)

theorem nodeSrc_isRational_D (Γ : ChartCtx p A) (ε : Fin (mAnnuli p)) : (nodeSrc Γ ε).IsRational := by
  apply isRational_of_deg_eq_one
  exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ ε ^ p)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem engine_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hβ : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) = 0)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ Q ∈ (Δ.annIn ε).dom,
      μ (Q.evalAt (Δ.annOut ε).param) = μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l ∧
      (∀ X ∈ (Δ.annIn ε).dom, X.ord (goodFamily Φ l) ≠ 0 → X = Q) ∧
      (∃ hq : Q.evalAt (Δ.annOut ε).param * ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l)⁻¹ ∈ A,
        IsUnit (⟨_, hq⟩ : ↥A) ∧
        IsLocalRing.residue ↥A ⟨_, hq⟩
          = -((nodeSrc Γ ε).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩))
              * ((nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
                  * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹))⁻¹) ∧
      ∀ X ∈ (Δ.annIn ε).dom,
        ∃ hu : X.evalAt (goodFamily Φ l * ((Δ.annOut ε).param
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹) ∈ A,
          IsUnit (⟨_, hu⟩ : ↥A) ∧
          IsLocalRing.residue ↥A ⟨_, hu⟩
            = (nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
                * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹) ∧
          X.evalAt (goodFamily Φ l)
            = X.evalAt (goodFamily Φ l * ((Δ.annOut ε).param
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹)
              * (X.evalAt (Δ.annOut ε).param - Q.evalAt (Δ.annOut ε).param) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set t := goodFamily Φ with ht
  set n := hasseExp Φ.toFamData l with hn
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ n with hc₁
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hc₁A : c₁ ∈ A := pow_mem hpA _
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
  set zo := (Δ.annOut ε).param with hzo
  have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
  have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
  have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
    intro h0
    have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
  have hscaled : goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
  have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
    rw [← hscaled]; exact hint0
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
  have e2 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hint0⟩ := Subtype.ext hscaled.symm
  have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
  have hord't : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨_, hC't⟩) = 0 := by rw [e2]; exact hβ
  have hrow : ∀ X ∈ (Δ.annIn ε).dom, t l ∈ X.toValuationSubring :=
    fun X hX => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε X hX l hl).1
  have hpole : ∀ X ∈ (Δ.annOut ε).dom, 0 ≤ X.ord (t l) := fun X hX => X.ord_nonneg_of_mem (hrow X (hdom ▸ hX))
  obtain ⟨Q, hQdom, hordQ, hordP, hμQ, ⟨hq, hqunit, hqres⟩, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one μ hμA
      (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
      (nodeTgt_isRational_D Γ ε) (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε) (nodeSrc_isRational_D Γ ε)
      hwide (t l) hint hrest hord c₁ hc₁0 hc₁A hC't hres't hord't hpole hz
  refine ⟨Q, hdom ▸ hQdom, by rw [hμQ, hc₁, map_pow], ?_, ⟨hq, hqunit, ?_⟩, ?_⟩
  · intro X hX hXord
    by_contra hXQ
    exact hXord (hordP X (hdom ▸ hX) hXQ)
  · rw [hqres, e2]
  · intro X hX
    have hXout : X ∈ (Δ.annOut ε).dom := hdom ▸ hX
    obtain ⟨hu, huunit, hures⟩ := hfac X hXout
    refine ⟨hu, huunit, hures, ?_⟩
    obtain ⟨hXrat, hzoX, -, hzoX0, -⟩ := (Δ.annOut ε).mem_dom X hXout
    have htX : t l ∈ X.toValuationSubring := hrow X hX
    by_cases hXQ : X = Q
    · subst hXQ
      have hev : X.evalAt (t l) = 0 := evalAt_eq_zero_of_ord_ne_zero_D X htX (by rw [hordQ]; exact one_ne_zero)
      rw [hev, sub_self, mul_zero]
    · have hwX : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param) ∈ X.toValuationSubring :=
        sub_mem hzoX (X.algebraMap_mem' _)
      have hwev : X.evalAt (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param)) = X.evalAt zo - Q.evalAt (Δ.annOut ε).param := by
        rw [evalAt_sub_D X hXrat hzoX (X.algebraMap_mem' _), evalAt_algebraMap_D]
      have hwne : X.evalAt zo - Q.evalAt (Δ.annOut ε).param ≠ 0 := by
        rw [sub_ne_zero]
        intro h1; apply hXQ
        obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := (Δ.annOut ε).mem_dom Q hQdom
        obtain ⟨P₀, -, huniq⟩ := (Δ.annOut ε).existsUnique_evalAt_eq ⟨Q.evalAt (Δ.annOut ε).param, haA⟩ ha𝔪 ha0 hm
        exact (huniq X ⟨hXout, h1⟩).trans (huniq Q ⟨hQdom, rfl⟩).symm
      have hev0 : X.evalAt (0 : modularFunctionFieldBar (1 * p)) = 0 := by
        rw [X.evalAt_of_mem (zero_mem _)]
        have : (⟨(0 : modularFunctionFieldBar (1 * p)), zero_mem _⟩ : X.toValuationSubring) = 0 := rfl
        rw [this, map_zero, ← map_zero (algebraMap (AlgebraicClosure ℚ) X.ResidueField), X.residueInv_algebraMap]
      have hw0 : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param) ≠ 0 := by
        intro h0; apply hwne; rw [← hwev, h0, hev0]
      have hordw : X.ord (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param)) = 0 :=
        ord_eq_zero_of_evalAt_ne_zero_D X hwX (by rw [hwev]; exact hwne)
      have hwinvX : (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹ ∈ X.toValuationSubring :=
        X.mem_of_ord_nonneg (inv_ne_zero hw0) (by rw [Place.ord_inv, hordw]; norm_num)
      rw [← hwev, ← evalAt_mul_D X hXrat (mul_mem htX hwinvX) hwX, inv_mul_cancel_right₀ hw0]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem outerUnit_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (X : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hX : X ∈ (Δ.annIn ε).dom)
    (hout : ∀ Y ∈ (Δ.annIn ε).dom, Y.ord (goodFamily Φ l) ≠ 0 →
      μ (Y.evalAt (Δ.annOut ε).param) < μ (X.evalAt (Δ.annOut ε).param)) :
    ∃ hmem : X.evalAt (goodFamily Φ l) * (X.evalAt (Δ.annOut ε).param)⁻¹ ∈ A,
      IsUnit (⟨_, hmem⟩ : ↥A) ∧
      IsLocalRing.residue ↥A ⟨_, hmem⟩
        = (nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
            * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set t := goodFamily Φ with ht
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc₁
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hc₁A : c₁ ∈ A := pow_mem hpA _
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
  set zo := (Δ.annOut ε).param with hzo
  have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
  have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
  have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
    intro h0
    have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
  have hscaled : goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
  have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
    rw [← hscaled]; exact hint0
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
  have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
  have hrow : ∀ Y ∈ (Δ.annIn ε).dom, t l ∈ Y.toValuationSubring :=
    fun Y hY => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε Y hY l hl).1
  have hpole : ∀ Y ∈ (Δ.annOut ε).dom, 0 ≤ Y.ord (t l) := fun Y hY => Y.ord_nonneg_of_mem (hrow Y (hdom ▸ hY))
  have hout' : ∀ Y ∈ (Δ.annOut ε).dom, Y.ord (t l) ≠ 0 → μ (Y.evalAt zo) < μ (X.evalAt zo) :=
    fun Y hY hYord => hout Y (hdom ▸ hY) hYord
  obtain ⟨hmem, hunit, hres⟩ :=
    AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt μ hμA
      (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
      (nodeTgt_isRational_D Γ ε) (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε)
      hwide (t l) hint hrest c₁ hc₁0 hc₁A hC't hres't hpole hz X (hdom ▸ hX) hout'
  have eA : X.evalAt (t l) * (X.evalAt zo) ^ (-((nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩)))
      = X.evalAt (t l) * (X.evalAt zo)⁻¹ := by rw [hord]; simp
  have eB : (infChart Γ).residue ⟨t l, hint⟩ * ((infChart Γ).residue ⟨zo, hz⟩) ^ (-((nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩)))
      = (infChart Γ).residue ⟨t l, hint⟩ * ((infChart Γ).residue ⟨zo, hz⟩)⁻¹ := by rw [hord]; simp
  have hmem' : X.evalAt (t l) * (X.evalAt zo)⁻¹ ∈ A := eA ▸ hmem
  have e3 : (⟨_, hmem'⟩ : ↥A) = ⟨_, hmem⟩ := Subtype.ext eA.symm
  refine ⟨hmem', by rw [e3]; exact hunit, ?_⟩
  rw [e3, hres, eB]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem zerosDepth_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hβle : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) ≤ 0)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    (∀ X ∈ (Δ.annIn ε).dom, X.ord (goodFamily Φ l) ≠ 0 →
        μ (X.evalAt (Δ.annOut ε).param) = μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l) ∧
    (∀ X ∈ (Δ.annIn ε).dom, μ (X.evalAt (goodFamily Φ l))
        ≤ max (μ (X.evalAt (Δ.annOut ε).param)) (μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  by_cases hβ0 : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) = 0
  · obtain ⟨Q, hQ, hμQ, hzeros, -, hfac⟩ := engine_D hA Γ Δ Φ ε l hl hint hint0 hz hord hβ0 μ hμA
    refine ⟨fun X hX hXord => by rw [hzeros X hX hXord]; exact hμQ, fun X hX => ?_⟩
    obtain ⟨hu, huunit, -, hmul⟩ := hfac X hX
    rw [hmul, map_mul, abv_eq_one_of_isUnit_D μ hμA hu huunit, one_mul (μ _), ← hμQ]
    exact abv_sub_le_max_D μ hμ _ _
  ·
    have hβneg : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) < 0 :=
      lt_of_le_of_ne hβle hβ0
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
      ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
    set t := goodFamily Φ with ht
    set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc₁
    have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
    have hc₁A : c₁ ∈ A := pow_mem hpA _
    obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
    set zo := (Δ.annOut ε).param with hzo
    have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
      rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
    have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
    have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
      intro h0
      have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
      rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
    have hscaled : goodFamilyZero Φ.toFamData l
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
    have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
      rw [← hscaled]; exact hint0
    obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
    have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
    have e2 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hint0⟩ := Subtype.ext hscaled.symm
    have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
    have hrow : ∀ Y ∈ (Δ.annIn ε).dom, t l ∈ Y.toValuationSubring :=
      fun Y hY => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε Y hY l hl).1
    have hpole : ∀ Y ∈ (Δ.annOut ε).dom, 0 ≤ Y.ord (t l) := fun Y hY => Y.ord_nonneg_of_mem (hrow Y (hdom ▸ hY))
    obtain ⟨D, hD0, hDsupp, hDord, hdeg, -⟩ :=
      AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
        (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
        (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε) hwide (t l) hint hrest c₁ hc₁0 hc₁A hC't hres't hpole
    have hordt : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [hordt, e2] at hdeg
    have hsum0 : (D.sum fun _ m => m) ≤ 0 := by rw [hdeg]; omega
    have hDzero : ∀ Y, D Y = 0 := by
      intro Y
      by_contra hne
      have hpos : 0 < D Y := lt_of_le_of_ne (hD0 Y) (Ne.symm hne)
      have hle : D Y ≤ D.sum fun _ m => m := by
        rw [Finsupp.sum]
        exact Finset.single_le_sum (fun Y' _ => hD0 Y') (Finsupp.mem_support_iff.2 hne)
      omega
    have hzf : ∀ Y ∈ (Δ.annIn ε).dom, Y.ord (t l) = 0 := fun Y hY => by rw [← hDord Y (hdom ▸ hY), hDzero]
    refine ⟨fun X hX hXord => absurd (hzf X hX) hXord, fun X hX => ?_⟩
    obtain ⟨hmem, hunit, -⟩ := outerUnit_D hA Γ Δ Φ ε l hl hint hint0 hz hord μ hμA X hX
      (fun Y hY hYord => absurd (hzf Y hY) hYord)
    obtain ⟨-, hzoX, -, hzoX0, -⟩ := (Δ.annOut ε).mem_dom X (hdom ▸ hX)
    have h1 : μ (X.evalAt (t l) * (X.evalAt zo)⁻¹) = 1 := abv_eq_one_of_isUnit_D μ hμA hmem hunit
    rw [map_mul, map_inv₀, mul_inv_eq_one₀ (μ.pos hzoX0).ne'] at h1
    rw [h1]; exact le_max_left _ _

end P2Helpers
end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar ssJSet deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue MultCovering.compConst_eq_compConst MultCovering.nonempty_chartCtx MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer_of_lt_hasseExp zero_mem_ssJSet_iff ofNat1728_mem_ssJSet_iff MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue exists_ssValue_eq nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_famCtx_orth_linearIndependent_zeroChart_residue compConst_eq_compConst nonempty_chartCtx exists_famCtx_toFamData_eq_of_bifiltered forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer_of_lt_hasseExp exists_unimodular_famData_wideCertificates_of_eq_eleven"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

theorem prox_symm_D {K : Type*} [Field K] {r : ℕ} (μ : AbsoluteValue K ℝ) (x y : Fin r → K) :
    prox μ x y = prox μ y x := by
  unfold prox
  have h : (fun q : Fin r × Fin r => μ (y q.1 * x q.2 - y q.2 * x q.1))
      = fun q : Fin r × Fin r => μ (x q.1 * y q.2 - x q.2 * y q.1) := by
    funext q
    rw [show y q.1 * x q.2 - y q.2 * x q.1 = -(x q.1 * y q.2 - x q.2 * y q.1) by ring, AbsoluteValue.map_neg]
  simp only [h]
  ring

end ModularCurve.MultCovering

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime] (hp11 : p = 11) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  intro μ hμ hμA R hR R' hR' hnonprop
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by omega
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  have h1728 : (1728 : IsLocalRing.ResidueField ↥A) ≠ 0 := by
    intro h
    have hdvd : p ∣ 1728 := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) p 1728).1 (by exact_mod_cast h)
    have h' : p ∣ 2 ^ 6 * 3 ^ 3 := by norm_num; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
  have hm2 : mAnnuli p = 2 := by rw [hp11]; decide
  have h0mem : (0 : IsLocalRing.ResidueField ↥A) ∈ ssJSet p (IsLocalRing.ResidueField ↥A) :=
    (ModularCurve.zero_mem_ssJSet_iff p hp5 (IsLocalRing.ResidueField ↥A)).2 (by omega)
  have h1728mem : (1728 : IsLocalRing.ResidueField ↥A) ∈ ssJSet p (IsLocalRing.ResidueField ↥A) :=
    (ModularCurve.ofNat1728_mem_ssJSet_iff p hp5 (IsLocalRing.ResidueField ↥A)).2 (by omega)
  obtain ⟨e₀, he₀⟩ := exists_ssValue_eq Γ 0 h0mem
  obtain ⟨e₁, he₁⟩ := exists_ssValue_eq Γ 1728 h1728mem
  have h01 : e₀ ≠ e₁ := by
    intro h; apply h1728; rw [← he₁, ← h, he₀]
  have hnodes : ∀ x : Fin (mAnnuli p), x = e₀ ∨ x = e₁ := by
    intro x
    have huniv : ({e₀, e₁} : Finset (Fin (mAnnuli p))) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_pair h01, Fintype.card_fin, hm2]
    have hx : x ∈ ({e₀, e₁} : Finset (Fin (mAnnuli p))) := by rw [huniv]; exact Finset.mem_univ x
    simpa using hx
  have hw₀ : jWidth (ssValue Γ e₀) = 3 := jWidth_of_eq_zero he₀
  have hw₁ : jWidth (ssValue Γ e₁) = 2 := jWidth_of_eq_1728 he₁ (by rw [he₁]; exact h1728)

  obtain ⟨Φγ, horthInf, horthZero, hAd⟩ :=
    ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue p hp5 s hs
  obtain ⟨hint, hLI⟩ := hAd A hA Γ
  obtain ⟨U, D', hint', hintI', hUunit, hU, hUinv, hU0, htRat, ht, hexp, hgfz, hLI', hatt0, hcont, ⟨l₂, l₃, h23, hl₂, hl₃, hn₂, hn₃⟩, hI2, hI3⟩ :=
    ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates_of_eq_eleven p hp11 A hA Γ Δ Φγ hint hLI
  obtain ⟨Φ', hΦ'⟩ := ModularCurve.MultCovering.exists_famCtx_toFamData_eq_of_bifiltered p Φγ horthInf horthZero
    U hUunit hU hUinv hU0 D' htRat ht hexp
  subst hΦ'
  rw [ModularCurve.MultCovering.compConst_eq_compConst p Φ Φ' s hs
    (fun A' hA' => by intro _ _; exact ModularCurve.MultCovering.nonempty_chartCtx p hp5 A' hA')]

  have hβle : ∀ (ε : Fin (mAnnuli p)) (l : Fin r),
      (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ'.toFamData l, hint' l⟩) ≤ 0 := by
    intro ε l; rw [hatt0]
    have : (0 : ℤ) ≤ ((hasseExp Φγ.toFamData l / jWidth (ssValue Γ ε) : ℕ) : ℤ) := Int.natCast_nonneg _
    omega
  have hzinf : ∀ ε : Fin (mAnnuli p), (Δ.annOut ε).param ∈ (infChart Γ).integers := by
    intro ε; obtain ⟨-, hzoC, -, -⟩ := Δ.attached_tgt ε; exact hzoC

  have hzfgen : ∀ (ε : Fin (mAnnuli p)) (l : Fin r), hasseExp Φγ.toFamData l = jWidth (ssValue Γ ε) →
      (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ' l, hintI' l⟩) = 1 →
      ∀ Q ∈ (Δ.annIn ε).dom, Q.ord (goodFamily Φ' l) = 0 := by
    intro ε l hn hord
    exact (ModularCurve.MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
      p A hA Γ Δ Φ' ε l ((hexp l).trans hn) (hintI' l) hord μ hμA).1

  have hα₂ : (nodeTgt Γ e₀).ord ((infChart Γ).residue ⟨goodFamily Φ' l₂, hintI' l₂⟩) = 1 := hI2 e₀ l₂ hl₂ hn₂
  have hα₂' : (nodeTgt Γ e₁).ord ((infChart Γ).residue ⟨goodFamily Φ' l₂, hintI' l₂⟩) = 1 := hI2 e₁ l₂ hl₂ hn₂
  have hα₃ : (nodeTgt Γ e₀).ord ((infChart Γ).residue ⟨goodFamily Φ' l₃, hintI' l₃⟩) = 1 := (hI3 e₀ l₃ hl₃ hn₃).1 he₀
  have hβ₂ : (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ'.toFamData l₂, hint' l₂⟩) = 0 := by
    rw [hatt0, hn₂, hw₀]; norm_num
  have hzf₂' : ∀ Q ∈ (Δ.annIn e₁).dom, Q.ord (goodFamily Φ' l₂) = 0 := hzfgen e₁ l₂ (by rw [hn₂, hw₁]) hα₂'
  have hzf₃ : ∀ Q ∈ (Δ.annIn e₀).dom, Q.ord (goodFamily Φ' l₃) = 0 := hzfgen e₀ l₃ (by rw [hn₃, hw₀]) hα₃
  have hn₂' : hasseExp Φ'.toFamData l₂ = 2 := (hexp l₂).trans hn₂
  have hn₃' : jWidth (ssValue Γ e₁) < hasseExp Φ'.toFamData l₃ := by rw [hw₁, hexp, hn₃]; norm_num

  have core : ∀ R₁ ∈ (Δ.annIn e₀).dom, ∀ R₂ ∈ (Δ.annIn e₁).dom,
      (∃ i' j', evalVec s R₁ i' * evalVec s R₂ j' ≠ evalVec s R₁ j' * evalVec s R₂ i') →
      |prox μ (evalVec s R₁) (evalVec s R₂)| ≤ compConst Φ' s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro R₁ hR₁ R₂ hR₂ hnp
    by_cases hdeep : ∃ m : AlgebraicClosure ℚ, m ∈ A ∧
        R₁.evalAt (Δ.annOut e₀).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₂ * m
    ·
      exact ModularCurve.MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree p A hA Γ Δ Φ' s hs e₀ e₁ h01 l₂ hl₂
        (hintI' l₂) hα₂ hα₂' (hint' l₂) hβ₂ hzf₂' μ hμ hμA R₁ hR₁ R₂ hR₂ hdeep hnp
    ·
      have hR₁up : μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₂ < μ (R₁.evalAt (Δ.annOut e₀).param) := by
        by_contra hle; push Not at hle
        apply hdeep
        have hpn0 : (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₂ ≠ 0 := pow_ne_zero _ hp0
        refine ⟨R₁.evalAt (Δ.annOut e₀).param * ((p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₂)⁻¹, (hμA _).2 ?_, ?_⟩
        · rw [map_mul, map_inv₀, map_pow]
          exact (mul_inv_le_iff₀ (pow_pos hμp0 _)).2 (hle.trans_eq (one_mul _).symm)
        · field_simp
      have hout₂ : ∀ Q ∈ (Δ.annIn e₀).dom, Q.ord (goodFamily Φ' l₂) ≠ 0 →
          μ (Q.evalAt (Δ.annOut e₀).param) < μ (R₁.evalAt (Δ.annOut e₀).param) := by
        intro Q hQ hQord
        obtain ⟨hzd, -⟩ := zerosDepth_D hA Γ Δ Φ' e₀ l₂ hl₂ (hintI' l₂) (hint' l₂) (hzinf e₀) hα₂ (hβle e₀ l₂) μ hμ hμA
        rw [hzd Q hQ hQord]; exact hR₁up
      have hout₃ : ∀ Q ∈ (Δ.annIn e₀).dom, Q.ord (goodFamily Φ' l₃) ≠ 0 →
          μ (Q.evalAt (Δ.annOut e₀).param) < μ (R₁.evalAt (Δ.annOut e₀).param) :=
        fun Q hQ h => absurd (hzf₃ Q hQ) h
      have hout₂' : ∀ Q ∈ (Δ.annIn e₁).dom, Q.ord (goodFamily Φ' l₂) ≠ 0 →
          μ (Q.evalAt (Δ.annOut e₁).param) < μ (R₂.evalAt (Δ.annOut e₁).param) :=
        fun Q hQ h => absurd (hzf₂' Q hQ) h
      exact ModularCurve.MultCovering.crossComparison_annIn_annIn_of_outer_of_lt_hasseExp p A hA Γ Δ Φ' s hs e₀ e₁ h01 l₂ l₃
        hl₂ hl₃ (hintI' l₂) (hintI' l₃) hα₂ hα₂' hα₃ hn₃' μ hμ hμA R₁ hR₁ R₂ hR₂ hout₂ hout₃ hout₂' hnp

  have hsymm : ∀ {R₁ R₂ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))},
      (∃ i' j', evalVec s R₁ i' * evalVec s R₂ j' ≠ evalVec s R₁ j' * evalVec s R₂ i') →
      (∃ i' j', evalVec s R₂ i' * evalVec s R₁ j' ≠ evalVec s R₂ j' * evalVec s R₁ i') := by
    intro R₁ R₂ ⟨i', j', hij⟩
    exact ⟨j', i', fun h => hij (by rw [mul_comm (evalVec s R₁ i'), mul_comm (evalVec s R₁ j')]; exact h)⟩
  rcases hnodes e with he | he <;> rcases hnodes e' with he' | he'
  · exact absurd (he.trans he'.symm) hne
  · rw [he] at hR; rw [he'] at hR'
    exact core R hR R' hR' hnonprop
  · rw [he] at hR; rw [he'] at hR'
    rw [prox_symm_D]
    exact core R' hR' R hR (hsymm hnonprop)
  · exact absurd (he.trans he'.symm) hne

end S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_eq_eleven
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_eq_eleven (solution)
