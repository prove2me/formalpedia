-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_of_sheetOne_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7895ea15-a789-5afe-b683-f07ebe646ca3

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.LevelOnePhi.instAddCommGroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne.ModularCurve ModularCurve.PlaceSpecialization~LevelOneProlongationPair P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne.ModularCurve.PlaceSpecialization"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ext ResidueField ord ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_t14 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem_t14"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_t14 {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg_t14"

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_t14 (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

p2m_export "AlgebraicCurve.Place" "ord_algebraMap_t14"

private theorem _root_.AlgebraicCurve.Place.ne_zero_of_ord_pos_t14 {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  simp at h

p2m_export "AlgebraicCurve.Place" "ne_zero_of_ord_pos_t14"

private theorem _root_.AlgebraicCurve.Place.isUnit_iff_ord_eq_zero_t14 {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  constructor
  · intro hu
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this
  · intro h0
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf0 h0
    exact hu

p2m_export "AlgebraicCurve.Place" "isUnit_iff_ord_eq_zero_t14"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_eq_or_ord_sub_pos_t14 {g : F} (hg : g ∈ v.toValuationSubring) (c : K) :
    v.HasValue g c ↔ g = algebraMap K F c ∨ 0 < v.ord (g - algebraMap K F c) := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg hcm

  have key : v.HasValue g c ↔
      IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hsub⟩ = 0 := by
    have hx : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
    rw [hx, map_sub, sub_eq_zero, v.residue_algebraMap c]
    constructor
    · intro h; exact h.residue_eq
    · intro h; exact ⟨hg, h⟩
  rw [key, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne (g - algebraMap K F c) 0 with h0 | h0
  · have hg' : g = algebraMap K F c := sub_eq_zero.mp h0
    have hz : (⟨g - algebraMap K F c, hsub⟩ : v.toValuationSubring) = 0 := Subtype.ext h0
    rw [hz]
    exact ⟨fun _ => Or.inl hg', fun _ => not_isUnit_zero⟩
  · rw [v.isUnit_iff_ord_eq_zero_t14 hsub h0]
    have hnn := v.ord_nonneg_of_mem_t14 hsub
    constructor
    · intro hne
      exact Or.inr (lt_of_le_of_ne hnn (Ne.symm hne))
    · rintro (hEq | hpos)
      · exact absurd (sub_eq_zero.mpr hEq) h0
      · exact ne_of_gt hpos

p2m_export "AlgebraicCurve.Place" "hasValue_iff_eq_or_ord_sub_pos_t14"
end Place
end AlgebraicCurve

namespace Subring p2m_export "Subring" "ext" end Subring
namespace Subring
p2m_open_scoped "Subring" in

private theorem _root_.Subring.inv_mem_of_isUnit_t14 {F : Type*} [Field F] {S : Subring F} {t : F} (h : t ∈ S)
    (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end Subring
p2m_export "" "Subring.inv_mem_of_isUnit_t14"
namespace ValuationSubring p2m_export "ValuationSubring" "algebraMap_apply ext zero_mem mem_nonunits_iff mul_mem one_mem mem_or_inv_mem add_mem valuation" end ValuationSubring
namespace ValuationSubring
p2m_open_scoped "ValuationSubring" in

private theorem _root_.ValuationSubring.inv_mem_of_isUnit_t14 {F : Type*} [Field F] {S : ValuationSubring F} {t : F}
    (h : t ∈ S) (hu : IsUnit (⟨t, h⟩ : S)) : t⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : Sˣ) : S).val * t = 1 := by
    have : ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := Units.inv_mul u
    rw [hu] at this
    exact congrArg Subtype.val this
  rw [← (eq_inv_of_mul_eq_one_left h1)]
  exact SetLike.coe_mem _

end ValuationSubring
p2m_export "" "ValuationSubring.inv_mem_of_isUnit_t14"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors IsCurveOver IsCurveOver.finiteResidue"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "residue_algebraMap HasValue hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ext ResidueField ord ord_coe_unit ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

private theorem _root_.AlgebraicCurve.Place.hasValue_iff_mem_and_eq_or_ord_sub_pos_t14
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) (g : L) (c : K) :
    v.HasValue g c ↔
      g ∈ v.toValuationSubring ∧ (g = algebraMap K L c ∨ 0 < v.ord (g - algebraMap K L c)) := by
  constructor
  · intro h
    exact ⟨h.mem, (v.hasValue_iff_eq_or_ord_sub_pos_t14 h.mem c).mp h⟩
  · rintro ⟨hg, h⟩
    exact (v.hasValue_iff_eq_or_ord_sub_pos_t14 hg c).mpr h
p2m_export "AlgebraicCurve.Place" "hasValue_iff_mem_and_eq_or_ord_sub_pos_t14"
end Place
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence ssPlaces IsAffineGeomPlace modularFunctionFieldFullC modularUnitSeries isCurveOver_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne"
p2m_open "ModularCurve.PlaceSpecialization~LevelOneProlongationPair"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "residue₁ residue₁_apply OrderLawFixed IsModel ι_coe R₁ redBar_residue mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem coe_algebraMap_intermediateField_laurent_t14 {L : Type*} [Field L]
    (E : IntermediateField L (LaurentSeries L)) (x : L) :
    ((algebraMap L ↥E x : ↥E) : LaurentSeries L) = HahnSeries.single 0 x := by
  rw [← algebraMap_laurentSeries_eq_single, IsScalarTower.algebraMap_apply L ↥E (LaurentSeries L) x]
  rfl

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.residue_algebraMap_eq_red_t14 (R : ProlongationTuple P) (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ = algebraMap k ↥(modularFunctionFieldC k 1) (red a) := by
  have h1 : R.R₁.residue ⟨_, h⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1)
        (IsLocalRing.residue A a) :=
    R.R₁.residue_algebraMap a
  apply Subtype.ext
  rw [residue₁_apply, h1, R.ι_coe, coe_algebraMap_intermediateField_laurent_t14,
    coe_algebraMap_intermediateField_laurent_t14, coeffMap_single, R.redBar_residue]

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "residue_algebraMap_eq_red_t14"

private def _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.FibreSumLawFstAt (R : ProlongationTuple P)
    (S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop) [DecidablePred S]
    (v : Place k ↥(modularFunctionFieldC k 1)) : Prop :=
  ∀ (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₁.integers), R.R₁.residue ⟨g, hg⟩ ≠ 0 →
    ∀ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), (∀ W, D W = W.ord g) →
      Finsupp.mapDomain P.reduceFst (D.filter S) v = v.ord (R.residue₁ ⟨g, hg⟩)

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "FibreSumLawFstAt"
set_option maxHeartbeats 6400000 in

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.one_le_ord_residue₁_of_fibreSumLaw_t14 (R : ProlongationTuple P)
    {S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop} [DecidablePred S]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hlaw : R.FibreSumLawFstAt S v)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : S W) (hWv : P.reduceFst W = v)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf1 : f ∈ R.R₁.integers) (hres : R.R₁.residue ⟨f, hf1⟩ ≠ 0)
    (hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), S W' → P.reduceFst W' = v → 0 ≤ W'.ord f)
    (hpos : 0 < W.ord f) : 1 ≤ v.ord (R.residue₁ ⟨f, hf1⟩) := by
  classical
  have hf0 : f ≠ 0 := W.ne_zero_of_ord_pos_t14 hpos
  obtain ⟨D, hD, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)).exists_divisor f hf0
  have hlaw' : Finsupp.mapDomain P.reduceFst (D.filter S) v = v.ord (R.residue₁ ⟨f, hf1⟩) :=
    hlaw f hf1 hres D hD
  set x : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := D.filter S with hx
  have hxapp : ∀ W', x W' = if S W' then D W' else 0 := fun W' => by
    rw [hx, Finsupp.filter_apply]
  let g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℤ := fun W' => if P.reduceFst W' = v then x W' else 0
  have hgnn : ∀ W', 0 ≤ g W' := by
    intro W'
    show 0 ≤ (if P.reduceFst W' = v then x W' else 0)
    split_ifs with h1
    · rw [hxapp]
      split_ifs with h2
      · rw [hD]; exact hnn W' h2 h1
      · exact le_refl _
    · exact le_refl _
  have hsum : ∑ W' ∈ x.support, g W' = v.ord (R.residue₁ ⟨f, hf1⟩) := by
    rw [← hlaw']
    unfold Finsupp.mapDomain
    rw [Finsupp.sum_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro W' _
    simp only [g, Finsupp.single_apply]
  have hxW : x W = W.ord f := by rw [hxapp, if_pos hW, hD]
  have hWmem : W ∈ x.support := by rw [Finsupp.mem_support_iff, hxW]; exact ne_of_gt hpos
  have hgW : g W = W.ord f := by
    show (if P.reduceFst W = v then x W else 0) = W.ord f
    rw [if_pos hWv, hxW]
  have h1 := Finset.single_le_sum (f := g) (s := x.support) (fun W' _ => hgnn W') hWmem
  rw [hsum, hgW] at h1
  omega

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "one_le_ord_residue₁_of_fibreSumLaw_t14"
set_option maxHeartbeats 6400000 in

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.value_mem_of_fibreSumLaw_t14 (R : ProlongationTuple P)
    {S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop} [DecidablePred S]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hlaw : R.FibreSumLawFstAt S v)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : S W) (hWv : P.reduceFst W = v)
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₁ : r ∈ R.R₁.integers)
    (hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), S W' → P.reduceFst W' = v → r ∈ W'.toValuationSubring)
    (c₀ : AlgebraicClosure ℚ) (hc₀ : W.HasValue r c₀) : c₀ ∈ A := by
  classical
  by_contra hnot
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl; exact hnot A.zero_mem
  have hεA : c₀⁻¹ ∈ A := (A.mem_or_inv_mem c₀).resolve_left hnot
  set ε : A := ⟨c₀⁻¹, hεA⟩ with hε
  have hεm : ε ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hnot
    have h := ValuationSubring.inv_mem_of_isUnit_t14 hεA hu
    rwa [inv_inv] at h
  have hredε : red ε = 0 := by
    rw [← R.redBar_residue ε, (IsLocalRing.residue_eq_zero_iff ε).mpr hεm, map_zero]
  have hcε : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr ε.2
  have hg1 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) * r - 1 ∈
      R.R₁.integers := sub_mem (mul_mem hcε h₁) (one_mem _)
  have hgsub : (⟨_, hg1⟩ : R.R₁.integers) = ⟨_, hcε⟩ * ⟨r, h₁⟩ - 1 := rfl
  have hresg : R.residue₁ ⟨_, hg1⟩ = -1 := by
    rw [hgsub, map_sub, map_mul, map_one, R.residue_algebraMap_eq_red_t14 ε hcε, hredε, map_zero, zero_mul,
      zero_sub]
  have hresg' : R.R₁.residue ⟨_, hg1⟩ ≠ 0 := by
    intro h0
    have : R.residue₁ ⟨_, hg1⟩ = 0 := by rw [residue₁_apply, h0, map_zero]
    rw [hresg] at this
    exact (neg_ne_zero.mpr one_ne_zero) this
  have hordg : v.ord (R.residue₁ ⟨_, hg1⟩) = 0 := by
    rw [hresg, show (-1 : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (-1) by
      rw [map_neg, map_one]]
    exact v.ord_algebraMap_t14 (-1)
  have hnng : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      S W' → P.reduceFst W' = v →
        0 ≤ W'.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) * r - 1) :=
    fun W' h1 h2 => W'.ord_nonneg_of_mem_t14
      (sub_mem (mul_mem (W'.algebraMap_mem' _) (hrW' W' h1 h2)) (one_mem _))
  have hval1 : W.HasValue (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (ε : AlgebraicClosure ℚ) * r) 1 := by
    have h := (W.hasValue_algebraMap (ε : AlgebraicClosure ℚ)).mul hc₀
    rwa [show (ε : AlgebraicClosure ℚ) * c₀ = 1 from inv_mul_cancel₀ hc₀0] at h
  have hposg : 0 < W.ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
      (ε : AlgebraicClosure ℚ) * r - 1) := by
    rcases (W.hasValue_iff_eq_or_ord_sub_pos_t14 hval1.mem 1).mp hval1 with hEq | hpos
    · exfalso
      apply hresg'
      have h0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (ε : AlgebraicClosure ℚ) * r - 1 = 0 := by
        rw [map_one] at hEq; rw [hEq, sub_self]
      have : (⟨_, hg1⟩ : R.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    · rwa [map_one] at hpos
  have h := R.one_le_ord_residue₁_of_fibreSumLaw_t14 hlaw hW hWv _ hg1 hresg' hnng hposg
  rw [hordg] at h
  omega

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "value_mem_of_fibreSumLaw_t14"
set_option maxHeartbeats 6400000 in

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_of_fibreSumLaw_t14 (R : ProlongationTuple P)
    {S : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop} [DecidablePred S]
    {v : Place k ↥(modularFunctionFieldC k 1)} (hlaw : R.FibreSumLawFstAt S v)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : S W) (hWv : P.reduceFst W = v)
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₁ : r ∈ R.R₁.integers)
    (hrW' : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), S W' → P.reduceFst W' = v → r ∈ W'.toValuationSubring) :
    ∃ c : A, W.HasValue r (c : AlgebraicClosure ℚ) ∧ v.HasValue (R.residue₁ ⟨r, h₁⟩) (red c) := by
  classical
  have hrW : r ∈ W.toValuationSubring := hrW' W hW hWv

  haveI := isCurveOver_modularFunctionFieldBar (1 * q)
  haveI : Module.Finite (AlgebraicClosure ℚ) W.ResidueField := IsCurveOver.finiteResidue W
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) W.ResidueField := Algebra.IsIntegral.of_finite _ _
  have hrat : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := W.ResidueField)).2
  obtain ⟨c₀, hc₀, -⟩ := W.exists_hasValue_of_surjective hrat hrW

  have hc₀A : c₀ ∈ A := R.value_mem_of_fibreSumLaw_t14 hlaw hW hWv r h₁ hrW' c₀ hc₀
  obtain ⟨c, hc⟩ : ∃ c : A, (c : AlgebraicClosure ℚ) = c₀ := ⟨⟨c₀, hc₀A⟩, rfl⟩
  subst hc
  refine ⟨c, hc₀, ?_⟩

  have hcR : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈
      R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr c.2
  have hs1 : r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈
      R.R₁.integers := sub_mem h₁ hcR
  have hssub : (⟨_, hs1⟩ : R.R₁.integers) = ⟨r, h₁⟩ - ⟨_, hcR⟩ := rfl
  have hress : R.residue₁ ⟨_, hs1⟩ = R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k 1) (red c) := by
    rw [hssub, map_sub, R.residue_algebraMap_eq_red_t14 c hcR]
  by_cases hz : R.residue₁ ⟨_, hs1⟩ = 0
  · have h : R.residue₁ ⟨r, h₁⟩ = algebraMap k ↥(modularFunctionFieldC k 1) (red c) := by
      rw [hress] at hz; exact sub_eq_zero.mp hz
    rw [h]
    exact v.hasValue_algebraMap (red c)
  · have hres' : R.R₁.residue ⟨_, hs1⟩ ≠ 0 := fun h0 => hz (by rw [residue₁_apply, h0, map_zero])
    have hnn : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        S W' → P.reduceFst W' = v →
          0 ≤ W'.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)) :=
      fun W' h1 h2 => W'.ord_nonneg_of_mem_t14 (sub_mem (hrW' W' h1 h2) (W'.algebraMap_mem' _))
    have hpos : 0 < W.ord (r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
        (c : AlgebraicClosure ℚ)) := by
      rcases (W.hasValue_iff_eq_or_ord_sub_pos_t14 hrW (c : AlgebraicClosure ℚ)).mp hc₀ with hEq | hpos
      · exfalso
        apply hz
        have h0 : r - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) = 0 := by
          rw [hEq, sub_self]
        have : (⟨_, hs1⟩ : R.R₁.integers) = 0 := Subtype.ext h0
        rw [this, map_zero]
      · exact hpos
    have h1 := R.one_le_ord_residue₁_of_fibreSumLaw_t14 hlaw hW hWv _ hs1 hres' hnn hpos
    rw [hress] at h1
    have hpos' : 0 < v.ord (R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k 1) (red c)) := by
      omega
    rw [v.hasValue_iff_mem_and_eq_or_ord_sub_pos_t14]
    refine ⟨?_, Or.inr hpos'⟩
    have hm : R.residue₁ ⟨r, h₁⟩ - algebraMap k ↥(modularFunctionFieldC k 1) (red c) ∈
        v.toValuationSubring :=
      v.mem_of_ord_nonneg_t14 (v.ne_zero_of_ord_pos_t14 hpos') hpos'.le
    have h := add_mem hm (v.algebraMap_mem' (red c))
    simpa using h

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "exists_hasValue_of_fibreSumLaw_t14"
end ProlongationTuple
end PlaceSpecialization
end ModularCurve

set_option maxHeartbeats 6400000 in
p2m_open "ModularCurve.PlaceSpecialization~LevelOneProlongationPair" in open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.ProlongationTuple _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne.ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k] [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace k 1 (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ))))
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers)
    (hfib : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W')) = P.reduceFst W' ∧
        IsAffineGeomPlace k 1 (P.reduceFst W') ∧ P.reduceFst W' ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W'.HasValue u (a : AlgebraicClosure ℚ))) →
      P.reduceFst W' = P.reduceFst W → f ∈ W'.toValuationSubring) :
    ∃ c : A, W.HasValue f (c : AlgebraicClosure ℚ) ∧ (P.reduceFst W).HasValue (R.residue₁ ⟨f, h₁⟩) (red c) := by
  classical
  obtain ⟨⟨hfix, haff, hss⟩, hsheet⟩ := hW

  have hlaw : R.FibreSumLawFstAt (fun W => ((frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W ∧
        IsAffineGeomPlace k 1 (P.reduceFst W) ∧ P.reduceFst W ∉ ssPlaces q 1 k) ∧
        (∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)))) (P.reduceFst W) :=
    fun g hg hres D hD =>
      ProlongationTuple.mapDomain_reduceFst_filter_sheetOne_eq_ord_residueFst_levelOne P R hR hO u hu
        g hg hres D hD (P.reduceFst W) hfix haff hss
  exact R.exists_hasValue_of_fibreSumLaw_t14 hlaw (W := W) ⟨⟨hfix, haff, hss⟩, hsheet⟩ rfl f h₁ hfib

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_of_sheetOne_levelOne (solution)
